use crate::Symbol;
use crate::{
    util::pretty_print, Analysis, EClass, EGraph, ENodeOrVar, FromOp, HashMap, HashSet, Id,
    Language, PatternAst, RecExpr, Rewrite, UnionFind, Var, Pattern, Subst
};
use instant::{Duration, Instant};
use std::cmp::Ordering;
use std::collections::{BinaryHeap, VecDeque};
use std::fmt::{self, Debug, Display, Formatter};
use std::rc::Rc;

use symbolic_expressions::Sexp;

const CONGRUENCE_LIMIT: usize = 10;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub(crate) enum Justification {
    Rule(Symbol),
    Congruence,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
struct Connection {
    next: Id,
    current: Id,
    justification: Justification,
    is_rewrite_forward: bool,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
struct ExplainNode<L: Language> {
    node: L,
    // neighbors includes parent connections
    neighbors: Vec<Connection>,
    parent_connection: Connection,
    // it was inserted because of:
    // 1) it's parent is inserted (points to parent enode)
    // 2) a rewrite instantiated it (points to adjacent enode)
    // 3) it was inserted directly (points to itself)
    // if 1 is true but it's also adjacent (2) then either works and it picks 2
    existance_node: Id,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct Explain<L: Language> {
    explainfind: Vec<ExplainNode<L>>,
    #[cfg_attr(feature = "serde-1", serde(with = "vectorize"))]
    pub uncanon_memo: HashMap<L, Id>,
    // For a given pair of enodes in the same eclass,
    // stores the length of the shortest found explanation
    // and the Id of the neighbor for retrieving
    // the explanation.
    // Invariant: The distance is always <= the unoptimized distance
    // That is, less than or equal to the result of `distance_between`
    shortest_explanation_memo: HashMap<(Id, Id), (usize, Id)>,
}

#[derive(Default)]
struct DistanceMemo {
    parent_distance: Vec<(Id, usize)>,
    common_ancestor: HashMap<(Id, Id), Id>,
    tree_depth: HashMap<Id, usize>,
}

/// Explanation trees are the compact representation showing
/// how one term can be rewritten to another.
///
/// Each [`TreeTerm`] has child [`TreeExplanation`]
/// justifying a transformation from the initial child to the final child term.
/// Children [`TreeTerm`] can be shared, thus re-using explanations.
/// This sharing can be checked via Rc pointer equality.
///
/// See [`TreeTerm`] for more details on how to
/// interpret each term.
pub type TreeExplanation<L> = Vec<Rc<TreeTerm<L>>>;

/// FlatExplanation are the simpler, expanded representation
/// showing one term being rewritten to another.
/// Each step contains a full `FlatTerm`. Each flat term
/// is connected to the previous by exactly one rewrite.
///
/// See [`FlatTerm`] for more details on how to find this rewrite.
pub type FlatExplanation<L> = Vec<FlatTerm<L>>;

/// A vector of grounded equalities. Each entry represents
/// two expressions that are equal and why.
pub type GroundedEqualities<L> = Vec<(RecExpr<L>, RecExpr<L>, Symbol)>;

/// A vector of equalities based on enode ids. Each entry represents
/// two enode ids that are equal and why.
pub type UnionEqualities = Vec<(Id, Id, Symbol)>;

// given two adjacent nodes and the direction of the proof
type ExplainCache<L> = HashMap<(Id, Id), Rc<TreeTerm<L>>>;
type NodeExplanationCache<L> = HashMap<Id, Rc<TreeTerm<L>>>;

/** A data structure representing an explanation that two terms are equivalent.

There are two representations of explanations, each of which can be
represented as s-expressions in strings.
See [`Explanation`] for more details.
**/
pub struct Explanation<L: Language> {
    /// The tree representation of the explanation.
    pub explanation_trees: TreeExplanation<L>,
    flat_explanation: Option<FlatExplanation<L>>,
}

impl<L: Language + Display + FromOp> Display for Explanation<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.get_sexp().to_string();
        f.write_str(&s)
    }
}

impl<L: Language + Display + FromOp> Explanation<L> {
    /// Get the flattened explanation as a string.
    pub fn get_flat_string(&mut self) -> String {
        self.get_flat_strings().join("\n")
    }

    /// Get the tree-style explanation as a string.
    pub fn get_string(&self) -> String {
        self.to_string()
    }

    /// Get the tree-style explanation with let binding as a string.
    /// See [`get_sexp_with_let`](Explanation::get_sexp_with_let) for the format of these strings.
    pub fn get_string_with_let(&self) -> String {
        let mut s = "".to_string();
        pretty_print(&mut s, &self.get_sexp_with_let(), 100, 0).unwrap();
        s
    }

    /// Get each term in the explanation as a string.
    pub fn get_flat_strings(&mut self) -> Vec<String> {
        self.make_flat_explanation()
            .iter()
            .map(|e| e.to_string())
            .collect()
    }

    /// Get each the tree-style explanation as an s-expression.
    ///
    /// The s-expression format mirrors the format of each [`TreeTerm`].
    /// When a child contains an explanation, the explanation is wrapped with
    /// "(Explanation ...)".
    /// When a term is being re-written it is wrapped with "(Rewrite=> rule-name expression)"
    /// or "(Rewrite<= rule-name expression)".
    /// "Rewrite=>" indicates that the previous term is rewritten to the current term
    /// and "Rewrite<=" indicates that the current term is rewritten to the previous term.
    /// The name of the rule or the reason provided to [`union_instantiations`](super::EGraph::union_instantiations).
    ///
    /// The following example shows that `(+ 1 (- a (* (- 2 1) a))) = 1`
    /// Example explanation:
    /// ```text
    /// (+ 1 (- a (* (- 2 1) a)))
    /// (+
    ///    1
    ///    (Explanation
    ///      (- a (* (- 2 1) a))
    ///      (-
    ///        a
    ///        (Explanation
    ///          (* (- 2 1) a)
    ///          (* (Explanation (- 2 1) (Rewrite=> constant_fold 1)) a)
    ///          (Rewrite=> comm-mul (* a 1))
    ///          (Rewrite<= mul-one a)))
    ///      (Rewrite=> cancel-sub 0)))
    /// (Rewrite=> constant_fold 1)
    /// ```
    pub fn get_sexp(&self) -> Sexp {
        let mut items = vec![Sexp::String("Explanation".to_string())];
        for e in self.explanation_trees.iter() {
            items.push(e.get_sexp());
        }

        Sexp::List(items)
    }

    /// Get the grounded equalities that make up this proof
    /// as pairs of RecExpr.
    pub fn get_grounded_equalities(&self) -> GroundedEqualities<L> {
        let mut seen: HashSet<*const TreeTerm<L>> = HashSet::default();
        let mut seen_adjacent = Default::default();
        let res = self.get_grounded_equalities_for(
            &self.explanation_trees,
            &mut seen,
            &mut seen_adjacent,
        );

        assert_eq!(res.len(), self.get_tree_size());
        res
    }

    fn get_grounded_equalities_for(
        &self,
        proof: &Vec<Rc<TreeTerm<L>>>,
        seen: &mut HashSet<*const TreeTerm<L>>,
        seen_adjacent: &mut HashSet<(Id, Id)>,
    ) -> GroundedEqualities<L> {
        let mut res = vec![];
        for i in 0..proof.len() {
            if !seen.insert(&*proof[i] as *const TreeTerm<L>) {
                continue;
            }
            let term = &proof[i];
            if term.backward_rule.is_some() || term.forward_rule.is_some() {
                let reason = term
                    .backward_rule
                    .unwrap_or_else(|| term.forward_rule.unwrap());
                let mut first = proof[i - 1].get_last_flat_term().get_recexpr();
                let mut second = proof[i].get_last_flat_term().get_recexpr();
                if term.backward_rule.is_some() {
                    std::mem::swap(&mut first, &mut second);
                }

                if seen_adjacent.insert((term.current, term.last)) {
                    seen_adjacent.insert((term.last, term.current));
                    res.push((first, second, reason));
                }
            }
            for child_proof in &term.child_proofs {
                let child_res = self.get_grounded_equalities_for(child_proof, seen, seen_adjacent);
                res.extend(child_res);
            }
        }
        res
    }

    /// Get the size of this explanation tree in terms of the number of rewrites
    /// in the let-bound version of the tree.
    pub fn get_tree_size(&self) -> usize {
        let mut seen = Default::default();
        let mut seen_adjacent = Default::default();
        let mut sum = 0;
        for e in self.explanation_trees.iter() {
            sum += self.tree_size(&mut seen, &mut seen_adjacent, e);
        }
        sum
    }

    fn tree_size(
        &self,
        seen: &mut HashSet<*const TreeTerm<L>>,
        seen_adjacent: &mut HashSet<(Id, Id)>,
        current: &Rc<TreeTerm<L>>,
    ) -> usize {
        if !seen.insert(&**current as *const TreeTerm<L>) {
            return 0;
        }
        let mut my_size = 0;
        if let Some(_) = current.forward_rule {
            my_size += 1;
        }
        if let Some(_) = current.backward_rule {
            my_size += 1;
        }
        assert!(my_size <= 1);
        if my_size == 1 {
            if !seen_adjacent.insert((current.current, current.last)) {
                return 0;
            } else {
                seen_adjacent.insert((current.last, current.current));
            }
        }

        for child_proof in &current.child_proofs {
            for child in child_proof {
                my_size += self.tree_size(seen, seen_adjacent, child);
            }
        }
        my_size
    }

    /// Get the tree-style explanation as an s-expression with let binding
    /// to enable sharing of subproofs.
    ///
    /// The following explanation shows that `(+ x (+ x (+ x x))) = (* 4 x)`.
    /// Steps such as factoring are shared via the let bindings.
    /// Example explanation:
    ///
    /// ```text
    /// (let
    ///     (v_0 (Rewrite=> mul-one (* x 1)))
    ///     (let
    ///       (v_1 (+ (Explanation x v_0) (Explanation x v_0)))
    ///       (let
    ///         (v_2 (+ 1 1))
    ///         (let
    ///           (v_3 (Rewrite=> factor (* x v_2)))
    ///           (Explanation
    ///             (+ x (+ x (+ x x)))
    ///             (Rewrite=> assoc-add (+ (+ x x) (+ x x)))
    ///             (+ (Explanation (+ x x) v_1 v_3) (Explanation (+ x x) v_1 v_3))
    ///             (Rewrite=> factor (* x (+ (+ 1 1) (+ 1 1))))
    ///             (Rewrite=> comm-mul (* (+ (+ 1 1) (+ 1 1)) x))
    ///             (*
    ///               (Explanation
    ///                 (+ (+ 1 1) (+ 1 1))
    ///                 (+
    ///                   (Explanation (+ 1 1) (Rewrite=> constant_fold 2))
    ///                   (Explanation (+ 1 1) (Rewrite=> constant_fold 2)))
    ///                 (Rewrite=> constant_fold 4))
    ///               x))))))
    /// ```
    pub fn get_sexp_with_let(&self) -> Sexp {
        let mut shared: HashSet<*const TreeTerm<L>> = Default::default();
        let mut to_let_bind = vec![];
        for term in &self.explanation_trees {
            self.find_to_let_bind(term.clone(), &mut shared, &mut to_let_bind);
        }

        let mut bindings: HashMap<*const TreeTerm<L>, Sexp> = Default::default();
        let mut generated_bindings: Vec<(Sexp, Sexp)> = Default::default();
        for to_bind in to_let_bind {
            if bindings.get(&(&*to_bind as *const TreeTerm<L>)).is_none() {
                let name = Sexp::String("v_".to_string() + &generated_bindings.len().to_string());
                let ast = to_bind.get_sexp_with_bindings(&bindings);
                generated_bindings.push((name.clone(), ast));
                bindings.insert(&*to_bind as *const TreeTerm<L>, name);
            }
        }

        let mut items = vec![Sexp::String("Explanation".to_string())];
        for e in self.explanation_trees.iter() {
            if let Some(existing) = bindings.get(&(&**e as *const TreeTerm<L>)) {
                items.push(existing.clone());
            } else {
                items.push(e.get_sexp_with_bindings(&bindings));
            }
        }

        let mut result = Sexp::List(items);

        for (name, expr) in generated_bindings.into_iter().rev() {
            let let_expr = Sexp::List(vec![name, expr]);
            result = Sexp::List(vec![Sexp::String("let".to_string()), let_expr, result]);
        }

        result
    }

    fn find_to_let_bind(
        &self,
        term: Rc<TreeTerm<L>>,
        shared: &mut HashSet<*const TreeTerm<L>>,
        to_let_bind: &mut Vec<Rc<TreeTerm<L>>>,
    ) {
        for proof in &term.child_proofs {
            for child in proof {
                self.find_to_let_bind(child.clone(), shared, to_let_bind);
            }
        }

        if !term.child_proofs.is_empty() && !shared.insert(&*term as *const TreeTerm<L>) {
            to_let_bind.push(term);
        }
    }

    /// Get each flattened term in the explanation as an s-expression.
    ///
    /// The s-expression format mirrors the format of each [`FlatTerm`].
    /// Each expression after the first will be annotated in one location with a rewrite.
    /// When a term is being re-written it is wrapped with "(Rewrite=> rule-name expression)"
    /// or "(Rewrite<= rule-name expression)".
    /// "Rewrite=>" indicates that the previous term is rewritten to the current term
    /// and "Rewrite<=" indicates that the current term is rewritten to the previous term.
    /// The name of the rule or the reason provided to [`union_instantiations`](super::EGraph::union_instantiations).
    ///
    /// Example explanation:
    /// ```text
    /// (+ 1 (- a (* (- 2 1) a)))
    /// (+ 1 (- a (* (Rewrite=> constant_fold 1) a)))
    /// (+ 1 (- a (Rewrite=> comm-mul (* a 1))))
    /// (+ 1 (- a (Rewrite<= mul-one a)))
    /// (+ 1 (Rewrite=> cancel-sub 0))
    /// (Rewrite=> constant_fold 1)
    /// ```
    pub fn get_flat_sexps(&mut self) -> Vec<Sexp> {
        self.make_flat_explanation()
            .iter()
            .map(|e| e.get_sexp())
            .collect()
    }
}

impl<L: Language> Explanation<L> {
    /// Construct a new explanation given its tree representation.
    pub fn new(explanation_trees: TreeExplanation<L>) -> Explanation<L> {
        Explanation {
            explanation_trees,
            flat_explanation: None,
        }
    }

    /// Using a set of grounded equalities, find an irriducible set of equalities
    /// which can still prove the start and end terms are equal.
    pub fn reduce_grounded_equalities(
        proof: &GroundedEqualities<L>,
        start: &RecExpr<L>,
        end: &RecExpr<L>,
    ) -> GroundedEqualities<L> {
        let mut res = vec![];

        let mut test_egraph = EGraph::<L, ()>::new(());
        for pair in proof {
            let (lhs, rhs, _) = pair;
            let l_id = test_egraph.add_expr(&lhs);
            let r_id = test_egraph.add_expr(&rhs);
            test_egraph.union(l_id, r_id);
        }
        test_egraph.rebuild();
        assert_eq!(test_egraph.add_expr(start), test_egraph.add_expr(end));

        for i in 0..proof.len() {
            let mut test_egraph = EGraph::<L, ()>::new(());
            for pair in &res {
                let (lhs, rhs, _) = pair;
                let l_id = test_egraph.add_expr(&lhs);
                let r_id = test_egraph.add_expr(&rhs);
                test_egraph.union(l_id, r_id);
            }

            for j in i + 1..proof.len() {
                let (lhs, rhs, _) = &proof[j];
                let l_id = test_egraph.add_expr(&lhs);
                let r_id = test_egraph.add_expr(&rhs);
                test_egraph.union(l_id, r_id);
            }

            test_egraph.rebuild();
            if test_egraph.add_expr(start) != test_egraph.add_expr(end) {
                res.push(proof[i].clone());
            }
        }

        res
    }

    /// Construct the flat representation of the explanation and return it.
    pub fn make_flat_explanation(&mut self) -> &FlatExplanation<L> {
        if self.flat_explanation.is_some() {
            return self.flat_explanation.as_ref().unwrap();
        } else {
            self.flat_explanation = Some(TreeTerm::flatten_proof(&self.explanation_trees));
            self.flat_explanation.as_ref().unwrap()
        }
    }

    /// Check the validity of the explanation with respect to the given rules.
    /// This only is able to check rule applications when the rules are implement `get_pattern_ast`.
    pub fn check_proof<'a, R, N: Analysis<L>>(&mut self, rules: R)
    where
        R: IntoIterator<Item = &'a Rewrite<L, N>>,
        L: 'a,
        N: 'a,
    {
        let rules: Vec<&Rewrite<L, N>> = rules.into_iter().collect();
        let rule_table = Explain::make_rule_table(rules.as_slice());
        self.make_flat_explanation();
        let flat_explanation = self.flat_explanation.as_ref().unwrap();
        assert!(!flat_explanation[0].has_rewrite_forward());
        assert!(!flat_explanation[0].has_rewrite_backward());
        for i in 0..flat_explanation.len() - 1 {
            let current = &flat_explanation[i];
            let next = &flat_explanation[i + 1];

            let has_forward = next.has_rewrite_forward();
            let has_backward = next.has_rewrite_backward();
            assert!(has_forward ^ has_backward);

            if has_forward {
                assert!(self.check_rewrite_at(current, next, &rule_table, true));
            } else {
                assert!(self.check_rewrite_at(current, next, &rule_table, false));
            }
        }
    }

    fn check_rewrite_at<N: Analysis<L>>(
        &self,
        current: &FlatTerm<L>,
        next: &FlatTerm<L>,
        table: &HashMap<Symbol, &Rewrite<L, N>>,
        is_forward: bool,
    ) -> bool {
        if is_forward && next.forward_rule.is_some() {
            let rule_name = next.forward_rule.as_ref().unwrap();
            if let Some(rule) = table.get(rule_name) {
                Explanation::check_rewrite(current, next, rule)
            } else {
                // give up when the rule is not provided
                true
            }
        } else if !is_forward && next.backward_rule.is_some() {
            let rule_name = next.backward_rule.as_ref().unwrap();
            if let Some(rule) = table.get(rule_name) {
                Explanation::check_rewrite(next, current, rule)
            } else {
                true
            }
        } else {
            for (left, right) in current.children.iter().zip(next.children.iter()) {
                if !self.check_rewrite_at(left, right, table, is_forward) {
                    return false;
                }
            }
            true
        }
    }

    // if the rewrite is just patterns, then it can check it
    fn check_rewrite<'a, N: Analysis<L>>(
        current: &'a FlatTerm<L>,
        next: &'a FlatTerm<L>,
        rewrite: &Rewrite<L, N>,
    ) -> bool {
        if let Some(lhs) = rewrite.searcher.get_pattern_ast() {
            if let Some(rhs) = rewrite.applier.get_pattern_ast() {
                let rewritten = current.rewrite(lhs, rhs);
                if &rewritten != next {
                    return false;
                }
            }
        }
        true
    }
}

/// An explanation for a term and its equivalent children.
/// Each child is a proof transforming the initial child into the final child term.
/// The initial term is given by taking each first sub-term
/// in each [`child_proofs`](TreeTerm::child_proofs) recursively.
/// The final term is given by all of the final terms in each [`child_proofs`](TreeTerm::child_proofs).
///
/// If [`forward_rule`](TreeTerm::forward_rule) is provided, then this TreeTerm's initial term
/// can be derived from the previous
/// TreeTerm by applying the rule.
/// Similarly, if [`backward_rule`](TreeTerm::backward_rule) is provided,
/// then the previous TreeTerm's final term is given by applying the rule to this TreeTerm's initial term.
///
/// TreeTerms are flattened by first flattening [`child_proofs`](TreeTerm::child_proofs), then wrapping
/// the flattened proof with this TreeTerm's node.
#[derive(Debug, Clone)]
pub struct TreeTerm<L: Language> {
    /// A node representing this TreeTerm's operator. The children of the node should be ignored.
    pub node: L,
    /// A rule rewriting this TreeTerm's initial term back to the last TreeTerm's final term.
    pub backward_rule: Option<Symbol>,
    /// A rule rewriting the last TreeTerm's final term to this TreeTerm's initial term.
    pub forward_rule: Option<Symbol>,
    /// A list of child proofs, each transforming the initial term to the final term for that child.
    pub child_proofs: Vec<TreeExplanation<L>>,

    last: Id,
    current: Id,
}

impl<L: Language> TreeTerm<L> {
    /// Construct a new TreeTerm given its node and child_proofs.
    pub fn new(node: L, child_proofs: Vec<TreeExplanation<L>>) -> TreeTerm<L> {
        TreeTerm {
            node,
            backward_rule: None,
            forward_rule: None,
            child_proofs,
            current: Id::from(0),
            last: Id::from(0),
        }
    }

    fn flatten_proof(proof: &[Rc<TreeTerm<L>>]) -> FlatExplanation<L> {
        let mut flat_proof: FlatExplanation<L> = vec![];
        for tree in proof {
            let mut explanation = tree.flatten_explanation();

            if !flat_proof.is_empty()
                && !explanation[0].has_rewrite_forward()
                && !explanation[0].has_rewrite_backward()
            {
                let last = flat_proof.pop().unwrap();
                explanation[0].combine_rewrites(&last);
            }

            flat_proof.extend(explanation);
        }

        flat_proof
    }

    /// Get a FlatTerm representing the first term in this proof.
    pub fn get_initial_flat_term(&self) -> FlatTerm<L> {
        FlatTerm {
            node: self.node.clone(),
            backward_rule: self.backward_rule.clone(),
            forward_rule: self.forward_rule.clone(),
            children: self
                .child_proofs
                .iter()
                .map(|child_proof| child_proof[0].get_initial_flat_term())
                .collect(),
        }
    }

    /// Get a FlatTerm representing the final term in this proof.
    pub fn get_last_flat_term(&self) -> FlatTerm<L> {
        FlatTerm {
            node: self.node.clone(),
            backward_rule: self.backward_rule.clone(),
            forward_rule: self.forward_rule.clone(),
            children: self
                .child_proofs
                .iter()
                .map(|child_proof| child_proof[child_proof.len() - 1].get_last_flat_term())
                .collect(),
        }
    }

    /// Construct the [`FlatExplanation`] for this TreeTerm.
    pub fn flatten_explanation(&self) -> FlatExplanation<L> {
        let mut proof = vec![];
        let mut child_proofs = vec![];
        let mut representative_terms = vec![];
        for child_explanation in &self.child_proofs {
            let flat_proof = TreeTerm::flatten_proof(child_explanation);
            representative_terms.push(flat_proof[0].remove_rewrites());
            child_proofs.push(flat_proof);
        }

        proof.push(FlatTerm::new(
            self.node.clone(),
            representative_terms.clone(),
        ));

        for (i, child_proof) in child_proofs.iter().enumerate() {
            // replace first one to preserve the rule annotation
            proof.last_mut().unwrap().children[i] = child_proof[0].clone();

            for child in child_proof.iter().skip(1) {
                let mut children = vec![];
                for (j, rep_term) in representative_terms.iter().enumerate() {
                    if j == i {
                        children.push(child.clone());
                    } else {
                        children.push(rep_term.clone());
                    }
                }

                proof.push(FlatTerm::new(self.node.clone(), children));
            }
            representative_terms[i] = child_proof.last().unwrap().remove_rewrites();
        }

        proof[0].backward_rule = self.backward_rule;
        proof[0].forward_rule = self.forward_rule;

        proof
    }
}

/// A single term in an flattened explanation.
/// After the first term in a [`FlatExplanation`], each term
/// will be annotated with exactly one [`backward_rule`](FlatTerm::backward_rule) or one
/// [`forward_rule`](FlatTerm::forward_rule). This can appear in children [`FlatTerm`]s,
/// indicating that the child is being rewritten.
///
/// When [`forward_rule`](FlatTerm::forward_rule) is provided, the previous FlatTerm can be rewritten
/// to this FlatTerm by applying the rule.
/// When [`backward_rule`](FlatTerm::backward_rule) is provided, the previous FlatTerm is given by applying
/// the rule to this FlatTerm.
/// Rules are either the string of the name of the rule or the reason provided to
/// [`union_instantiations`](super::EGraph::union_instantiations).
///
#[derive(Debug, Clone, Eq)]
pub struct FlatTerm<L: Language> {
    /// The node representing this FlatTerm's operator.
    /// The children of the node should be ignored.
    pub node: L,
    /// A rule rewriting this FlatTerm back to the last FlatTerm.
    pub backward_rule: Option<Symbol>,
    /// A rule rewriting the last FlatTerm to this FlatTerm.
    pub forward_rule: Option<Symbol>,
    /// The children of this FlatTerm.
    pub children: FlatExplanation<L>,
}

impl<L: Language + Display + FromOp> Display for FlatTerm<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.get_sexp().to_string();
        write!(f, "{}", s)
    }
}

impl<L: Language> PartialEq for FlatTerm<L> {
    fn eq(&self, other: &FlatTerm<L>) -> bool {
        if !self.node.matches(&other.node) {
            return false;
        }

        for (child1, child2) in self.children.iter().zip(other.children.iter()) {
            if !child1.eq(child2) {
                return false;
            }
        }
        true
    }
}

impl<L: Language> FlatTerm<L> {
    /// Remove the rewrite annotation from this flatterm, if any.
    pub fn remove_rewrites(&self) -> FlatTerm<L> {
        FlatTerm::new(
            self.node.clone(),
            self.children
                .iter()
                .map(|child| child.remove_rewrites())
                .collect(),
        )
    }

    fn combine_rewrites(&mut self, other: &FlatTerm<L>) {
        if other.forward_rule.is_some() {
            assert!(self.forward_rule.is_none());
            self.forward_rule = other.forward_rule;
        }

        if other.backward_rule.is_some() {
            assert!(self.backward_rule.is_none());
            self.backward_rule = other.backward_rule;
        }

        for (left, right) in self.children.iter_mut().zip(other.children.iter()) {
            left.combine_rewrites(right);
        }
    }
}

impl<L: Language> Default for Explain<L> {
    fn default() -> Self {
        Self::new()
    }
}

impl<L: Language + Display + FromOp> FlatTerm<L> {
    /// Convert this FlatTerm to an S-expression.
    /// See [`get_flat_sexps`](Explanation::get_flat_sexps) for the format of these expressions.
    pub fn get_sexp(&self) -> Sexp {
        let op = Sexp::String(self.node.to_string());
        let mut expr = if self.node.is_leaf() {
            op
        } else {
            let mut vec = vec![op];
            for child in &self.children {
                vec.push(child.get_sexp());
            }
            Sexp::List(vec)
        };

        if let Some(rule_name) = &self.backward_rule {
            expr = Sexp::List(vec![
                Sexp::String("Rewrite<=".to_string()),
                Sexp::String((*rule_name).to_string()),
                expr,
            ]);
        }

        if let Some(rule_name) = &self.forward_rule {
            expr = Sexp::List(vec![
                Sexp::String("Rewrite=>".to_string()),
                Sexp::String((*rule_name).to_string()),
                expr,
            ]);
        }

        expr
    }

    /// Convert this FlatTerm to a RecExpr.
    pub fn get_recexpr(&self) -> RecExpr<L> {
        let without_rewrites = self.remove_rewrites();
        return without_rewrites.to_string().parse().unwrap();
    }
}

impl<L: Language + Display + FromOp> Display for TreeTerm<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut buf = String::new();
        let width = 80;
        pretty_print(&mut buf, &self.get_sexp(), width, 1).unwrap();
        write!(f, "{}", buf)
    }
}

impl<L: Language + Display + FromOp> TreeTerm<L> {
    /// Convert this TreeTerm to an S-expression.
    /// See [`get_sexp`](Explanation::get_sexp) for the format of these expressions.
    pub fn get_sexp(&self) -> Sexp {
        self.get_sexp_with_bindings(&Default::default())
    }

    pub(crate) fn get_sexp_with_bindings(
        &self,
        bindings: &HashMap<*const TreeTerm<L>, Sexp>,
    ) -> Sexp {
        let op = Sexp::String(self.node.to_string());
        let mut expr = if self.node.is_leaf() {
            op
        } else {
            let mut vec = vec![op];
            for child in &self.child_proofs {
                assert!(!child.is_empty());
                if child.len() == 1 {
                    if let Some(existing) = bindings.get(&(&*child[0] as *const TreeTerm<L>)) {
                        vec.push(existing.clone());
                    } else {
                        vec.push(child[0].get_sexp_with_bindings(bindings));
                    }
                } else {
                    let mut child_expressions = vec![Sexp::String("Explanation".to_string())];
                    for child_explanation in child.iter() {
                        if let Some(existing) =
                            bindings.get(&(&**child_explanation as *const TreeTerm<L>))
                        {
                            child_expressions.push(existing.clone());
                        } else {
                            child_expressions
                                .push(child_explanation.get_sexp_with_bindings(bindings));
                        }
                    }
                    vec.push(Sexp::List(child_expressions));
                }
            }
            Sexp::List(vec)
        };

        if let Some(rule_name) = &self.backward_rule {
            expr = Sexp::List(vec![
                Sexp::String("Rewrite<=".to_string()),
                Sexp::String((*rule_name).to_string()),
                expr,
            ]);
        }

        if let Some(rule_name) = &self.forward_rule {
            expr = Sexp::List(vec![
                Sexp::String("Rewrite=>".to_string()),
                Sexp::String((*rule_name).to_string()),
                expr,
            ]);
        }

        expr
    }
}

impl<L: Language> FlatTerm<L> {
    /// Construct a new FlatTerm given a node and its children.
    pub fn new(node: L, children: FlatExplanation<L>) -> FlatTerm<L> {
        FlatTerm {
            node,
            backward_rule: None,
            forward_rule: None,
            children,
        }
    }

    /// Rewrite the FlatTerm by matching the lhs and substituting the rhs.
    /// The lhs must be guaranteed to match.
    pub fn rewrite(&self, lhs: &PatternAst<L>, rhs: &PatternAst<L>) -> FlatTerm<L> {
        let lhs_nodes = lhs.as_ref();
        let rhs_nodes = rhs.as_ref();
        let mut bindings = Default::default();
        self.make_bindings(lhs_nodes, lhs_nodes.len() - 1, &mut bindings);
        FlatTerm::from_pattern(rhs_nodes, rhs_nodes.len() - 1, &bindings)
    }

    /// Checks if this term or any child has a [`forward_rule`](FlatTerm::forward_rule).
    pub fn has_rewrite_forward(&self) -> bool {
        self.forward_rule.is_some()
            || self
                .children
                .iter()
                .any(|child| child.has_rewrite_forward())
    }

    /// Checks if this term or any child has a [`backward_rule`](FlatTerm::backward_rule).
    pub fn has_rewrite_backward(&self) -> bool {
        self.backward_rule.is_some()
            || self
                .children
                .iter()
                .any(|child| child.has_rewrite_backward())
    }

    fn from_pattern(
        pattern: &[ENodeOrVar<L>],
        location: usize,
        bindings: &HashMap<Var, &FlatTerm<L>>,
    ) -> FlatTerm<L> {
        match &pattern[location] {
            ENodeOrVar::Var(var) => (*bindings.get(var).unwrap()).clone(),
            ENodeOrVar::ENode(node) => {
                let children = node.fold(vec![], |mut acc, child| {
                    acc.push(FlatTerm::from_pattern(
                        pattern,
                        usize::from(child),
                        bindings,
                    ));
                    acc
                });
                FlatTerm::new(node.clone(), children)
            }
        }
    }

    fn make_bindings<'a>(
        &'a self,
        pattern: &[ENodeOrVar<L>],
        location: usize,
        bindings: &mut HashMap<Var, &'a FlatTerm<L>>,
    ) {
        match &pattern[location] {
            ENodeOrVar::Var(var) => {
                if let Some(existing) = bindings.get(var) {
                    if existing != &self {
                        panic!(
                            "Invalid proof: binding for variable {:?} does not match between {:?} \n and \n {:?}",
                            var, existing, self);
                    }
                } else {
                    bindings.insert(*var, self);
                }
            }
            ENodeOrVar::ENode(node) => {
                // The node must match the rewrite or the proof is invalid.
                assert!(node.matches(&self.node));
                let mut counter = 0;
                node.for_each(|child| {
                    self.children[counter].make_bindings(pattern, usize::from(child), bindings);
                    counter += 1;
                });
            }
        }
    }
}

// Make sure to use push_increase instead of push when using priority queue
#[derive(Copy, Clone, Eq, PartialEq)]
struct HeapState<I> {
    cost: usize,
    item: I,
}
// The priority queue depends on `Ord`.
// Explicitly implement the trait so the queue becomes a min-heap
// instead of a max-heap.
impl<I: Eq + PartialEq> Ord for HeapState<I> {
    fn cmp(&self, other: &Self) -> Ordering {
        // Notice that the we flip the ordering on costs.
        // In case of a tie we compare positions - this step is necessary
        // to make implementations of `PartialEq` and `Ord` consistent.
        other
            .cost
            .cmp(&self.cost)
            .then_with(|| self.cost.cmp(&other.cost))
    }
}

// `PartialOrd` needs to be implemented as well.
impl<I: Eq + PartialEq> PartialOrd for HeapState<I> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<L: Language> Explain<L> {
    fn node_to_explanation(
        &self,
        node_id: Id,
        cache: &mut NodeExplanationCache<L>,
    ) -> Rc<TreeTerm<L>> {
        if let Some(existing) = cache.get(&node_id) {
            existing.clone()
        } else {
            let node = self.explainfind[usize::from(node_id)].node.clone();
            let children = node.fold(vec![], |mut sofar, child| {
                sofar.push(vec![self.node_to_explanation(child, cache)]);
                sofar
            });
            let res = Rc::new(TreeTerm::new(node, children));
            cache.insert(node_id, res.clone());
            res
        }
    }

    pub(crate) fn node_to_recexpr(&self, node_id: Id) -> RecExpr<L> {
        let mut res = Default::default();
        let mut cache = Default::default();
        self.node_to_recexpr_internal(&mut res, node_id, &mut cache);
        res
    }

    fn node_to_recexpr_internal(&self, res: &mut RecExpr<L>, node_id: Id, cache: &mut HashMap<Id, Id>) {
        let new_node = self.explainfind[usize::from(node_id)].node.clone().map_children(|child| {
            if let Some(existing) = cache.get(&child) {
                *existing
            } else {
                self.node_to_recexpr_internal(res, child, cache);
                Id::from(res.as_ref().len() - 1)
            }
        });
        res.add(new_node);
    }

    pub(crate) fn node_to_pattern(&self, node_id: Id, substitutions: &HashMap<Id, Id>) -> (Pattern<L>, Subst) {
        let mut res = Default::default();
        let mut subst = Default::default();
        let mut cache = Default::default();
        self.node_to_pattern_internal(&mut res, node_id, substitutions, &mut subst, &mut cache);
        (Pattern::new(res), subst)
    }

    fn node_to_pattern_internal(&self, res: &mut PatternAst<L>, node_id: Id, var_substitutions: &HashMap<Id, Id>, subst: &mut Subst, cache: &mut HashMap<Id, Id>) {
        if let Some(existing) = var_substitutions.get(&node_id) {
            let var = format!("?{}", node_id).parse().unwrap();
            res.add(ENodeOrVar::Var(var));
            subst.insert(var, *existing);
        } else {
            let new_node = self.explainfind[usize::from(node_id)].node.clone().map_children(|child| {
                if let Some(existing) = cache.get(&child) {
                    *existing
                } else {
                    self.node_to_pattern_internal(res, child, var_substitutions, subst, cache);
                    Id::from(res.as_ref().len() - 1)
                }
            });
            res.add(ENodeOrVar::ENode(new_node));
        }
    }


    fn node_to_flat_explanation(&self, node_id: Id) -> FlatTerm<L> {
        let node = self.explainfind[usize::from(node_id)].node.clone();
        let children = node.fold(vec![], |mut sofar, child| {
            sofar.push(self.node_to_flat_explanation(child));
            sofar
        });
        FlatTerm::new(node, children)
    }

    fn make_rule_table<'a, N: Analysis<L>>(
        rules: &[&'a Rewrite<L, N>],
    ) -> HashMap<Symbol, &'a Rewrite<L, N>> {
        let mut table: HashMap<Symbol, &'a Rewrite<L, N>> = Default::default();
        for r in rules {
            table.insert(r.name, r);
        }
        table
    }

    pub fn check_each_explain<N: Analysis<L>>(&self, rules: &[&Rewrite<L, N>]) -> bool {
        let rule_table = Explain::make_rule_table(rules);
        for i in 0..self.explainfind.len() {
            let explain_node = &self.explainfind[i];

            // check that explanation reasons never form a cycle
            let mut existance = i;
            let mut seen_existance: HashSet<usize> = Default::default();
            loop {
                seen_existance.insert(existance);
                let next = usize::from(self.explainfind[existance].existance_node);
                if existance == next {
                    break;
                }
                existance = next;
                if seen_existance.contains(&existance) {
                    panic!("Cycle in existance!");
                }
            }

            if explain_node.parent_connection.next != Id::from(i) {
                let mut current_explanation = self.node_to_flat_explanation(Id::from(i));
                let mut next_explanation =
                    self.node_to_flat_explanation(explain_node.parent_connection.next);
                if let Justification::Rule(rule_name) =
                    &explain_node.parent_connection.justification
                {
                    if let Some(rule) = rule_table.get(rule_name) {
                        if !explain_node.parent_connection.is_rewrite_forward {
                            std::mem::swap(&mut current_explanation, &mut next_explanation);
                        }
                        if !Explanation::check_rewrite(
                            &current_explanation,
                            &next_explanation,
                            rule,
                        ) {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }

    pub fn new() -> Self {
        Explain {
            explainfind: vec![],
            uncanon_memo: Default::default(),
            shortest_explanation_memo: Default::default(),
        }
    }

    pub(crate) fn set_existance_reason(&mut self, node: Id, existance_node: Id) {
        self.explainfind[usize::from(node)].existance_node = existance_node;
    }

    pub(crate) fn add(&mut self, node: L, set: Id, existance_node: Id) -> Id {
        assert_eq!(self.explainfind.len(), usize::from(set));
        self.uncanon_memo.insert(node.clone(), set);
        self.explainfind.push(ExplainNode {
            node,
            neighbors: vec![],
            parent_connection: Connection {
                justification: Justification::Congruence,
                is_rewrite_forward: false,
                next: Id::from(set),
                current: Id::from(set),
            },
            existance_node,
        });
        set
    }

    // reverse edges recursively to make this node the leader
    fn make_leader(&mut self, node: Id) {
        let next = self.explainfind[usize::from(node)].parent_connection.next;
        if next != node {
            self.make_leader(next);
            let node_connection = &self.explainfind[usize::from(node)].parent_connection;
            let pconnection = Connection {
                justification: node_connection.justification.clone(),
                is_rewrite_forward: !node_connection.is_rewrite_forward,
                next: node,
                current: next,
            };
            self.explainfind[usize::from(next)].parent_connection = pconnection;
        }
    }

    pub(crate) fn alternate_rewrite(&mut self, node1: Id, node2: Id, justification: Justification) {
        if node1 == node2 {
            return;
        }
        if let Some((cost, _)) = self.shortest_explanation_memo.get(&(node1, node2)) {
            if cost <= &1 {
                return;
            }
        }

        let lconnection = Connection {
            justification: justification.clone(),
            is_rewrite_forward: true,
            next: node2,
            current: node1,
        };

        let rconnection = Connection {
            justification: justification,
            is_rewrite_forward: false,
            next: node1,
            current: node2,
        };

        self.explainfind[usize::from(node1)]
            .neighbors
            .push(lconnection);
        self.explainfind[usize::from(node2)]
            .neighbors
            .push(rconnection);
        self.shortest_explanation_memo
            .insert((node1, node2), (1, node2));
        self.shortest_explanation_memo
            .insert((node2, node1), (1, node1));
    }

    pub(crate) fn union(
        &mut self,
        node1: Id,
        node2: Id,
        justification: Justification,
        new_rhs: bool,
    ) {
        if let Justification::Congruence = justification {
            assert!(self.explainfind[usize::from(node1)]
                .node
                .matches(&self.explainfind[usize::from(node2)].node));
        }
        if new_rhs {
            self.set_existance_reason(node2, node1)
        }

        self.make_leader(node1);
        self.explainfind[usize::from(node1)].parent_connection.next = node2;

        if let Justification::Rule(_) = justification {
            self.shortest_explanation_memo
                .insert((node1, node2), (1, node2));
            self.shortest_explanation_memo
                .insert((node2, node1), (1, node1));
        }

        let pconnection = Connection {
            justification: justification.clone(),
            is_rewrite_forward: true,
            next: node2,
            current: node1,
        };
        let other_pconnection = Connection {
            justification,
            is_rewrite_forward: false,
            next: node1,
            current: node2,
        };
        self.explainfind[usize::from(node1)]
            .neighbors
            .push(pconnection.clone());
        self.explainfind[usize::from(node2)]
            .neighbors
            .push(other_pconnection);
        self.explainfind[usize::from(node1)].parent_connection = pconnection;
    }

    pub(crate) fn get_union_equalities(&self) -> UnionEqualities {
        let mut equalities = vec![];
        for node in &self.explainfind {
            for neighbor in &node.neighbors {
                if neighbor.is_rewrite_forward {
                    match neighbor.justification {
                        Justification::Rule(r) => {
                            equalities.push((neighbor.current, neighbor.next, r));
                        }
                        _ => (),
                    }
                }
            }
        }
        equalities
    }

    pub(crate) fn populate_enodes<N: Analysis<L>>(&self, mut egraph: EGraph<L, N>) -> EGraph<L, N> {
        for i in 0..self.explainfind.len() {
            let node = &self.explainfind[i];
            egraph.add(node.node.clone());
        }

        egraph
    }

    pub(crate) fn explain_equivalence<N: Analysis<L>>(
        &mut self,
        left: Id,
        right: Id,
        memo: &HashMap<L, Id>,
        unionfind: &mut UnionFind,
        classes: &HashMap<Id, EClass<L, N::Data>>,
        optimize_iters: usize,
        greedy_search: bool,
    ) -> Explanation<L> {
        self.calculate_shortest_explanations::<N>(
            left,
            right,
            classes,
            &unionfind,
            optimize_iters,
            greedy_search,
        );

        let mut cache = Default::default();
        let mut enode_cache = Default::default();
        Explanation::new(self.explain_enodes(left, right, &mut cache, &mut enode_cache, false))
    }

    pub(crate) fn explain_existance(&mut self, left: Id) -> Explanation<L> {
        let mut cache = Default::default();
        let mut enode_cache = Default::default();
        Explanation::new(self.explain_enode_existance(
            left,
            self.node_to_explanation(left, &mut enode_cache),
            &mut cache,
            &mut enode_cache,
        ))
    }

    fn common_ancestor(&self, mut left: Id, mut right: Id) -> Id {
        let mut seen_left: HashSet<Id> = Default::default();
        let mut seen_right: HashSet<Id> = Default::default();
        loop {
            seen_left.insert(left);
            if seen_right.contains(&left) {
                return left;
            }

            seen_right.insert(right);
            if seen_left.contains(&right) {
                return right;
            }

            let next_left = self.explainfind[usize::from(left)].parent_connection.next;
            let next_right = self.explainfind[usize::from(right)].parent_connection.next;
            assert!(next_left != left || next_right != right);
            left = next_left;
            right = next_right;
        }
    }

    fn get_connections(&self, mut node: Id, ancestor: Id) -> Vec<Connection> {
        if node == ancestor {
            return vec![];
        }

        let mut nodes = vec![];
        loop {
            let next = self.explainfind[usize::from(node)].parent_connection.next;
            nodes.push(
                self.explainfind[usize::from(node)]
                    .parent_connection
                    .clone(),
            );
            if next == ancestor {
                return nodes;
            }
            assert!(next != node);
            node = next;
        }
    }

    fn get_path_unoptimized(&self, left: Id, right: Id) -> (Vec<Connection>, Vec<Connection>) {
        let ancestor = self.common_ancestor(left, right);
        let left_connections = self.get_connections(left, ancestor);
        let right_connections = self.get_connections(right, ancestor);
        (left_connections, right_connections)
    }

    fn get_neighbor(&self, current: Id, next: Id) -> Connection {
        for neighbor in &self.explainfind[usize::from(current)].neighbors {
            if neighbor.next == next {
                if let Justification::Rule(_) = neighbor.justification {
                    return neighbor.clone();
                }
            }
        }
        return Connection {
            justification: Justification::Congruence,
            current: current,
            next: next,
            is_rewrite_forward: true,
        };
    }   

    fn get_path(&self, mut left: Id, right: Id) -> (Vec<Connection>, Vec<Connection>) {
        let mut left_connections = vec![];
        loop {
            if left == right {
                return (left_connections, vec![]);
            }
            if let Some((_, next)) = self.shortest_explanation_memo.get(&(left, right)) {
                left_connections.push(self.get_neighbor(left, *next));
                left = *next;
            } else {
                break;
            }
        }

        let (restleft, right_connections) = self.get_path_unoptimized(left, right);
        left_connections.extend(restleft);
        (left_connections, right_connections)
    }

    fn explain_enode_existance(
        &self,
        node: Id,
        rest_of_proof: Rc<TreeTerm<L>>,
        cache: &mut ExplainCache<L>,
        enode_cache: &mut NodeExplanationCache<L>,
    ) -> TreeExplanation<L> {
        let graphnode = &self.explainfind[usize::from(node)];
        let existance = graphnode.existance_node;
        let existance_node = &self.explainfind[usize::from(existance)];
        // case 1)
        if existance == node {
            return vec![self.node_to_explanation(node, enode_cache), rest_of_proof];
        }

        // case 2)
        if graphnode.parent_connection.next == existance
            || existance_node.parent_connection.next == node
        {
            let direction;
            let justification;
            if graphnode.parent_connection.next == existance {
                direction = !graphnode.parent_connection.is_rewrite_forward;
                justification = &graphnode.parent_connection.justification;
            } else {
                direction = existance_node.parent_connection.is_rewrite_forward;
                justification = &existance_node.parent_connection.justification;
            }
            return self.explain_enode_existance(
                existance,
                self.explain_adjacent(
                    existance,
                    node,
                    direction,
                    justification,
                    cache,
                    enode_cache,
                    false,
                ),
                cache,
                enode_cache,
            );
        }

        // case 3)
        let mut new_rest_of_proof = (*self.node_to_explanation(existance, enode_cache)).clone();
        let mut index_of_child = 0;
        let mut found = false;
        existance_node.node.for_each(|child| {
            if found {
                return;
            }
            if child == node {
                found = true;
            } else {
                index_of_child += 1;
            }
        });
        assert!(found);
        new_rest_of_proof.child_proofs[index_of_child].push(rest_of_proof);

        self.explain_enode_existance(existance, Rc::new(new_rest_of_proof), cache, enode_cache)
    }

    fn explain_enodes(
        &self,
        left: Id,
        right: Id,
        cache: &mut ExplainCache<L>,
        node_explanation_cache: &mut NodeExplanationCache<L>,
        use_unoptimized: bool,
    ) -> TreeExplanation<L> {
        let mut proof = vec![self.node_to_explanation(left, node_explanation_cache)];

        let (left_connections, right_connections) = if use_unoptimized {
            self.get_path_unoptimized(left, right)
        } else {
            self.get_path(left, right)
        };

        for (i, connection) in left_connections
            .iter()
            .chain(right_connections.iter().rev())
            .enumerate()
        {
            let mut direction = connection.is_rewrite_forward;
            let mut next = connection.next;
            let mut current = connection.current;
            if i >= left_connections.len() {
                direction = !direction;
                std::mem::swap(&mut next, &mut current);
            }

            proof.push(self.explain_adjacent(
                current,
                next,
                direction,
                &connection.justification,
                cache,
                node_explanation_cache,
                use_unoptimized,
            ));
        }
        proof
    }

    fn explain_adjacent(
        &self,
        current: Id,
        next: Id,
        rule_direction: bool,
        justification: &Justification,
        cache: &mut ExplainCache<L>,
        node_explanation_cache: &mut NodeExplanationCache<L>,
        use_unoptimized: bool,
    ) -> Rc<TreeTerm<L>> {
        let fingerprint = (current, next);

        if let Some(answer) = cache.get(&fingerprint) {
            return answer.clone();
        }

        let term = match justification {
            Justification::Rule(name) => {
                let mut rewritten =
                    (*self.node_to_explanation(next, node_explanation_cache)).clone();
                if rule_direction {
                    rewritten.forward_rule = Some(*name);
                } else {
                    rewritten.backward_rule = Some(*name);
                }

                rewritten.current = next;
                rewritten.last = current;

                Rc::new(rewritten)
            }
            Justification::Congruence => {
                // add the children proofs to the last explanation
                let current_node = &self.explainfind[usize::from(current)].node;
                let next_node = &self.explainfind[usize::from(next)].node;
                assert!(current_node.matches(next_node));
                let mut subproofs = vec![];

                for (left_child, right_child) in current_node
                    .children()
                    .iter()
                    .zip(next_node.children().iter())
                {
                    subproofs.push(self.explain_enodes(
                        *left_child,
                        *right_child,
                        cache,
                        node_explanation_cache,
                        use_unoptimized,
                    ));
                }
                Rc::new(TreeTerm::new(current_node.clone(), subproofs))
            }
        };

        cache.insert(fingerprint, term.clone());

        term
    }

    fn find_all_enodes(&self, eclass: Id) -> HashSet<Id> {
        let mut enodes = HashSet::default();
        let mut todo = vec![eclass];

        while todo.len() > 0 {
            let current = todo.pop().unwrap();
            if enodes.insert(current) {
                for neighbor in &self.explainfind[usize::from(current)].neighbors {
                    todo.push(neighbor.next);
                }
            }
        }
        enodes
    }

    fn add_tree_depths(&self, node: Id, depths: &mut HashMap<Id, usize>) -> usize {
        if depths.get(&node).is_none() {
            let parent = self.parent(node);
            let depth = if parent == node {
                0
            } else {
                self.add_tree_depths(parent, depths) + 1
            };
            depths.insert(node, depth);
        }
        return *depths.get(&node).unwrap();
    }

    fn calculate_tree_depths(&self) -> HashMap<Id, usize> {
        let mut depths = HashMap::default();
        for i in 0..self.explainfind.len() {
            self.add_tree_depths(Id::from(i), &mut depths);
        }
        return depths;
    }

    // For every possible proof length query for this eclass, find the best path.
    // When congruence proof sizes are absent, ignore them.
    fn shortest_explanations_eclass(
        &mut self,
        eclass: Id,
        congruent_nodes: &Vec<Vec<Id>>,
        eclass_congruence_queries: &HashMap<Id, Vec<(Id, Id)>>,
    ) -> bool {
        let enodes = self.find_all_enodes(eclass);
        let mut did_anything = false;

        // update the shortest path between all of the queries
        for (start, end) in eclass_congruence_queries.get(&eclass).unwrap_or(&vec![]) {
            let cost_before = self
                .shortest_explanation_memo
                .get(&(*start, *end))
                .map(|(cost, _next)| *cost);
            let mut ends: HashSet<Id> = Default::default();
            ends.insert(*end);
            self.shortest_path_modulo_congruence(
                *start,
                &ends,
                congruent_nodes,
                &mut Default::default(),
                false,
                true,
            );
            let cost_after = self
                .shortest_explanation_memo
                .get(&(*start, *end))
                .map(|(cost, _next)| *cost);
            if cost_before != cost_after {
                if let (Some(before), Some(after)) = (cost_before, cost_after) {
                    assert!(after < before);
                }
                did_anything = true;
            }
        }

        // updates shortest paths based on all possible intermediates
        /*for intermediate in &enodes {
            for start in &enodes {
                for end in &enodes {
                    let start_to_intermediate = if let Some(v) =
                        self.shortest_explanation_memo.get(&(*start, *intermediate))
                    {
                        *v
                    } else {
                        continue;
                    };
                    let intermediate_to_end = if let Some(v) =
                        self.shortest_explanation_memo.get(&(*intermediate, *end))
                    {
                        *v
                    } else {
                        continue;
                    };
                    let old =
                        if let Some((c, _)) = self.shortest_explanation_memo.get(&(*start, *end)) {
                            *c
                        } else {
                            usize::MAX
                        };
                    let new = start_to_intermediate
                        .0
                        .checked_add(intermediate_to_end.0)
                        .unwrap();
                    if new < old {
                        self.shortest_explanation_memo
                            .insert((*start, *end), (new, start_to_intermediate.1));
                        did_anything = true;
                    }
                }
            }
        }*/

        did_anything
    }

    fn replace_distance(&mut self, current: Id, next: Id, right: Id, distance: usize) {
        self.shortest_explanation_memo
            .insert((current, right), (distance, next));
    }

    fn populate_path_length(
        &mut self,
        start: Id,
        right: Id,
        left_connections: &Vec<Connection>,
        distance_memo: &mut DistanceMemo,
        target_cost: usize,
        use_estimates: bool,
    ) {
        self.shortest_explanation_memo
            .insert((right, right), (0, right));
        let mut last_cost = 0;
        for connection in left_connections.iter().rev() {
            let next = connection.next;
            let current = connection.current;
            let next_cost = self
                .shortest_explanation_memo
                .get(&(next, right))
                .unwrap()
                .0;
            let dist = if use_estimates {
                self.connection_distance(connection, distance_memo)
            } else {
                self.connection_distance_cached(connection).unwrap()
            };
            last_cost = dist + next_cost;
            self.replace_distance(current, next, right, next_cost + dist);
        }
        assert!(last_cost <= target_cost);    
            
        
    }

    fn distance_between(&mut self, left: Id, right: Id, distance_memo: &mut DistanceMemo) -> usize {
        if left == right {
            return 0;
        }
        let ancestor = if let Some(a) = distance_memo.common_ancestor.get(&(left, right)) {
            *a
        } else {
            // fall back on calculating ancestor for top-level query (not from congruence)
            self.common_ancestor(left, right)
        };
        // calculate edges until you are past the ancestor
        self.calculate_parent_distance(left, ancestor, distance_memo);
        self.calculate_parent_distance(right, ancestor, distance_memo);

        // now all three share an ancestor
        let a = self.calculate_parent_distance(ancestor, Id::from(usize::MAX), distance_memo);
        let b = self.calculate_parent_distance(left, Id::from(usize::MAX), distance_memo);
        let c = self.calculate_parent_distance(right, Id::from(usize::MAX), distance_memo);

        assert!(
            distance_memo.parent_distance[usize::from(ancestor)].0
                == distance_memo.parent_distance[usize::from(left)].0
        );
        assert!(
            distance_memo.parent_distance[usize::from(ancestor)].0
                == distance_memo.parent_distance[usize::from(right)].0
        );

        // calculate distance to find upper bound
        let dist = b
            .checked_add(c)
            .unwrap_or_else(|| panic!("overflow in proof size calculation!"))
            .checked_sub(
                a.checked_mul(2)
                    .unwrap_or_else(|| panic!("overflow in proof size calculation!")),
            )
            .unwrap_or_else(|| panic!("common ancestor distance was too large!"));

        //assert_eq!(dist+1, Explanation::new(self.explain_enodes(left, right, &mut Default::default())).make_flat_explanation().len());

        return dist;
    }

    fn congruence_distance_cached(&self, current: Id, next: Id) -> Option<usize> {
        let current_node = self.explainfind[usize::from(current)].node.clone();
        let next_node = self.explainfind[usize::from(next)].node.clone();
        let mut cost: usize = 0;
        for (left_child, right_child) in current_node
            .children()
            .iter()
            .zip(next_node.children().iter())
        {
            if let Some((cached_cost, _next)) = self
                .shortest_explanation_memo
                .get(&(*left_child, *right_child))
            {
                cost = cost.checked_add(*cached_cost).unwrap();
            } else {
                return None;
            }
        }
        Some(cost)
    }

    // TODO use bigint because this overflows easily
    fn congruence_distance(
        &mut self,
        current: Id,
        next: Id,
        distance_memo: &mut DistanceMemo,
    ) -> usize {
        let current_node = self.explainfind[usize::from(current)].node.clone();
        let next_node = self.explainfind[usize::from(next)].node.clone();
        let mut cost: usize = 0;
        for (left_child, right_child) in current_node
            .children()
            .iter()
            .zip(next_node.children().iter())
        {
            cost = cost
                .checked_add(self.distance_between(*left_child, *right_child, distance_memo))
                .unwrap();
        }
        cost
    }

    fn connection_distance(
        &mut self,
        connection: &Connection,
        distance_memo: &mut DistanceMemo,
    ) -> usize {
        match connection.justification {
            Justification::Congruence => {
                self.congruence_distance(connection.current, connection.next, distance_memo)
            }
            Justification::Rule(_) => 1,
        }
    }

    fn connection_distance_cached(&mut self, connection: &Connection) -> Option<usize> {
        match connection.justification {
            Justification::Congruence => {
                self.congruence_distance_cached(connection.current, connection.next)
            }
            Justification::Rule(_) => Some(1),
        }
    }

    fn calculate_parent_distance(
        &mut self,
        enode: Id,
        ancestor: Id,
        distance_memo: &mut DistanceMemo,
    ) -> usize {
        loop {
            let parent = distance_memo.parent_distance[usize::from(enode)].0;
            let dist = distance_memo.parent_distance[usize::from(enode)].1;
            if self.parent(parent) == parent {
                break;
            }

            let parent_parent = distance_memo.parent_distance[usize::from(parent)].0;
            if parent_parent != parent {
                let new_dist = dist + distance_memo.parent_distance[usize::from(parent)].1;
                distance_memo.parent_distance[usize::from(enode)] = (parent_parent, new_dist);
            } else {
                if ancestor == Id::from(usize::MAX) {
                    break;
                }
                if distance_memo.tree_depth.get(&parent).unwrap()
                    <= distance_memo.tree_depth.get(&ancestor).unwrap()
                {
                    break;
                }

                // find the length of one parent connection
                let connection = &self.explainfind[usize::from(parent)].parent_connection;
                let current = connection.current;
                let next = connection.next;
                let cost = match connection.justification {
                    Justification::Congruence => {
                        self.congruence_distance(current, next, distance_memo)
                    }
                    Justification::Rule(_) => 1,
                };
                distance_memo.parent_distance[usize::from(parent)] = (self.parent(parent), cost);
            }
        }

        //assert_eq!(distance_memo.parent_distance[usize::from(enode)].1+1,
        //Explanation::new(self.explain_enodes(enode, distance_memo.parent_distance[usize::from(enode)].0, &mut Default::default())).make_flat_explanation().len());

        distance_memo.parent_distance[usize::from(enode)].1
    }

    fn find_congruence_neighbors<N: Analysis<L>>(
        &self,
        classes: &HashMap<Id, EClass<L, N::Data>>,
        congruence_neighbors: &mut Vec<Vec<Id>>,
        unionfind: &UnionFind,
    ) {
        let mut counter = 0;
        // add the normal congruence edges first
        for node in &self.explainfind {
            match node.parent_connection.justification {
                Justification::Congruence => {
                    let current = node.parent_connection.current;
                    let next = node.parent_connection.next;
                    congruence_neighbors[usize::from(current)].push(next);
                    congruence_neighbors[usize::from(next)].push(current);
                    counter += 1;
                }
                _ => (),
            }
        }

        'outer: for eclass in classes.keys() {
            let enodes = self.find_all_enodes(*eclass);
            // find all congruence nodes
            let mut cannon_enodes: HashMap<L, Vec<Id>> = Default::default();
            for enode in &enodes {
                let cannon = self.explainfind[usize::from(*enode)]
                    .node
                    .clone()
                    .map_children(|child| unionfind.find(child));
                if let Some(others) = cannon_enodes.get_mut(&cannon) {
                    for other in others.iter() {
                        congruence_neighbors[usize::from(*enode)].push(*other);
                        congruence_neighbors[usize::from(*other)].push(*enode);
                    }
                    counter += 1;
                    others.push(*enode);
                } else {
                    counter += 1;
                    cannon_enodes.insert(cannon, vec![*enode]);
                }
                // Don't find every congruence edge because that could be n^2 edges
                if counter > CONGRUENCE_LIMIT * self.explainfind.len() {
                    break 'outer;
                }
            }
        }
    }

    pub fn get_num_congr<N: Analysis<L>>(
        &self,
        classes: &HashMap<Id, EClass<L, N::Data>>,
        unionfind: &UnionFind,
    ) -> usize {
        let mut congruence_neighbors = vec![vec![]; self.explainfind.len()];
        self.find_congruence_neighbors::<N>(classes, &mut congruence_neighbors, unionfind);
        let mut count = 0;
        for v in congruence_neighbors {
            count += v.len();
        }

        count / 2
    }

    pub fn get_num_nodes(&self) -> usize {
        self.explainfind.len()
    }

    fn shortest_path_modulo_congruence(
        &mut self,
        start: Id,
        ends: &HashSet<Id>,
        congruence_neighbors: &Vec<Vec<Id>>,
        distance_memo: &mut DistanceMemo,
        // use estimates means use vanilla proof lengths- use this for greedy optimization
        use_estimates: bool,
        update_paths: bool,
    ) -> Option<(Vec<Connection>, Vec<Connection>)> {
        let mut todo = BinaryHeap::new();
        todo.push(HeapState {
            cost: 0,
            item: Connection {
                current: start,
                next: start,
                justification: Justification::Congruence,
                is_rewrite_forward: true,
            },
        });

        let mut last = HashMap::default();
        let mut path_cost = HashMap::default();
        let first_end = *ends.iter().next().unwrap(); 

        'outer: loop {
            if todo.len() == 0 {
                break 'outer;
            }
            let state = todo.pop().unwrap();
            let connection = state.item;
            let cost_so_far = state.cost;
            let current = connection.next;

            if let Some(_) = last.get(&current) {
                continue;
            } else {
                last.insert(current, connection);
                path_cost.insert(current, cost_so_far);
            }

            if use_estimates && current == first_end {
                break;
            }

            for neighbor in &self.explainfind[usize::from(current)].neighbors {
                if let Justification::Rule(_) = neighbor.justification {
                    let neighbor_cost = cost_so_far.checked_add(1).unwrap();
                    todo.push(HeapState {
                        item: neighbor.clone(),
                        cost: neighbor_cost,
                    });
                }
            }

            'inner: for other in congruence_neighbors[usize::from(current)].iter() {
                let next = other;
                let distance = if use_estimates {
                    self.congruence_distance(current, *next, distance_memo)
                } else {
                    if let Some(dist) = self.congruence_distance_cached(current, *next) {
                        dist
                    } else {
                        continue 'inner;
                    }
                };
                let next_cost = cost_so_far + distance;
                todo.push(HeapState {
                    item: Connection {
                        current: current,
                        next: *next,
                        justification: Justification::Congruence,
                        is_rewrite_forward: true,
                    },
                    cost: next_cost,
                });
            }
        }

        let total_cost = path_cost.get(&first_end);

        let mut left_connections = vec![];
        let mut right_connections = vec![];

        // assert that we found a path better than the normal one
        if use_estimates {
            let dist = self.distance_between(start, first_end, distance_memo);
            if *total_cost.unwrap() > dist {
                panic!(
                    "Found cost greater than baseline {} vs {}",
                    total_cost.unwrap(), dist
                );
            }
        }
        if use_estimates && *total_cost.unwrap() == self.distance_between(start, first_end, distance_memo) {
            let (a_left_connections, a_right_connections) = self.get_path_unoptimized(start, first_end);
            left_connections = a_left_connections;
            right_connections = a_right_connections;
        } else {
            let mut is_first = true;

            'ends: for end in ends {
                if update_paths {
                    let mut current = *end;
                    let mut connections = vec![];
                    while current != start {
                        let prev = last.get(&current);
                        if prev.is_none() {
                            continue 'ends;
                        } else {
                            let prev_connection = prev.unwrap();
                            connections.push(prev_connection.clone());
                            current = prev_connection.current;
                        }
                    }
                    connections.reverse();
                    self.populate_path_length(
                        start,
                        *end,
                        &connections,
                        distance_memo,
                        *path_cost.get(end).unwrap(),
                        use_estimates,
                    );
                    if is_first {
                        left_connections = connections;
                        is_first = false;
                    }
                } else {
                    if let Some(found_cost) = path_cost.get(end) {
                        self.shortest_explanation_memo.insert((start, *end), (*found_cost, start));
                    }
                }
            }
        }

        Some((left_connections, right_connections))
    }

    fn greedy_short_explanations(
        &mut self,
        start: Id,
        end: Id,
        congruence_neighbors: &Vec<Vec<Id>>,
        unionfind: &UnionFind,
        distance_memo: &mut DistanceMemo,
        eclass_seen_memo: &mut HashSet<Id>,
        mut fuel: usize,
    ) {
        let mut todo_congruence = VecDeque::new();
        todo_congruence.push_back((start, end));

        while todo_congruence.len() > 0 {
            let (start, end) = todo_congruence.pop_front().unwrap();
            let eclass_size = self.find_all_enodes(start).len();
            if fuel < eclass_size {
                continue;
            }
            fuel -= eclass_size;

            let mut ends: HashSet<Id> = Default::default();
            ends.insert(end);
            let (left_connections, right_connections) = self
                .shortest_path_modulo_congruence(
                    start,
                    &ends,
                    congruence_neighbors,
                    distance_memo,
                    true,
                    true,
                )
                .unwrap();

            //assert!(Explanation::new(self.explain_enodes(start, end, &mut Default::default())).make_flat_explanation().len()-1 <= total_cost);

            for (i, connection) in left_connections
                .iter()
                .chain(right_connections.iter().rev())
                .enumerate()
            {
                let mut next = connection.next;
                let mut current = connection.current;
                if i >= left_connections.len() {
                    std::mem::swap(&mut next, &mut current);
                }
                if let Justification::Congruence = connection.justification {
                    let current_node = self.explainfind[usize::from(current)].node.clone();
                    let next_node = self.explainfind[usize::from(next)].node.clone();
                    for (left_child, right_child) in current_node
                        .children()
                        .iter()
                        .zip(next_node.children().iter())
                    {
                        todo_congruence.push_back((*left_child, *right_child));
                    }
                }
            }
        }
    }

    fn tarjan_ocla(
        &self,
        enode: Id,
        children: &HashMap<Id, Vec<Id>>,
        common_ancestor_queries: &HashMap<Id, Vec<Id>>,
        black_set: &mut HashSet<Id>,
        unionfind: &mut UnionFind,
        ancestor: &mut Vec<Id>,
        common_ancestor: &mut HashMap<(Id, Id), Id>,
    ) {
        ancestor[usize::from(enode)] = enode;
        for child in children[&enode].iter() {
            self.tarjan_ocla(
                *child,
                children,
                common_ancestor_queries,
                black_set,
                unionfind,
                ancestor,
                common_ancestor,
            );
            unionfind.union(enode, *child);
            ancestor[usize::from(unionfind.find(enode))] = enode;
        }

        if common_ancestor_queries.get(&enode).is_some() {
            black_set.insert(enode);
            for other in common_ancestor_queries.get(&enode).unwrap() {
                if black_set.contains(&other) {
                    let ancestor = ancestor[usize::from(unionfind.find(*other))];
                    common_ancestor.insert((enode, *other), ancestor);
                    common_ancestor.insert((*other, enode), ancestor);
                }
            }
        }
    }

    fn parent(&self, enode: Id) -> Id {
        self.explainfind[usize::from(enode)].parent_connection.next
    }

    fn calculate_common_ancestor<N: Analysis<L>>(
        &self,
        classes: &HashMap<Id, EClass<L, N::Data>>,
        congruence_neighbors: &Vec<Vec<Id>>,
    ) -> HashMap<(Id, Id), Id> {
        let mut common_ancestor_queries = HashMap::default();
        for s_int in 0..congruence_neighbors.len() {
            let start = &Id::from(s_int);
            let others = &congruence_neighbors[s_int];
            for other in others {
                for (left, right) in self.explainfind[usize::from(*start)]
                    .node
                    .children()
                    .iter()
                    .zip(self.explainfind[usize::from(*other)].node.children().iter())
                {
                    if left != right {
                        if common_ancestor_queries.get(start).is_none() {
                            common_ancestor_queries.insert(*start, vec![]);
                        }
                        if common_ancestor_queries.get(other).is_none() {
                            common_ancestor_queries.insert(*other, vec![]);
                        }
                        common_ancestor_queries.get_mut(start).unwrap().push(*other);
                        common_ancestor_queries.get_mut(other).unwrap().push(*start);
                    }
                }
            }
        }

        let mut common_ancestor = HashMap::default();
        let mut unionfind = UnionFind::default();
        let mut ancestor = vec![];
        for i in 0..self.explainfind.len() {
            unionfind.make_set();
            ancestor.push(Id::from(i));
        }
        for (eclass, _) in classes.iter() {
            let enodes = self.find_all_enodes(*eclass);
            let mut children: HashMap<Id, Vec<Id>> = HashMap::default();
            for enode in &enodes {
                children.insert(*enode, vec![]);
            }
            for enode in &enodes {
                if self.parent(*enode) != *enode {
                    children.get_mut(&self.parent(*enode)).unwrap().push(*enode);
                }
            }

            let mut black_set = HashSet::default();

            let mut parent = *enodes.iter().next().unwrap();
            while parent != self.parent(parent) {
                parent = self.parent(parent);
            }
            self.tarjan_ocla(
                parent,
                &children,
                &common_ancestor_queries,
                &mut black_set,
                &mut unionfind,
                &mut ancestor,
                &mut common_ancestor,
            );
        }

        common_ancestor
    }

    fn set_rewrite_distances(&mut self) {
        for i in 0..self.explainfind.len() {
            self.shortest_explanation_memo
                .insert((Id::from(i), Id::from(i)), (0, Id::from(0)));
            for child in &self.explainfind[i].neighbors {
                if let Justification::Rule(_) = child.justification {
                    self.shortest_explanation_memo
                        .insert((child.current, child.next), (1, child.next));
                }
            }
        }
    }

    fn find_congruence_queries(
        &self,
        unionfind: &UnionFind,
        congruence_neighbors: &Vec<Vec<Id>>,
    ) -> Vec<HashSet<Id>> {
        let mut queries: Vec<HashSet<Id>> = vec![Default::default(); self.explainfind.len()];
        for (i, neighbors) in congruence_neighbors.iter().enumerate() {
            for neighbor in neighbors {
                let current = &self.explainfind[usize::from(Id::from(i))].node;
                let next = &self.explainfind[usize::from(*neighbor)].node;
                for (left, right) in current.children().iter().zip(next.children().iter()) {
                    if left == right {
                        continue;
                    }
                    queries[usize::from(*left)].insert(*right);
                }
            }
        }
        queries
    }

    fn calculate_shortest_explanations<N: Analysis<L>>(
        &mut self,
        start: Id,
        end: Id,
        classes: &HashMap<Id, EClass<L, N::Data>>,
        unionfind: &UnionFind,
        iters: usize,
        greedy_search: bool,
    ) {
        if iters == 0 && !greedy_search {
            return;
        }
        let mut congruence_neighbors = vec![vec![]; self.explainfind.len()];
        self.find_congruence_neighbors::<N>(classes, &mut congruence_neighbors, unionfind);
        let mut parent_distance = vec![(Id::from(0), 0); self.explainfind.len()];
        for i in 0..self.explainfind.len() {
            parent_distance[i] = (Id::from(i), 0);
        }
        let mut distance_memo = DistanceMemo {
            parent_distance,
            common_ancestor: self.calculate_common_ancestor::<N>(classes, &congruence_neighbors),
            tree_depth: self.calculate_tree_depths(),
        };

        if greedy_search {
            let mut eclass_seen_memo = HashSet::default();
            let fuel = iters * self.explainfind.len();
            self.greedy_short_explanations(
                start,
                end,
                &congruence_neighbors,
                &unionfind,
                &mut distance_memo,
                &mut eclass_seen_memo,
                fuel,
            );
        } else {
            let mut eclass_congruence_queries =
                self.find_congruence_queries(unionfind, &congruence_neighbors);
            eclass_congruence_queries[usize::from(start)].insert(end);
            // clear the memo and start from scratch
            self.shortest_explanation_memo.clear();

            // initialize distances to self
            for i in 0..self.explainfind.len() {
                self.shortest_explanation_memo
                    .insert((Id::from(i), Id::from(i)), (0, Id::from(i)));
            }

            for i in 0..iters {
                let start_time = Instant::now();
                let mut did_something = false;
                for start in 0..eclass_congruence_queries.len() {
                    let ends = &eclass_congruence_queries[start];
                    if ends.len() == 0 {
                        continue;
                    }
                    let costs_before: Vec<Option<usize>> = ends.iter().map(|end| {
                        self
                                        .shortest_explanation_memo
                                        .get(&(Id::from(start), *end))
                                        .map(|(cost, _next)| *cost)
                    }).collect();
                    self.shortest_path_modulo_congruence(
                        Id::from(start),
                        ends,
                        &congruence_neighbors,
                        &mut Default::default(),
                        false,
                        true,
                    );

                    let costs_after: Vec<Option<usize>> = ends.iter().map(|end| {
                        self
                                        .shortest_explanation_memo
                                        .get(&(Id::from(start), *end))
                                        .map(|(cost, _next)| *cost)
                    }).collect();
                    if costs_before != costs_after {
                        for (cost_before, cost_after) in costs_before.iter().zip(costs_after.iter()) {
                            if let (Some(before), Some(after)) = (cost_before, cost_after) {
                                assert!(after <= before);
                            }
                        }
                        
                        did_something = true;
                    }
                }

                //println!("iteration {} took {}", i, start_time.elapsed().as_millis());

                if !did_something {
                    assert!(self.shortest_explanation_memo.get(&(start, end)).is_some());
                    break;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::super::*;

    #[test]
    fn simple_explain() {
        use SymbolLang as S;

        crate::init_logger();
        let mut egraph = EGraph::<S, ()>::default().with_explanations_enabled();

        let fa = "(f a)".parse().unwrap();
        let fb = "(f b)".parse().unwrap();
        egraph.add_expr(&fa);
        egraph.add_expr(&fb);
        egraph.add_expr(&"c".parse().unwrap());
        egraph.add_expr(&"d".parse().unwrap());

        egraph.union_instantiations(
            &"a".parse().unwrap(),
            &"c".parse().unwrap(),
            &Default::default(),
            "ac".to_string(),
        );

        egraph.union_instantiations(
            &"c".parse().unwrap(),
            &"d".parse().unwrap(),
            &Default::default(),
            "cd".to_string(),
        );

        egraph.union_instantiations(
            &"d".parse().unwrap(),
            &"b".parse().unwrap(),
            &Default::default(),
            "db".to_string(),
        );

        egraph.rebuild();

        assert_eq!(
            egraph
                .explain_equivalence(&fa, &fb, 0, false)
                .get_flat_sexps()
                .len(),
            4
        );
        assert_eq!(
            egraph
                .explain_equivalence(&fa, &fb, 100, false)
                .get_flat_sexps()
                .len(),
            4
        );
        assert_eq!(
            egraph
                .explain_equivalence(&fa, &fb, 0, true)
                .get_flat_sexps()
                .len(),
            4
        );

        egraph.union_instantiations(
            &"(f a)".parse().unwrap(),
            &"g".parse().unwrap(),
            &Default::default(),
            "fag".to_string(),
        );
        egraph.union_instantiations(
            &"g".parse().unwrap(),
            &"(f b)".parse().unwrap(),
            &Default::default(),
            "gfb".to_string(),
        );

        egraph.rebuild();

        assert_eq!(
            egraph
                .explain_equivalence(&fa, &fb, 0, false)
                .get_flat_sexps()
                .len(),
            4
        );
        assert_eq!(
            egraph
                .explain_equivalence(&fa, &fb, 1, true)
                .get_flat_sexps()
                .len(),
            3
        );

        assert_eq!(
            egraph
                .explain_equivalence(&fa, &fb, 100, false)
                .get_flat_sexps()
                .len(),
            3
        );

        egraph.dot().to_dot("target/foo.dot").unwrap();
    }
}
