#![allow(clippy::only_used_in_recursion)]
use crate::Symbol;
use crate::{
    util::pretty_print, Analysis, EClass, ENodeOrVar, FromOp, HashMap, HashSet, Id, Language,
    PatternAst, RecExpr, Rewrite, UnionFind, Var,
};

use std::cmp::Ordering;
use std::collections::{BinaryHeap, VecDeque};
use std::fmt::{self, Debug, Display, Formatter};
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

use num_bigint::BigUint;
use num_traits::identities::{One, Zero};
use symbolic_expressions::Sexp;

type ProofCost = BigUint;

const CONGRUENCE_LIMIT: usize = 2;
const GREEDY_NUM_ITERS: usize = 2;

/// A justification for a union, either via a rule or congruence.
/// A direct union with a justification is also stored as a rule.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub enum Justification {
    /// Justification by a rule with this name.
    Rule(Symbol),
    /// Justification by congruence.
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
struct ExplainNode {
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
    explainfind: Vec<ExplainNode>,
    #[cfg_attr(feature = "serde-1", serde(with = "vectorize"))]
    #[cfg_attr(
        feature = "serde-1",
        serde(bound(
            serialize = "L: serde::Serialize",
            deserialize = "L: serde::Deserialize<'de>",
        ))
    )]
    pub uncanon_memo: HashMap<L, Id>,
    /// By default, egg uses a greedy algorithm to find shorter explanations when they are extracted.
    pub optimize_explanation_lengths: bool,
    // For a given pair of enodes in the same eclass,
    // stores the length of the shortest found explanation
    // and the Id of the neighbor for retrieving
    // the explanation.
    // Invariant: The distance is always <= the unoptimized distance
    // That is, less than or equal to the result of `distance_between`
    #[cfg_attr(feature = "serde-1", serde(skip))]
    shortest_explanation_memo: HashMap<(Id, Id), (ProofCost, Id)>,
}

pub(crate) struct ExplainNodes<'a, L: Language> {
    explain: &'a mut Explain<L>,
    nodes: &'a [L],
}

#[derive(Default)]
struct DistanceMemo {
    parent_distance: Vec<(Id, ProofCost)>,
    common_ancestor: HashMap<(Id, Id), Id>,
    tree_depth: HashMap<Id, ProofCost>,
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
    /// Get each flattened term in the explanation as an s-expression string.
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
    pub fn get_flat_string(&mut self) -> String {
        self.get_flat_strings().join("\n")
    }

    /// Get each the tree-style explanation as an s-expression string.
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
    pub fn get_string(&self) -> String {
        self.to_string()
    }

    /// Get the tree-style explanation as an s-expression string
    /// with let binding to enable sharing of subproofs.
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
    pub fn get_string_with_let(&self) -> String {
        let mut s = "".to_string();
        pretty_print(&mut s, &self.get_sexp_with_let(), 100, 0).unwrap();
        s
    }

    /// Get each term in the explanation as a string.
    /// See [`get_string`](Explanation::get_string) for the format of these strings.
    pub fn get_flat_strings(&mut self) -> Vec<String> {
        self.make_flat_explanation()
            .iter()
            .map(|e| e.to_string())
            .collect()
    }

    fn get_sexp(&self) -> Sexp {
        let mut items = vec![Sexp::String("Explanation".to_string())];
        for e in self.explanation_trees.iter() {
            items.push(e.get_sexp());
        }

        Sexp::List(items)
    }

    /// Get the size of this explanation tree in terms of the number of rewrites
    /// in the let-bound version of the tree.
    pub fn get_tree_size(&self) -> ProofCost {
        let mut seen = Default::default();
        let mut seen_adjacent = Default::default();
        let mut sum: ProofCost = BigUint::zero();
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
    ) -> ProofCost {
        if !seen.insert(&**current as *const TreeTerm<L>) {
            return BigUint::zero();
        }
        let mut my_size: ProofCost = BigUint::zero();
        if current.forward_rule.is_some() {
            my_size += 1_u32;
        }
        if current.backward_rule.is_some() {
            my_size += 1_u32;
        }
        assert!(my_size.is_zero() || my_size.is_one());
        if my_size.is_one() {
            if !seen_adjacent.insert((current.current, current.last)) {
                return BigUint::zero();
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

    fn get_sexp_with_let(&self) -> Sexp {
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

    // for every subterm which is shared in
    // multiple places, add it to to_let_bind
    fn find_to_let_bind(
        &self,
        term: Rc<TreeTerm<L>>,
        shared: &mut HashSet<*const TreeTerm<L>>,
        to_let_bind: &mut Vec<Rc<TreeTerm<L>>>,
    ) {
        if !term.child_proofs.is_empty() {
            if shared.insert(&*term as *const TreeTerm<L>) {
                for proof in &term.child_proofs {
                    for child in proof {
                        self.find_to_let_bind(child.clone(), shared, to_let_bind);
                    }
                }
            } else {
                to_let_bind.push(term);
            }
        }
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
    pub fn check_proof<'a, R, N>(&mut self, rules: R)
    where
        R: IntoIterator<Item = &'a Rewrite<L, N>>,
        L: 'a,
        N: Analysis<L> + 'a,
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
            backward_rule: self.backward_rule,
            forward_rule: self.forward_rule,
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
            backward_rule: self.backward_rule,
            forward_rule: self.forward_rule,
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
    /// See [`get_flat_string`](Explanation::get_flat_string) for the format of these expressions.
    pub fn get_string(&self) -> String {
        self.get_sexp().to_string()
    }

    fn get_sexp(&self) -> Sexp {
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
        self.remove_rewrites().to_string().parse().unwrap()
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
    fn get_sexp(&self) -> Sexp {
        self.get_sexp_with_bindings(&Default::default())
    }

    fn get_sexp_with_bindings(&self, bindings: &HashMap<*const TreeTerm<L>, Sexp>) -> Sexp {
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
#[derive(Clone, Eq, PartialEq)]
struct HeapState<I> {
    cost: ProofCost,
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
    fn make_rule_table<'a, N: Analysis<L>>(
        rules: &[&'a Rewrite<L, N>],
    ) -> HashMap<Symbol, &'a Rewrite<L, N>> {
        let mut table: HashMap<Symbol, &'a Rewrite<L, N>> = Default::default();
        for r in rules {
            table.insert(r.name, r);
        }
        table
    }
    pub fn new() -> Self {
        Explain {
            explainfind: vec![],
            uncanon_memo: Default::default(),
            shortest_explanation_memo: Default::default(),
            optimize_explanation_lengths: true,
        }
    }

    pub(crate) fn set_existance_reason(&mut self, node: Id, existance_node: Id) {
        self.explainfind[usize::from(node)].existance_node = existance_node;
    }

    pub(crate) fn add(&mut self, node: L, set: Id, existance_node: Id) -> Id {
        assert_eq!(self.explainfind.len(), usize::from(set));
        self.uncanon_memo.insert(node, set);
        self.explainfind.push(ExplainNode {
            neighbors: vec![],
            parent_connection: Connection {
                justification: Justification::Congruence,
                is_rewrite_forward: false,
                next: set,
                current: set,
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
            if cost.is_zero() || cost.is_one() {
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
            justification,
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
            .insert((node1, node2), (BigUint::one(), node2));
        self.shortest_explanation_memo
            .insert((node2, node1), (BigUint::one(), node1));
    }

    pub(crate) fn union(
        &mut self,
        node1: Id,
        node2: Id,
        justification: Justification,
        new_rhs: bool,
    ) {
        if let Justification::Congruence = justification {
            // assert!(self.node(node1).matches(self.node(node2)));
        }
        if new_rhs {
            self.set_existance_reason(node2, node1)
        }

        self.make_leader(node1);
        self.explainfind[usize::from(node1)].parent_connection.next = node2;

        if let Justification::Rule(_) = justification {
            self.shortest_explanation_memo
                .insert((node1, node2), (BigUint::one(), node2));
            self.shortest_explanation_memo
                .insert((node2, node1), (BigUint::one(), node1));
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
                    if let Justification::Rule(r) = neighbor.justification {
                        equalities.push((neighbor.current, neighbor.next, r));
                    }
                }
            }
        }
        equalities
    }

    pub(crate) fn with_nodes<'a>(&'a mut self, nodes: &'a [L]) -> ExplainNodes<'a, L> {
        ExplainNodes {
            explain: self,
            nodes,
        }
    }
}

impl<'a, L: Language> Deref for ExplainNodes<'a, L> {
    type Target = Explain<L>;

    fn deref(&self) -> &Self::Target {
        self.explain
    }
}

impl<'a, L: Language> DerefMut for ExplainNodes<'a, L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.explain
    }
}

impl<'x, L: Language> ExplainNodes<'x, L> {
    pub(crate) fn node(&self, node_id: Id) -> &L {
        &self.nodes[usize::from(node_id)]
    }
    fn node_to_explanation(
        &self,
        node_id: Id,
        cache: &mut NodeExplanationCache<L>,
    ) -> Rc<TreeTerm<L>> {
        if let Some(existing) = cache.get(&node_id) {
            existing.clone()
        } else {
            let node = self.node(node_id).clone();
            let children = node.fold(vec![], |mut sofar, child| {
                sofar.push(vec![self.node_to_explanation(child, cache)]);
                sofar
            });
            let res = Rc::new(TreeTerm::new(node, children));
            cache.insert(node_id, res.clone());
            res
        }
    }

    fn node_to_flat_explanation(&self, node_id: Id) -> FlatTerm<L> {
        let node = self.node(node_id).clone();
        let children = node.fold(vec![], |mut sofar, child| {
            sofar.push(self.node_to_flat_explanation(child));
            sofar
        });
        FlatTerm::new(node, children)
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

    pub(crate) fn explain_equivalence<N: Analysis<L>>(
        &mut self,
        left: Id,
        right: Id,
        unionfind: &mut UnionFind,
        classes: &HashMap<Id, EClass<L, N::Data>>,
    ) -> Explanation<L> {
        if self.optimize_explanation_lengths {
            self.calculate_shortest_explanations::<N>(left, right, classes, unionfind);
        }

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
        Connection {
            justification: Justification::Congruence,
            current,
            next,
            is_rewrite_forward: true,
        }
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
            let mut connection = if graphnode.parent_connection.next == existance {
                graphnode.parent_connection.clone()
            } else {
                existance_node.parent_connection.clone()
            };

            if graphnode.parent_connection.next == existance {
                connection.is_rewrite_forward = !connection.is_rewrite_forward;
                std::mem::swap(&mut connection.next, &mut connection.current);
            }

            let adj = self.explain_adjacent(connection, cache, enode_cache, false);
            let mut exp = self.explain_enode_existance(existance, adj, cache, enode_cache);
            exp.push(rest_of_proof);
            return exp;
        }

        // case 3)
        let mut new_rest_of_proof = (*self.node_to_explanation(existance, enode_cache)).clone();
        let mut index_of_child = 0;
        let mut found = false;
        self.node(existance).for_each(|child| {
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
            let mut connection = connection.clone();
            if i >= left_connections.len() {
                connection.is_rewrite_forward = !connection.is_rewrite_forward;
                std::mem::swap(&mut connection.next, &mut connection.current);
            }

            proof.push(self.explain_adjacent(
                connection,
                cache,
                node_explanation_cache,
                use_unoptimized,
            ));
        }
        proof
    }

    fn explain_adjacent(
        &self,
        connection: Connection,
        cache: &mut ExplainCache<L>,
        node_explanation_cache: &mut NodeExplanationCache<L>,
        use_unoptimized: bool,
    ) -> Rc<TreeTerm<L>> {
        let fingerprint = (connection.current, connection.next);

        if let Some(answer) = cache.get(&fingerprint) {
            return answer.clone();
        }

        let term = match connection.justification {
            Justification::Rule(name) => {
                let mut rewritten =
                    (*self.node_to_explanation(connection.next, node_explanation_cache)).clone();
                if connection.is_rewrite_forward {
                    rewritten.forward_rule = Some(name);
                } else {
                    rewritten.backward_rule = Some(name);
                }

                rewritten.current = connection.next;
                rewritten.last = connection.current;

                Rc::new(rewritten)
            }
            Justification::Congruence => {
                // add the children proofs to the last explanation
                let current_node = self.node(connection.current);
                let next_node = self.node(connection.next);
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

        while let Some(current) = todo.pop() {
            if enodes.insert(current) {
                for neighbor in &self.explainfind[usize::from(current)].neighbors {
                    todo.push(neighbor.next);
                }
            }
        }
        enodes
    }

    fn add_tree_depths(&self, node: Id, depths: &mut HashMap<Id, ProofCost>) -> ProofCost {
        if depths.get(&node).is_none() {
            let parent = self.parent(node);
            let depth = if parent == node {
                BigUint::zero()
            } else {
                self.add_tree_depths(parent, depths) + 1_u32
            };

            depths.insert(node, depth);
        }

        depths.get(&node).unwrap().clone()
    }

    fn calculate_tree_depths(&self) -> HashMap<Id, ProofCost> {
        let mut depths = HashMap::default();
        for i in 0..self.explainfind.len() {
            self.add_tree_depths(Id::from(i), &mut depths);
        }
        depths
    }

    fn replace_distance(&mut self, current: Id, next: Id, right: Id, distance: ProofCost) {
        self.shortest_explanation_memo
            .insert((current, right), (distance, next));
    }

    fn populate_path_length(
        &mut self,
        right: Id,
        left_connections: &[Connection],
        distance_memo: &mut DistanceMemo,
    ) {
        self.shortest_explanation_memo
            .insert((right, right), (BigUint::zero(), right));
        for connection in left_connections.iter().rev() {
            let next = connection.next;
            let current = connection.current;
            let next_cost = self
                .shortest_explanation_memo
                .get(&(next, right))
                .unwrap()
                .0
                .clone();
            let dist = self.connection_distance(connection, distance_memo);
            self.replace_distance(current, next, right, next_cost + dist);
        }
    }

    fn distance_between(
        &mut self,
        left: Id,
        right: Id,
        distance_memo: &mut DistanceMemo,
    ) -> ProofCost {
        if left == right {
            return BigUint::zero();
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
        b + c - (a << 1)

        //assert_eq!(dist+1, Explanation::new(self.explain_enodes(left, right, &mut Default::default())).make_flat_explanation().len());
    }

    fn congruence_distance(
        &mut self,
        current: Id,
        next: Id,
        distance_memo: &mut DistanceMemo,
    ) -> ProofCost {
        let current_node = self.node(current).clone();
        let next_node = self.node(next).clone();
        let mut cost: ProofCost = BigUint::zero();
        for (left_child, right_child) in current_node
            .children()
            .iter()
            .zip(next_node.children().iter())
        {
            cost += self.distance_between(*left_child, *right_child, distance_memo);
        }
        cost
    }

    fn connection_distance(
        &mut self,
        connection: &Connection,
        distance_memo: &mut DistanceMemo,
    ) -> ProofCost {
        match connection.justification {
            Justification::Congruence => {
                self.congruence_distance(connection.current, connection.next, distance_memo)
            }
            Justification::Rule(_) => BigUint::one(),
        }
    }

    fn calculate_parent_distance(
        &mut self,
        enode: Id,
        ancestor: Id,
        distance_memo: &mut DistanceMemo,
    ) -> ProofCost {
        loop {
            let parent = distance_memo.parent_distance[usize::from(enode)].0;
            let dist = distance_memo.parent_distance[usize::from(enode)].1.clone();
            if self.parent(parent) == parent {
                break;
            }

            let parent_parent = distance_memo.parent_distance[usize::from(parent)].0;
            if parent_parent != parent {
                let new_dist = dist + distance_memo.parent_distance[usize::from(parent)].1.clone();
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
                    Justification::Rule(_) => BigUint::one(),
                };
                distance_memo.parent_distance[usize::from(parent)] = (self.parent(parent), cost);
            }
        }

        //assert_eq!(distance_memo.parent_distance[usize::from(enode)].1+1,
        //Explanation::new(self.explain_enodes(enode, distance_memo.parent_distance[usize::from(enode)].0, &mut Default::default())).make_flat_explanation().len());

        distance_memo.parent_distance[usize::from(enode)].1.clone()
    }

    fn find_congruence_neighbors<N: Analysis<L>>(
        &self,
        classes: &HashMap<Id, EClass<L, N::Data>>,
        congruence_neighbors: &mut [Vec<Id>],
        unionfind: &UnionFind,
    ) {
        let mut counter = 0;
        // add the normal congruence edges first
        for node in &self.explainfind {
            if let Justification::Congruence = node.parent_connection.justification {
                let current = node.parent_connection.current;
                let next = node.parent_connection.next;
                congruence_neighbors[usize::from(current)].push(next);
                congruence_neighbors[usize::from(next)].push(current);
                counter += 1;
            }
        }

        'outer: for eclass in classes.keys() {
            let enodes = self.find_all_enodes(*eclass);
            // find all congruence nodes
            let mut cannon_enodes: HashMap<L, Vec<Id>> = Default::default();
            for enode in &enodes {
                let cannon = self
                    .node(*enode)
                    .clone()
                    .map_children(|child| unionfind.find(child));
                if let Some(others) = cannon_enodes.get_mut(&cannon) {
                    for other in others.iter() {
                        congruence_neighbors[usize::from(*enode)].push(*other);
                        congruence_neighbors[usize::from(*other)].push(*enode);
                        counter += 1;
                    }
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
        end: Id,
        congruence_neighbors: &[Vec<Id>],
        distance_memo: &mut DistanceMemo,
    ) -> Option<(Vec<Connection>, Vec<Connection>)> {
        let mut todo = BinaryHeap::new();
        todo.push(HeapState {
            cost: BigUint::zero(),
            item: Connection {
                current: start,
                next: start,
                justification: Justification::Congruence,
                is_rewrite_forward: true,
            },
        });

        let mut last = HashMap::default();
        let mut path_cost = HashMap::default();

        'outer: loop {
            if todo.is_empty() {
                break 'outer;
            }
            let state = todo.pop().unwrap();
            let connection = state.item;
            let cost_so_far = state.cost.clone();
            let current = connection.next;

            if last.get(&current).is_some() {
                continue 'outer;
            } else {
                last.insert(current, connection);
                path_cost.insert(current, cost_so_far.clone());
            }

            if current == end {
                break;
            }

            for neighbor in &self.explainfind[usize::from(current)].neighbors {
                if let Justification::Rule(_) = neighbor.justification {
                    let neighbor_cost = cost_so_far.clone() + 1_u32;
                    todo.push(HeapState {
                        item: neighbor.clone(),
                        cost: neighbor_cost,
                    });
                }
            }

            for other in congruence_neighbors[usize::from(current)].iter() {
                let next = other;
                let distance = self.congruence_distance(current, *next, distance_memo);
                let next_cost = cost_so_far.clone() + distance;
                todo.push(HeapState {
                    item: Connection {
                        current,
                        next: *next,
                        justification: Justification::Congruence,
                        is_rewrite_forward: true,
                    },
                    cost: next_cost,
                });
            }
        }

        let total_cost = path_cost.get(&end);

        let left_connections;
        let mut right_connections = vec![];

        // we would like to assert that we found a path better than the normal one
        // but since proof sizes are saturated this is not true
        /*let dist = self.distance_between(start, end, distance_memo);
        if *total_cost.unwrap() > dist {
            panic!(
                "Found cost greater than baseline {} vs {}",
                total_cost.unwrap(),
                dist
            );
        }*/
        if *total_cost.unwrap() >= self.distance_between(start, end, distance_memo) {
            let (a_left_connections, a_right_connections) = self.get_path_unoptimized(start, end);
            left_connections = a_left_connections;
            right_connections = a_right_connections;
        } else {
            let mut current = end;
            let mut connections = vec![];
            while current != start {
                let prev = last.get(&current);
                if let Some(prev_connection) = prev {
                    connections.push(prev_connection.clone());
                    current = prev_connection.current;
                } else {
                    break;
                }
            }
            connections.reverse();
            self.populate_path_length(end, &connections, distance_memo);
            left_connections = connections;
        }

        Some((left_connections, right_connections))
    }

    fn greedy_short_explanations(
        &mut self,
        start: Id,
        end: Id,
        congruence_neighbors: &[Vec<Id>],
        distance_memo: &mut DistanceMemo,
        mut fuel: usize,
    ) {
        let mut todo_congruence = VecDeque::new();
        todo_congruence.push_back((start, end));

        while !todo_congruence.is_empty() {
            let (start, end) = todo_congruence.pop_front().unwrap();
            let eclass_size = self.find_all_enodes(start).len();
            if fuel < eclass_size {
                continue;
            }
            fuel = fuel.saturating_sub(eclass_size);

            let (left_connections, right_connections) = self
                .shortest_path_modulo_congruence(start, end, congruence_neighbors, distance_memo)
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
                    let current_node = self.node(current).clone();
                    let next_node = self.node(next).clone();
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

    #[allow(clippy::too_many_arguments)]
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
                if black_set.contains(other) {
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
        congruence_neighbors: &[Vec<Id>],
    ) -> HashMap<(Id, Id), Id> {
        let mut common_ancestor_queries = HashMap::default();
        for (s_int, others) in congruence_neighbors.iter().enumerate() {
            let start = &Id::from(s_int);
            for other in others {
                for (left, right) in self
                    .node(*start)
                    .children()
                    .iter()
                    .zip(self.node(*other).children().iter())
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

    fn calculate_shortest_explanations<N: Analysis<L>>(
        &mut self,
        start: Id,
        end: Id,
        classes: &HashMap<Id, EClass<L, N::Data>>,
        unionfind: &UnionFind,
    ) {
        let mut congruence_neighbors = vec![vec![]; self.explainfind.len()];
        self.find_congruence_neighbors::<N>(classes, &mut congruence_neighbors, unionfind);
        let mut parent_distance = vec![(Id::from(0), BigUint::zero()); self.explainfind.len()];
        for (i, entry) in parent_distance.iter_mut().enumerate() {
            entry.0 = Id::from(i);
        }

        let mut distance_memo = DistanceMemo {
            parent_distance,
            common_ancestor: self.calculate_common_ancestor::<N>(classes, &congruence_neighbors),
            tree_depth: self.calculate_tree_depths(),
        };

        let fuel = GREEDY_NUM_ITERS * self.explainfind.len();
        self.greedy_short_explanations(start, end, &congruence_neighbors, &mut distance_memo, fuel);
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

        assert_eq!(egraph.add_expr(&fa), egraph.add_expr(&fb));
        assert_eq!(
            egraph
                .explain_equivalence(&fa, &fb)
                .get_flat_strings()
                .len(),
            4
        );
        assert_eq!(
            egraph
                .explain_equivalence(&fa, &fb)
                .get_flat_strings()
                .len(),
            4
        );
        assert_eq!(
            egraph
                .explain_equivalence(&fa, &fb)
                .get_flat_strings()
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

        egraph = egraph.without_explanation_length_optimization();
        assert_eq!(
            egraph
                .explain_equivalence(&fa, &fb)
                .get_flat_strings()
                .len(),
            4
        );
        egraph = egraph.with_explanation_length_optimization();
        assert_eq!(
            egraph
                .explain_equivalence(&fa, &fb)
                .get_flat_strings()
                .len(),
            3
        );

        assert_eq!(
            egraph
                .explain_equivalence(&fa, &fb)
                .get_flat_strings()
                .len(),
            3
        );

        egraph.dot().to_dot("target/foo.dot").unwrap();
    }

    #[test]
    fn simple_explain_exists() {
        //! Same as previous test, but now I want to make a rewrite add some term and see it exists in
        //! more then one step
        use crate::SymbolLang;
        init_logger();

        let rws: Vec<Rewrite<SymbolLang, ()>> =
            [rewrite!("makeb"; "a" => "b"), rewrite!("makec"; "b" => "c")].to_vec();
        let mut egraph = Runner::default()
            .with_explanations_enabled()
            .without_explanation_length_optimization()
            .with_expr(&"a".parse().unwrap())
            .run(&rws)
            .egraph;
        egraph.rebuild();
        let _a: Symbol = "a".parse().unwrap();
        let _b: Symbol = "b".parse().unwrap();
        let _c: Symbol = "c".parse().unwrap();
        let mut exp = egraph.explain_existance(&"c".parse().unwrap());
        println!("{:?}", exp.make_flat_explanation());
        assert_eq!(
            exp.make_flat_explanation().len(),
            3,
            "Expected 3 steps, got {:?}",
            exp.make_flat_explanation()
        );
    }
}

#[test]
fn simple_explain_union_trusted() {
    use crate::{EGraph, SymbolLang};
    crate::init_logger();
    let mut egraph = EGraph::new(()).with_explanations_enabled();

    let a = egraph.add_uncanonical(SymbolLang::leaf("a"));
    let b = egraph.add_uncanonical(SymbolLang::leaf("b"));
    let c = egraph.add_uncanonical(SymbolLang::leaf("c"));
    let d = egraph.add_uncanonical(SymbolLang::leaf("d"));
    egraph.union_trusted(a, b, "a=b");
    egraph.rebuild();
    let fa = egraph.add_uncanonical(SymbolLang::new("f", vec![a]));
    let fb = egraph.add_uncanonical(SymbolLang::new("f", vec![b]));
    egraph.union_trusted(c, fa, "c=fa");
    egraph.union_trusted(d, fb, "d=fb");
    egraph.rebuild();
    let mut exp = egraph.explain_equivalence(&"c".parse().unwrap(), &"d".parse().unwrap());
    assert_eq!(exp.make_flat_explanation().len(), 4)
}
