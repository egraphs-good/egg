use crate::Symbol;
use crate::{
    util::pretty_print, Analysis, EClass, ENodeOrVar, HashMap, HashSet, Id, Language, PatternAst,
    RecExpr, Rewrite, Subst, UnionFind, Var,
};
use std::fmt::{self, Debug, Display, Formatter};
use std::rc::Rc;

use priority_queue::PriorityQueue;
use symbolic_expressions::Sexp;

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
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct Explain<L: Language> {
    explainfind: Vec<ExplainNode<L>>,
    uncanon_memo: HashMap<L, Id>,
    // For a given pair of enodes in the same eclass,
    // stores the length of the shortest explanation
    // and the Id of the neighbor for retrieving
    // the explanation.
    shortest_explanation_memo: HashMap<(Id, Id), (usize, Id)>,
}

struct DistanceMemo {
    parent_distance: Vec<(Id, usize)>,
    common_ancestor: HashMap<(Id, Id), Id>,
}

/// Explanation trees are the compact representation showing
/// how one term can be rewritten to another.
///
/// Each [`TreeTerm`] has child [`TreeExplanation`]
/// justifying a transformation from the initial child to the final child term.
/// Children [`TreeTerm`] can be shared, thus re-using explanations.
/// This sharing can be checked via Rc pointer equality.
///
/// See [`TreeTerm`] for more deatils on how to
/// interpret each term.
pub type TreeExplanation<L> = Vec<Rc<TreeTerm<L>>>;

/// FlatExplanation are the simpler, expanded representation
/// showing one term being rewritten to another.
/// Each step contains a full `FlatTerm`. Each flat term
/// is connected to the previous by exactly one rewrite.
///
/// See [`FlatTerm`] for more details on how to find this rewrite.
pub type FlatExplanation<L> = Vec<FlatTerm<L>>;

// given two adjacent nodes and the direction of the proof
type ExplainCache<L> = HashMap<(Id, Id), Rc<TreeTerm<L>>>;

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

impl<L: Language + Display> Display for Explanation<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.get_sexp().to_string();
        f.write_str(&s)
    }
}

impl<L: Language + Display> Explanation<L> {
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
                if &current.rewrite(lhs, rhs) != next {
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
/// in each [`child_proofs`](TreeTerm::child_proofs) recursivly.
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
    /// A rule rewritting this TreeTerm's initial term back to the last TreeTerm's final term.
    pub backward_rule: Option<Symbol>,
    /// A rule rewriting the last TreeTerm's final term to this TreeTerm's initial term.
    pub forward_rule: Option<Symbol>,
    /// A list of child proofs, each transforming the initial term to the final term for that child.
    pub child_proofs: Vec<TreeExplanation<L>>,
}

impl<L: Language> TreeTerm<L> {
    /// Construct a new TreeTerm given its node and child_proofs.
    pub fn new(node: L, child_proofs: Vec<TreeExplanation<L>>) -> TreeTerm<L> {
        TreeTerm {
            node,
            backward_rule: None,
            forward_rule: None,
            child_proofs,
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

impl<L: Language + Display> Display for FlatTerm<L> {
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
            if !child1.eq(&child2) {
                return false;
            }
        }
        true
    }
}

impl<L: Language> FlatTerm<L> {
    fn remove_rewrites(&self) -> FlatTerm<L> {
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

impl<L: Language + Display> FlatTerm<L> {
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
}

impl<L: Language + Display> Display for TreeTerm<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut buf = String::new();
        let width = 80;
        pretty_print(&mut buf, &self.get_sexp(), width, 1).unwrap();
        write!(f, "{}", buf)
    }
}

impl<L: Language + Display> TreeTerm<L> {
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
        let lhs_nodes = lhs.as_ref().as_ref();
        let rhs_nodes = rhs.as_ref().as_ref();
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
                bindings.insert(*var, self);
            }
            ENodeOrVar::ENode(node) => {
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

impl<L: Language> Explain<L> {
    fn node_to_explanation(&self, node_id: Id) -> TreeTerm<L> {
        let node = self.explainfind[usize::from(node_id)].node.clone();
        let children = node.fold(vec![], |mut sofar, child| {
            sofar.push(vec![Rc::new(self.node_to_explanation(child))]);
            sofar
        });
        TreeTerm::new(node, children)
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

    pub fn add(&mut self, node: L, set: Id) -> Id {
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
        });
        set
    }

    pub(crate) fn add_expr(
        &mut self,
        expr: &RecExpr<L>,
        memo: &HashMap<L, Id>,
        unionfind: &mut UnionFind,
    ) -> Id {
        let nodes: Vec<ENodeOrVar<L>> = expr
            .as_ref()
            .iter()
            .map(|node| ENodeOrVar::ENode(node.clone()))
            .collect();
        let pattern = PatternAst::from(nodes);
        self.add_match(&pattern, &Default::default(), memo, unionfind)
    }

    // add_match uses the memo in order to re-discover matches
    // given a substitution.
    // This requires that congruence has been restored and the memo is up to date.
    pub(crate) fn add_match(
        &mut self,
        pattern: &PatternAst<L>,
        subst: &Subst,
        memo: &HashMap<L, Id>,
        unionfind: &mut UnionFind,
    ) -> Id {
        let nodes = pattern.as_ref().as_ref();
        let mut new_ids = Vec::with_capacity(nodes.len());
        let mut match_ids = Vec::with_capacity(nodes.len());
        for node in nodes {
            match node {
                ENodeOrVar::Var(var) => {
                    let bottom_id = unionfind.find(subst[*var]);
                    new_ids.push(unionfind.find(bottom_id));
                    match_ids.push(bottom_id);
                }
                ENodeOrVar::ENode(pattern_node) => {
                    let node = pattern_node
                        .clone()
                        .map_children(|i| new_ids[usize::from(i)]);
                    let new_congruent_node = pattern_node
                        .clone()
                        .map_children(|i| match_ids[usize::from(i)]);
                    if let Some(existing_id) = self.uncanon_memo.get(&new_congruent_node) {
                        new_ids.push(unionfind.find(*existing_id));
                        match_ids.push(*existing_id);
                    } else {
                        let congruent_id = *memo.get(&node).unwrap_or_else(|| {
                            panic!("Internal error! Pattern did not exist for substitution.");
                        });

                        let congruent_class = unionfind.find(congruent_id);

                        new_ids.push(congruent_class);
                        assert!(
                            node == self.explainfind[usize::from(congruent_id)]
                                .node
                                .clone()
                                .map_children(|id| unionfind.find(id))
                        );

                        let new_congruent_id = self.add(new_congruent_node, unionfind.make_set());
                        match_ids.push(new_congruent_id);
                        // make the congruent_id we found the leader
                        unionfind.union(congruent_class, new_congruent_id);
                        self.union(new_congruent_id, congruent_id, Justification::Congruence);
                    }
                }
            }
        }

        let last_id = *match_ids.last().unwrap();
        last_id
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

    pub(crate) fn union(&mut self, node1: Id, node2: Id, justification: Justification) {
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

    pub(crate) fn explain_matches<N: Analysis<L>>(
        &mut self,
        left: &RecExpr<L>,
        right: &PatternAst<L>,
        subst: &Subst,
        memo: &HashMap<L, Id>,
        unionfind: &mut UnionFind,
        classes: &HashMap<Id, EClass<L, N::Data>>,
        optimize_iters: usize,
        greedy_search: bool,
    ) -> Explanation<L> {
        let left_added = self.add_expr(left, memo, unionfind);
        let right_added = self.add_match(right, &subst, memo, unionfind);
        self.calculate_shortest_explanations::<N>(
            left_added,
            right_added,
            classes,
            &unionfind,
            optimize_iters,
            greedy_search,
        );
        let mut cache = Default::default();
        let res = Explanation::new(self.explain_enodes(left_added, right_added, &mut cache));
        res
    }

    pub(crate) fn explain_equivalence<N: Analysis<L>>(
        &mut self,
        left: &RecExpr<L>,
        right: &RecExpr<L>,
        memo: &HashMap<L, Id>,
        unionfind: &mut UnionFind,
        classes: &HashMap<Id, EClass<L, N::Data>>,
        optimize_iters: usize,
        greedy_search: bool,
    ) -> Explanation<L> {
        let left_added = self.add_expr(left, memo, unionfind);
        let right_added = self.add_expr(right, memo, unionfind);
        self.calculate_shortest_explanations::<N>(
            left_added,
            right_added,
            classes,
            &unionfind,
            optimize_iters,
            greedy_search,
        );
        let mut cache = Default::default();
        Explanation::new(self.explain_enodes(left_added, right_added, &mut cache))
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

    fn get_path(&self, mut left: Id, right: Id) -> (Vec<Connection>, Vec<Connection>) {
        let mut left_connections = vec![];
        loop {
            if left == right {
                return (left_connections, vec![]);
            }
            if let Some((_, next)) = self.shortest_explanation_memo.get(&(left, right)) {
                break;
                let mut found = false;
                for neighbor in &self.explainfind[usize::from(left)].neighbors {
                    if neighbor.next == *next {
                        if let Justification::Rule(_) = neighbor.justification {
                            left_connections.push(neighbor.clone());
                            found = true;
                            break;
                        }
                    }
                }
                if !found {
                    left_connections.push(Connection {
                        justification: Justification::Congruence,
                        current: left,
                        next: *next,
                        is_rewrite_forward: true,
                    });
                }
                left = *next;
            } else {
                break;
            }
        }

        let (restleft, right_connections) = self.get_path_unoptimized(left, right);
        left_connections.extend(restleft);
        (left_connections, right_connections)
    }

    fn explain_enodes(
        &self,
        left: Id,
        right: Id,
        cache: &mut ExplainCache<L>,
    ) -> TreeExplanation<L> {
        let mut proof = vec![Rc::new(self.node_to_explanation(left))];

        let (left_connections, right_connections) = self.get_path(left, right);

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
    ) -> Rc<TreeTerm<L>> {
        let fingerprint = (current, next);

        if let Some(answer) = cache.get(&fingerprint) {
            return answer.clone();
        }

        let term = match justification {
            Justification::Rule(name) => {
                let mut rewritten = self.node_to_explanation(next);
                if rule_direction {
                    rewritten.forward_rule = Some(*name);
                } else {
                    rewritten.backward_rule = Some(*name);
                }

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
                    subproofs.push(self.explain_enodes(*left_child, *right_child, cache));
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

    // Run Floyd-Warshall to find all pairs shortest paths for this eclass.
    // When child lengths are absent, they are considered
    // to be the largest usize length.
    fn shortest_explanations_eclass(
        &mut self,
        eclass: Id,
        unionfind: &UnionFind,
        congruent_nodes: &Vec<Vec<Id>>,
        distance_memo: &mut DistanceMemo,
    ) -> bool {
        let enodes = self.find_all_enodes(eclass);
        let mut did_anything = false;

        // distance to congruent nodes is the sum of distances between children
        for enode in &enodes {
            for other in congruent_nodes[usize::from(*enode)].iter() {
                let mut cost = 0;
                let current_node = &self.explainfind[usize::from(*enode)].node;
                let next_node = &self.explainfind[usize::from(*other)].node;
                for (left_child, right_child) in current_node
                    .children()
                    .iter()
                    .zip(next_node.children().iter())
                {
                    if let Some((child_cost, _)) = self
                        .shortest_explanation_memo
                        .get(&(*left_child, *right_child))
                    {
                        cost += *child_cost;
                    } else {
                        cost = usize::MAX;
                        break;
                    }
                }

                let old = self.cache_distance_between(*enode, *other, distance_memo);

                if cost < old.0 {
                    self.shortest_explanation_memo
                        .insert((*enode, *other), (cost, *other));
                    self.shortest_explanation_memo
                        .insert((*other, *enode), (cost, *enode));
                    did_anything = true;
                }
            }
        }

        // updates shortest paths based on all possible intermediates
        for intermediate in &enodes {
            for start in &enodes {
                for end in &enodes {
                    let start_to_intermediate =
                        match self.shortest_explanation_memo.get(&(*start, *intermediate)) {
                            Some(pair) => pair.clone(),
                            None => continue,
                        };
                    let intermediate_to_end =
                        match self.shortest_explanation_memo.get(&(*intermediate, *end)) {
                            Some((v, _)) => *v,
                            None => continue,
                        };
                    let old = self.cache_distance_between(*start, *end, distance_memo);
                    let new = start_to_intermediate.0 + intermediate_to_end;
                    if new < old.0 {
                        self.shortest_explanation_memo
                            .insert((*start, *end), (new, start_to_intermediate.1));
                        did_anything = true;
                    }
                }
            }
        }

        did_anything
    }

    fn replace_distance(&mut self, current: Id, next: Id, right: Id, distance: usize) {
        self.shortest_explanation_memo.insert(
            (current, right),
            (
                distance,
                next,
            ),
        );
    }

    fn populate_path_length(
        &mut self,
        right: Id,
        left_connections: &Vec<Connection>,
        distance_memo: &mut DistanceMemo,
    ) {
        self.shortest_explanation_memo
            .insert((right, right), (0, right));
        for connection in left_connections.iter().rev() {
            let next = connection.next;
            let current = connection.current;
            let next_cost = self
                .shortest_explanation_memo
                .get(&(next, right))
                .unwrap()
                .0;
            let dist = self.distance_between(current, next, distance_memo).0;
            self.replace_distance(current, next, right, next_cost+dist);
        }
    }


    fn cache_distance_between(&mut self, left: Id, right: Id, distance_memo: &mut DistanceMemo) -> (usize, Id) {
        if let Some((dist, next)) = self.shortest_explanation_memo.get(&(left, right)) {
            (*dist, *next)
        } else {
            self.distance_between(left, right, distance_memo)
        }
    }

    fn distance_between(&mut self, left: Id, right: Id, distance_memo: &mut DistanceMemo) -> (usize, Id) {
        if left == right {
            return (0, left);
        }
        let ancestor = *distance_memo.common_ancestor.get(&(left, right)).unwrap();
        // calculate edges until you are past the ancestor
        self.calculate_parent_distance(left, ancestor, distance_memo);
        self.calculate_parent_distance(right, ancestor, distance_memo);

        // now all three share an ancestor
        let a = self.calculate_parent_distance(ancestor, Id::from(usize::MAX), distance_memo); 
        let b = self.calculate_parent_distance(left, Id::from(usize::MAX), distance_memo);
        let c = self.calculate_parent_distance(right, Id::from(usize::MAX), distance_memo);

        assert!(distance_memo.parent_distance[usize::from(ancestor)].0 ==
        distance_memo.parent_distance[usize::from(left)].0);
        assert!(distance_memo.parent_distance[usize::from(ancestor)].0 ==
        distance_memo.parent_distance[usize::from(right)].0);

        // calculate distance to find upper bound
        let dist = b + c - 2*a;

        let next = self.parent(left);
        return (dist, next);
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
                if parent == ancestor {
                    break;
                }
                let higher = *distance_memo.common_ancestor.get(&(parent, ancestor)).unwrap();
                if higher != ancestor {
                    assert!(higher == parent);
                    break;
                }

                // find the length of one parent connection
                let connection = &self.explainfind[usize::from(parent)].parent_connection;
                let current = connection.current;
                let next = connection.next;
                let cost = 
                if let Some((cost, _)) = self.shortest_explanation_memo.get(&(current, next)) {
                    *cost
                } else {
                    match connection.justification {
                        Justification::Congruence => {
                            let current_node = self.explainfind[usize::from(current)]
                                .node
                                .clone();
                            let next_node = self.explainfind[usize::from(next)].node.clone();
                            let mut cost = 0;
                            for (left_child, right_child) in current_node
                                .children()
                                .iter()
                                .zip(next_node.children().iter())
                            {
                                cost +=
                                    self.distance_between(*left_child, *right_child, distance_memo).0;
                            }
                            cost
                        }
                        Justification::Rule(_) => 1,
                    }
                };
                distance_memo.parent_distance[usize::from(parent)] = (self.parent(parent), cost);
            }
        }

        distance_memo.parent_distance[usize::from(enode)].1
    }

    fn find_congruence_neighbors<N: Analysis<L>>(
        &self,
        classes: &HashMap<Id, EClass<L, N::Data>>,
        congruence_neighbors: &mut Vec<Vec<Id>>,
        unionfind: &UnionFind,
    ) {
        for eclass in classes.keys() {
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
                    others.push(*enode);
                } else {
                    cannon_enodes.insert(cannon, vec![*enode]);
                }
            }
        }
    }

    fn greedy_short_explanations(
        &mut self,
        start: Id,
        end: Id,
        congruence_neighbors: &Vec<Vec<Id>>,
        unionfind: &UnionFind,
        distance_memo: &mut DistanceMemo,
        eclass_seen_memo: &mut HashSet<Id>,
        depth: usize
    ) -> usize {
        if !eclass_seen_memo.insert(unionfind.find(start)) {
            return self.cache_distance_between(start, end, distance_memo).0
        }

        let mut todo = PriorityQueue::new();
        todo.push(
            Connection {
                current: start,
                next: start,
                justification: Justification::Congruence,
                is_rewrite_forward: true,
            },
            usize::MAX,
        );

        let mut last = HashMap::default();
        let total_cost;

        loop {
            assert!(todo.len() > 0);
            let (connection, cost_so_far) = todo.pop().unwrap();
            let current = connection.next;

            if let Some(_) = last.get(&current) {
                continue;
            } else {
                last.insert(current, connection);
            }

            if current == end {
                total_cost = usize::MAX - cost_so_far;
                break;
            }

            for neighbor in &self.explainfind[usize::from(current)].neighbors {
                if let Justification::Rule(_) = neighbor.justification {
                    let neighbor_cost = (usize::MAX - cost_so_far) + 1;
                    todo.push(neighbor.clone(), usize::MAX - neighbor_cost);
                }
            }

            for other in congruence_neighbors[usize::from(current)].iter() {
                let distance = if depth > 0 {
                    self.greedy_short_explanations(current, *other, congruence_neighbors, unionfind, distance_memo, eclass_seen_memo, depth.saturating_sub(1))
                } else {
                    self.distance_between(current, *other, distance_memo).0
                };
                let other_cost = (usize::MAX - cost_so_far)
                    + distance;
                todo.push(
                    Connection {
                        current: current,
                        next: *other,
                        justification: Justification::Congruence,
                        is_rewrite_forward: true,
                    },
                    usize::MAX - other_cost,
                );
            }
        }

        let mut left_connections = vec![];
        let mut right_connections = vec![];
        // when we found an equivalent path, avoid cycles by taking the normal route
        let dist = self.distance_between(start, end, distance_memo).0;
        assert!(total_cost <= dist);
        if total_cost == dist {
            let (a_left_connections, a_right_connections) = self.get_path_unoptimized(start, end);
            left_connections = a_left_connections;
            right_connections = a_right_connections;
        } else {
            let mut current = end;
            while current != start {
                let prev_connection = last.get(&current).unwrap();
                left_connections.push(prev_connection.clone());
                current = prev_connection.current;
            }
            left_connections.reverse();
            self.populate_path_length(end, &left_connections, distance_memo);
        }

        let mut greedy_cost = 0;

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
                let mut cost = 0;
                let current_node = self.explainfind[usize::from(current)].node.clone();
                let next_node = self.explainfind[usize::from(next)].node.clone();
                for (left_child, right_child) in current_node
                    .children()
                    .iter()
                    .zip(next_node.children().iter())
                {
                    cost += self.greedy_short_explanations(
                        *left_child,
                        *right_child,
                        congruence_neighbors,
                        unionfind,
                        distance_memo,
                        eclass_seen_memo,
                        depth.saturating_sub(1),
                    );
                }
                greedy_cost += cost;
            } else {
                greedy_cost += 1;
            }
        }

        greedy_cost
    }

    fn tarjan_ocla(
        &self,
        enode: Id,
        children: &HashMap<Id, Vec<Id>>,
        black_set: &mut HashSet<Id>,
        unionfind: &mut UnionFind,
        ancestor: &mut Vec<Id>,
        common_ancestor: &mut HashMap<(Id, Id), Id>,
    ) {
        ancestor[usize::from(enode)] = enode;
        for child in children[&enode].iter() {
            self.tarjan_ocla(*child, children, black_set, unionfind, ancestor, common_ancestor);
            unionfind.union(enode, *child);
            ancestor[usize::from(unionfind.find(enode))] = enode;
        }

        black_set.insert(enode);
        for other in black_set.iter() {
            let ancestor = ancestor[usize::from(unionfind.find(*other))];
            common_ancestor.insert((enode, *other), ancestor);
            common_ancestor.insert((*other, enode), ancestor);
        }
    }

    fn parent(&self, enode: Id) -> Id {
        self.explainfind[usize::from(enode)].parent_connection.next
    }

    fn calculate_common_ancestor<N: Analysis<L>>(
        &self,
        classes: &HashMap<Id, EClass<L, N::Data>>,
    ) -> HashMap<(Id, Id), Id> {
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
            self.tarjan_ocla(parent, &children, &mut black_set, &mut unionfind, &mut ancestor, &mut common_ancestor);
        }

        println!("done with tarjan");
        common_ancestor
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
            common_ancestor: self.calculate_common_ancestor::<N>(classes),
        };

        if greedy_search {
            let mut eclass_seen_memo = HashSet::default();
            self.greedy_short_explanations(
                start,
                end,
                &congruence_neighbors,
                &unionfind,
                &mut distance_memo,
                &mut eclass_seen_memo,
                iters
            );
        } else {
            for _i in 0..iters {
                let mut did_something = false;
                for eclass in classes.keys() {
                    if self.shortest_explanations_eclass(*eclass, unionfind, &congruence_neighbors, &mut distance_memo)
                    {
                        did_something = true;
                    }
                }

                if !did_something {
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

        assert_eq!(egraph.explain_equivalence(&fa, &fb, 0, false).get_flat_sexps().len(), 4);
        assert_eq!(egraph.explain_equivalence(&fa, &fb, 100, false).get_flat_sexps().len(), 4);
        assert_eq!(egraph.explain_equivalence(&fa, &fb, 0, true).get_flat_sexps().len(), 4);

        egraph.union_instantiations(&"(f a)".parse().unwrap(), &"g".parse().unwrap(), &Default::default(), "fag".to_string());
        egraph.union_instantiations(&"g".parse().unwrap(), &"(f b)".parse().unwrap(), &Default::default(), "gfb".to_string());

        egraph.rebuild();

        assert_eq!(egraph.explain_equivalence(&fa, &fb, 0, false).get_flat_sexps().len(), 4);
        assert_eq!(egraph.explain_equivalence(&fa, &fb, 0, true).get_flat_sexps().len(), 3);
        assert_eq!(egraph.explain_equivalence(&fa, &fb, 100, false).get_flat_sexps().len(), 3);
        

        egraph.dot().to_dot("target/foo.dot").unwrap();
    }
}

