use crate::{
    util::pretty_print, Analysis, ENodeOrVar, HashMap, HashSet, Id, Language, PatternAst,
    RecExpr, Rewrite, Subst, UnionFind, Var,
};
use std::fmt::{self, Debug, Display, Formatter};
use std::rc::Rc;
use symbolic_expressions::Sexp;

#[derive(Debug, Clone)]
pub(crate) enum Justification {
    Rule(String),
    Congruence,
}

#[derive(Debug, Clone)]
struct ExplainNode<L: Language> {
    node: L,
    next: Id,
    current: Id,
    justification: Justification,
    is_rewrite_forward: bool,
}

#[derive(Debug, Clone)]
pub struct Explain<L: Language> {
    unionfind: UnionFind,
    explainfind: Vec<ExplainNode<L>>,
    // a map from updated enodes to their original enode ids
    pub memo: HashMap<L, Id>,
    uncanon_memo: HashMap<L, Id>,
}

pub type ExplanationTrees<L> = Vec<Rc<TreeTerm<L>>>;
// given two adjacent nodes and the direction of the proof
type ExplainCache<L> = HashMap<(Id, Id), Rc<TreeTerm<L>>>;


/** A data structure representing an explanation that two terms are equivalent.

There are two representations of explanations, each with
a corresponding string representation. The first is 
[`explanation_trees`], the compact representation where children can contain explanations.
The second is from `make_flat_explanation`, which flattens the tree
representation into a series of full terms.

See TODO for an explanation of the tree data structure and
TODO for an explanation of the flat representation.

[`explanation_trees`]: Explanation::explanation_trees
**/
pub struct Explanation<L: Language> {
    /// The tree representation of the explanation.
    pub explanation_trees: ExplanationTrees<L>,
    flat_explanation: Option<Vec<FlatTerm<L>>>,
}

impl<L: Language + Display> Display for Explanation<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.to_strings().join("\n");
        f.write_str(&s)
    }
}

impl<L: Language + Display> Explanation<L> {
    /// Output the flattened explanation as a string.
    pub fn to_flat_string(&mut self) -> String {
        self.to_flat_strings().join("\n")
    }

    /// Output each term in the explanation as a string.
    pub fn to_flat_strings(&mut self) -> Vec<String> {
        self.make_flat_explanation()
            .iter()
            .map(|e| e.to_string())
            .collect()
    }

    /// Output each explanation tree as a string.
    pub fn to_strings(&self) -> Vec<String> {
        self.explanation_trees
            .iter()
            .map(|e| e.to_string())
            .collect()
    }
}

impl<L: Language> Explanation<L> {
    /// Construct a new explanation given its tree representation.
    pub fn new(explanation_trees: ExplanationTrees<L>) -> Explanation<L> {
        Explanation {
            explanation_trees,
            flat_explanation: None,
        }
    }

    /// Construct the flat representation of the explanation and return it.
    pub fn make_flat_explanation<'a>(&'a mut self) -> &Vec<FlatTerm<L>> {
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
        table: &HashMap<String, &Rewrite<L, N>>,
        is_forward: bool,
    ) -> bool {
        if is_forward && next.forward_rule.is_some() {
            let rule_name = next.forward_rule.as_ref().unwrap();
            if let Some(rule) = table.get(rule_name) {
                println!("Checking {} forward", rule_name);
                Explanation::check_rewrite(current, next, rule)
            } else {
                // give up when the rule is not provided
                true
            }
        } else if !is_forward && next.backward_rule.is_some() {
            let rule_name = next.backward_rule.as_ref().unwrap();
            if let Some(rule) = table.get(rule_name) {
                println!("Checking {} backward", rule_name);
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

/// An explanation for a given term between to congruent enodes.
/// Each child has a proof that it is congruent to the other enode's children.
/// The rule denotes the rule that can be used to rewrite the explanation and it's
/// final children to the next term in a proof.
#[derive(Debug, Clone)]
pub struct TreeTerm<L: Language> {
    node: L,
    // a rule for rewriting the term backward or forward
    backward_rule: Option<String>,
    forward_rule: Option<String>,
    // one proof per child of the node
    child_proofs: Vec<ExplanationTrees<L>>,
}

impl<L: Language> TreeTerm<L> {
    pub fn new(node: L, child_proofs: Vec<ExplanationTrees<L>>) -> TreeTerm<L> {
        TreeTerm {
            node,
            backward_rule: None,
            forward_rule: None,
            child_proofs,
        }
    }

    fn flatten_proof(proof: &ExplanationTrees<L>) -> Vec<FlatTerm<L>> {
        let mut flat_proof: Vec<FlatTerm<L>> = vec![];
        for tree in proof {
            let mut explanation = tree.flatten_explanation();

            if !flat_proof.is_empty() {
                if !explanation[0].has_rewrite_forward() && !explanation[0].has_rewrite_backward() {
                    let last = flat_proof.pop().unwrap();
                    explanation[0].combine_rewrites(&last);
                }
            }

            flat_proof.extend(explanation);
        }

        flat_proof
    }

    pub fn flatten_explanation(&self) -> Vec<FlatTerm<L>> {
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

        proof[0].backward_rule = self.backward_rule.clone();
        proof[0].forward_rule = self.forward_rule.clone();

        proof
    }
}

/// A flattened explanation which represents a single term
/// in a proof.
/// At most one part of the term is rewritten forward and at most one
/// part of the term is rewritten backwards.
#[derive(Debug, Clone, Eq)]
pub struct FlatTerm<L: Language> {
    node: L,
    backward_rule: Option<String>,
    forward_rule: Option<String>,
    children: Vec<FlatTerm<L>>,
}

impl<L: Language + Display> Display for FlatTerm<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.to_sexp().to_string();
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
            self.forward_rule = other.forward_rule.clone();
        }

        if other.backward_rule.is_some() {
            assert!(self.backward_rule.is_none());
            self.backward_rule = other.backward_rule.clone();
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
    pub fn to_sexp(&self) -> Sexp {
        let op = Sexp::String(self.node.to_string());
        let mut expr = if self.node.is_leaf() {
            op
        } else {
            let mut vec = vec![op];
            for child in &self.children {
                vec.push(child.to_sexp());
            }
            Sexp::List(vec)
        };

        if let Some(rule_name) = &self.backward_rule {
            expr = Sexp::List(vec![
                Sexp::String("Rewrite<=".to_string()),
                Sexp::String(rule_name.clone()),
                expr,
            ]);
        }

        if let Some(rule_name) = &self.forward_rule {
            expr = Sexp::List(vec![
                Sexp::String("Rewrite=>".to_string()),
                Sexp::String(rule_name.clone()),
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
        pretty_print(&mut buf, &self.to_sexp(), width, 1).unwrap();
        write!(f, "{}", buf)
    }
}

impl<L: Language + Display> TreeTerm<L> {
    pub fn to_sexp(&self) -> Sexp {
        let op = Sexp::String(self.node.to_string());
        let mut expr = if self.node.is_leaf() {
            op
        } else {
            let mut vec = vec![op];
            for child in &self.child_proofs {
                assert!(child.len() > 0);
                if child.len() == 1 {
                    vec.push(child[0].to_sexp());
                } else {
                    let mut child_expressions = vec![Sexp::String("Explanation".to_string())];
                    for child_explanation in child.iter() {
                        child_expressions.push(child_explanation.to_sexp());
                    }
                    vec.push(Sexp::List(child_expressions));
                }
            }
            Sexp::List(vec)
        };

        if let Some(rule_name) = &self.backward_rule {
            expr = Sexp::List(vec![
                Sexp::String("Rewrite<=".to_string()),
                Sexp::String(rule_name.clone()),
                expr,
            ]);
        }

        if let Some(rule_name) = &self.forward_rule {
            expr = Sexp::List(vec![
                Sexp::String("Rewrite=>".to_string()),
                Sexp::String(rule_name.clone()),
                expr,
            ]);
        }

        expr
    }
}

impl<L: Language> FlatTerm<L> {
    pub fn new(node: L, children: Vec<FlatTerm<L>>) -> FlatTerm<L> {
        FlatTerm {
            node,
            backward_rule: None,
            forward_rule: None,
            children,
        }
    }

    pub fn rewrite(&self, lhs: &PatternAst<L>, rhs: &PatternAst<L>) -> FlatTerm<L> {
        let lhs_nodes = lhs.as_ref();
        let mut bindings = Default::default();
        self.make_bindings(lhs_nodes, lhs_nodes.len() - 1, &mut bindings);
        FlatTerm::from_pattern(rhs.as_ref(), rhs.as_ref().len() - 1, &bindings)
    }

    pub fn has_rewrite_forward(&self) -> bool {
        !self.forward_rule.is_none()
            || self
                .children
                .iter()
                .any(|child| child.has_rewrite_forward())
    }

    pub fn has_rewrite_backward(&self) -> bool {
        !self.backward_rule.is_none()
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
    ) -> HashMap<String, &'a Rewrite<L, N>> {
        let mut table: HashMap<String, &Rewrite<L, N>> = Default::default();
        for r in rules {
            table.insert(r.name.clone(), r);
        }
        table
    }

    pub fn check_each_explain<N: Analysis<L>>(&self, rules: &[&Rewrite<L, N>]) -> bool {
        let rule_table = Explain::make_rule_table(rules);
        for i in 0..self.explainfind.len() {
            let explain_node = &self.explainfind[i];
            if explain_node.next != Id::from(i) {
                let mut current_explanation = self.node_to_flat_explanation(Id::from(i));
                let mut next_explanation = self.node_to_flat_explanation(explain_node.next);
                match &explain_node.justification {
                    Justification::Rule(rule_name) => {
                        if let Some(rule) = rule_table.get(rule_name) {
                            if !explain_node.is_rewrite_forward {
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
                    _ => (),
                }
            }
        }
        true
    }

    pub fn new() -> Self {
        Explain {
            unionfind: Default::default(),
            explainfind: vec![],
            memo: Default::default(),
            uncanon_memo: Default::default(),
        }
    }

    pub fn add(&mut self, node: L) -> Id {
        let set = self.unionfind.make_set();
        self.uncanon_memo.insert(node.clone(), set);
        self.explainfind.push(ExplainNode {
            node,
            justification: Justification::Congruence,
            next: set,
            current: set,
            is_rewrite_forward: false,
        });
        set
    }

    fn add_expr(&mut self, expr: &RecExpr<L>) -> Id {
        let nodes: Vec<ENodeOrVar<L>> = expr
            .as_ref()
            .iter()
            .map(|node| ENodeOrVar::ENode(node.clone()))
            .collect();
        let pattern = PatternAst::from(nodes);
        self.add_match(None, &pattern, &Default::default())
    }

    // add_match uses the memo in order to re-discover matches
    // given a substitution.
    // This requires that congruence has been restored and the memo is up to date.
    pub(crate) fn add_match(
        &mut self,
        eclass: Option<Id>,
        pattern: &PatternAst<L>,
        subst: &Subst,
    ) -> Id {
        let nodes = pattern.as_ref();
        let mut new_ids = Vec::with_capacity(nodes.len());
        let mut match_ids = Vec::with_capacity(nodes.len());
        for node in nodes {
            match node {
                ENodeOrVar::Var(var) => {
                    let bottom_id = self.find(subst[*var]);
                    new_ids.push(self.find(bottom_id));
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
                        new_ids.push(self.find(*existing_id));
                        match_ids.push(*existing_id);
                    } else {
                        let congruent_id = *self.memo.get(&node).unwrap_or_else(|| {
                            panic!("Pattern did not exist for substitution!");
                        });

                        let congruent_class = self.find(congruent_id);

                        new_ids.push(congruent_class);
                        assert!(
                            node == self.explainfind[usize::from(congruent_id)]
                                .node
                                .clone()
                                .map_children(|id| self.find(id))
                        );

                        let new_congruent_id = self.add(new_congruent_node);
                        match_ids.push(new_congruent_id);
                        // make the congruent_id we found the leader
                        self.union(
                            new_congruent_id,
                            congruent_id,
                            congruent_class,
                            new_congruent_id,
                            Some(Justification::Congruence),
                        );
                    }
                }
            }
        }

        let last_id = *match_ids.last().unwrap();
        if let Some(eclass_id) = eclass {
            assert_eq!(self.find(last_id), self.find(eclass_id));
        }
        last_id
    }

    pub fn find(&self, current: Id) -> Id {
        self.unionfind.find(current)
    }

    pub fn find_mut(&mut self, current: Id) -> Id {
        self.unionfind.find_mut(current)
    }

    // reverse edges recursively to make this node the leader
    fn make_leader(&mut self, node: Id) {
        let next = self.explainfind[usize::from(node)].next;
        if next != node {
            self.make_leader(next);
            self.explainfind[usize::from(next)].justification =
                self.explainfind[usize::from(node)].justification.clone();
            self.explainfind[usize::from(next)].is_rewrite_forward =
                !self.explainfind[usize::from(node)].is_rewrite_forward;
            self.explainfind[usize::from(next)].next = node;
        }
    }

    pub(crate) fn union(
        &mut self,
        node1: Id,
        node2: Id,
        canon_id1: Id,
        canon_id2: Id,
        justification_maybe: Option<Justification>,
    ) -> Id {
        assert_ne!(self.find(node1), self.find(node2));
        if let Some(justification) = justification_maybe {
            self.make_leader(node1);
            self.explainfind[usize::from(node1)].next = node2;
            self.explainfind[usize::from(node1)].justification = justification;
            self.explainfind[usize::from(node1)].is_rewrite_forward = true;
            self.unionfind.union(canon_id1, canon_id2)
        } else {
            // Act like a normal union find when the rule is not provided.
            self.unionfind.union(canon_id1, canon_id2)
        }
    }

    pub fn explain_matches(
        &mut self,
        left: &RecExpr<L>,
        right: &PatternAst<L>,
        subst: &Subst,
    ) -> Explanation<L> {
        let left_added = self.add_expr(left);
        let right_added = self.add_match(None, &right, &subst);
        let mut cache = Default::default();
        Explanation::new(self.explain_enodes(left_added, right_added, &mut cache))
    }

    pub fn explain_equivalence(&mut self, left: &RecExpr<L>, right: &RecExpr<L>) -> Explanation<L> {
        let left_added = self.add_expr(left);
        let right_added = self.add_expr(right);
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

            let next_left = self.explainfind[usize::from(left)].next;
            let next_right = self.explainfind[usize::from(right)].next;
            assert!(next_left != left || next_right != right);
            left = next_left;
            right = next_right;
        }
    }

    fn get_nodes<'a>(&'a self, mut node: Id, ancestor: Id) -> Vec<&'a ExplainNode<L>> {
        if node == ancestor {
            return vec![];
        }

        let mut nodes = vec![];
        loop {
            let next = self.explainfind[usize::from(node)].next;
            nodes.push(&self.explainfind[usize::from(node)]);
            if next == ancestor {
                return nodes;
            }
            assert!(next != node);
            node = next;
        }
    }

    fn explain_enodes(
        &self,
        left: Id,
        right: Id,
        cache: &mut ExplainCache<L>,
    ) -> ExplanationTrees<L> {
        assert!(self.find(left) == self.find(right));

        let mut proof = vec![Rc::new(self.node_to_explanation(left))];
        let ancestor = self.common_ancestor(left, right);
        let left_nodes = self.get_nodes(left, ancestor);
        let right_nodes = self.get_nodes(right, ancestor);

        for (i, node) in left_nodes
            .iter()
            .chain(right_nodes.iter().rev())
            .enumerate()
        {
            let mut direction = node.is_rewrite_forward;
            let mut next = node.next;
            let mut current = node.current;
            if i >= left_nodes.len() {
                direction = !direction;
                std::mem::swap(&mut next, &mut current);
            }

            proof.push(self.explain_adjacent(current, next, direction, &node.justification, cache));
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
                    rewritten.forward_rule = Some(name.clone());
                } else {
                    rewritten.backward_rule = Some(name.clone());
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
}
