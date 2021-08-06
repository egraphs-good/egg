use crate::{
    Analysis, EClass, ENodeOrVar, HashMap, HashSet, Id, Language, PatternAst, Rewrite, Subst, UnionFind, Var,
    RecExpr,
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

pub type Explanation<L> = Vec<Rc<TreeTerm<L>>>;


/// An explanation for a given term between to congruent enodes.
/// Each child has a proof that it is congruent to the other enode's children.
/// The rule denotes the rule that can be used to rewrite the explanation and it's
/// final children to the next term in a proof.
#[derive(Debug, Clone)]
pub struct TreeTerm<L: Language> {
    node: L,
    is_rewritten_forward: bool,
    is_rewritten_backward: bool,
    next_rule: Option<String>,
    // one proof per child of the node
    child_proofs: Vec<Explanation<L>>,
}

impl<L: Language> TreeTerm<L> {
    pub fn new(node: L, child_proofs: Vec<Explanation<L>>) -> TreeTerm<L> {
        TreeTerm {
            node,
            is_rewritten_forward: false,
            is_rewritten_backward: false,
            next_rule: None,
            child_proofs,
        }
    }

    fn flatten_proof(proof: &Explanation<L>) -> Vec<FlatTreeTerm<L>> {
        proof.iter().flat_map(|explanation| explanation.flatten_explanation()).collect()
    }

    pub fn flatten_explanation(&self) -> Vec<FlatTreeTerm<L>> {
        let mut proof = vec![];
        let mut child_proofs = vec![];
        let mut representative_terms = vec![];
        for child_explanation in &self.child_proofs {
            let flat_proof = TreeTerm::flatten_proof(child_explanation);
            representative_terms.push(flat_proof[0].clone());
            child_proofs.push(flat_proof);
        }

        for (i, child_proof) in child_proofs.iter().enumerate() {
            for child in child_proof.iter() {
                let mut children = vec![];
                for (j, rep_term) in representative_terms.iter().enumerate() {
                    if j == i {
                        children.push(child.clone());
                    } else {
                        children.push(rep_term.clone());
                    }
                }

                proof.push(FlatTreeTerm {
                    node: child.node.clone(),
                    is_rewritten_forward: false,
                    is_rewritten_backward: false,
                    next_rule: child.next_rule.clone(),
                    children});
            }
            representative_terms[i] = child_proof.last().unwrap().clone();
        }

        proof[0].is_rewritten_backward = self.is_rewritten_backward;
        proof.last_mut().unwrap().is_rewritten_forward = self.is_rewritten_forward;
        proof.last_mut().unwrap().next_rule = self.next_rule.clone();

        proof
    }
}

/// A flattened explanation which represents a single term
/// in a proof.
/// At most one part of the term is rewritten forward and at most one
/// part of the term is rewritten backwards.
/// `next_rule` represents the rule that can be used to rewrite either this term or
/// the next back to this term.
#[derive(Debug, Clone, Eq)]
pub struct FlatTreeTerm<L: Language> {
    node: L,
    is_rewritten_forward: bool,
    is_rewritten_backward: bool,
    next_rule: Option<String>,
    children: Vec<FlatTreeTerm<L>>,
}

impl<L: Language + Display> Display for FlatTreeTerm<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.to_sexp().to_string();
        write!(f, "{}", s)
    }
}

impl<L: Language> PartialEq for FlatTreeTerm<L> {
    fn eq(&self, other: &FlatTreeTerm<L>) -> bool {
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

impl<L: Language> Default for Explain<L> {
    fn default() -> Self {
        Self::new()
    }
}

impl<L: Language + Display> FlatTreeTerm<L> {
    pub fn to_sexp(&self) -> Sexp {
        let op = Sexp::String(self.node.to_string());
        if self.node.is_leaf() {
            op
        } else {
            let mut vec = vec![op];
            for child in &self.children {
                vec.push(child.to_sexp());
            }
            Sexp::List(vec)
        }
    }
}

impl<L: Language> FlatTreeTerm<L> {
    pub fn new(node: L, children: Vec<FlatTreeTerm<L>>) -> FlatTreeTerm<L> {
        FlatTreeTerm {
            node,
            is_rewritten_forward: false,
            is_rewritten_backward: false,
            next_rule: None,
            children,
        }
    }

    pub fn rewrite(&self, lhs: &PatternAst<L>, rhs: &PatternAst<L>) -> FlatTreeTerm<L> {
        let lhs_nodes = lhs.as_ref();
        let mut bindings = Default::default();
        self.make_bindings(lhs_nodes, lhs_nodes.len() - 1, &mut bindings);
        FlatTreeTerm::from_pattern(rhs.as_ref(), rhs.as_ref().len() - 1, &bindings)
    }

    fn from_pattern(
        pattern: &[ENodeOrVar<L>],
        location: usize,
        bindings: &HashMap<Var, &FlatTreeTerm<L>>,
    ) -> FlatTreeTerm<L> {
        match &pattern[location] {
            ENodeOrVar::Var(var) => bindings.get(var).unwrap().clone().clone(),
            ENodeOrVar::ENode(node) => {
                let children = node.fold(vec![], |mut acc, child| {
                    acc.push(FlatTreeTerm::from_pattern(
                        pattern,
                        usize::from(child),
                        bindings,
                    ));
                    acc
                });
                FlatTreeTerm::new(node.clone(), children)
            }
        }
    }

    fn make_bindings<'a>(
        &'a self,
        pattern: &[ENodeOrVar<L>],
        location: usize,
        bindings: &mut HashMap<Var, &'a FlatTreeTerm<L>>,
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

    fn node_to_flat_explanation(&self, node_id: Id) -> FlatTreeTerm<L> {
        let node = self.explainfind[usize::from(node_id)].node.clone();
        let children = node.fold(vec![], |mut sofar, child| {
            sofar.push(self.node_to_flat_explanation(child));
            sofar
        });
        FlatTreeTerm::new(node, children)
    }

    fn make_rule_table<'a, N: Analysis<L>>(
        &self,
        rules: &[&'a Rewrite<L, N>],
    ) -> HashMap<String, &'a Rewrite<L, N>> {
        let mut table: HashMap<String, &Rewrite<L, N>> = Default::default();
        for r in rules {
            table.insert(r.name.clone(), r);
        }
        table
    }

    // if the rewrite is just patterns, then it can check it
    fn check_rewrite<'a, N: Analysis<L>>(
        &self,
        mut current: &'a FlatTreeTerm<L>,
        mut next: &'a FlatTreeTerm<L>,
        rewrite: &Rewrite<L, N>,
        is_rewrite_forward: bool,
    ) -> bool {
        if let Some(lhs) = rewrite.searcher.get_pattern_ast() {
            if let Some(rhs) = rewrite.applier.get_pattern_ast() {
                if !is_rewrite_forward {
                    std::mem::swap(&mut current, &mut next);
                }
                if &current.rewrite(lhs, rhs) != next {
                    return false;
                }
            }
        }
        true
    }

    pub fn check_each_explain<N: Analysis<L>>(&self, rules: &[&Rewrite<L, N>]) -> bool {
        let rule_table = self.make_rule_table(rules);
        for i in 0..self.explainfind.len() {
            let explain_node = &self.explainfind[i];
            if explain_node.next != Id::from(i) {
                let current_explanation = self.node_to_flat_explanation(Id::from(i));
                let next_explanation = self.node_to_flat_explanation(explain_node.next);
                match &explain_node.justification {
                    Justification::Rule(rule_name) => {
                        if let Some(rule) = rule_table.get(rule_name) {
                            if !self.check_rewrite(
                                &current_explanation,
                                &next_explanation,
                                rule,
                                explain_node.is_rewrite_forward,
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

    fn add_expr(&mut self, expr: &RecExpr<L>) -> Id{
        let nodes: Vec<ENodeOrVar<L>> = expr.as_ref().iter().map(|node| ENodeOrVar::ENode(node.clone())).collect();
        let pattern = PatternAst::from(nodes);
        self.add_match(None, &pattern, &Default::default())
    }

    // add_match uses the memo in order to re-discover matches
    // given a substitution.
    // This requires that congruence has been restored and the memo is up to date.
    pub(crate) fn add_match(&mut self, eclass: Option<Id>, pattern: &PatternAst<L>, subst: &Subst) -> Id {
        let nodes = pattern.as_ref();
        let mut new_ids = Vec::with_capacity(nodes.len());
        let mut match_ids = Vec::with_capacity(nodes.len());
        for node in nodes {
            match node {
                ENodeOrVar::Var(var) => {
                    let bottom_id = self.find(subst[*var]);
                    new_ids.push(bottom_id);
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
                            panic!("Memo not up to date!");
                            /*for (pnode, pid) in &classes.get(&node.children()[0]).unwrap().parents {
                                if pnode.clone().map_children(|id| self.find(id)) == node {
                                    return pid;
                                }
                            }
                            panic!("Didn't find matching parent for pattern");*/
                        });
                        new_ids.push(self.find(congruent_id));
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
                            self.find(congruent_id),
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
        if let Some(justification) = justification_maybe {
            self.make_leader(node1);
            self.explainfind[usize::from(node1)].next = node2;
            self.explainfind[usize::from(node1)].justification = justification;
            self.explainfind[usize::from(node1)].is_rewrite_forward = true;
            self.unionfind.union_roots(canon_id1, canon_id2)
        } else {
            // Act like a normal union find when the rule is not provided.
            self.unionfind.union_roots(canon_id1, canon_id2)
        }
    }

    pub fn explain_equivalence(&mut self, left: &RecExpr<L>, right: &RecExpr<L>) -> Explanation<L> {
        let left_added = self.add_expr(left);
        let right_added = self.add_expr(right);
        self.explain_enodes(left_added, right_added)
    }

    fn common_anscestor(&self, mut left: Id, mut right: Id) -> Id {
        let mut seen: HashSet<Id> = Default::default();
        loop {
            if seen.insert(left) {
                return left;
            } else if seen.insert(right) {
                return right;
            }

            let next_left = self.explainfind[usize::from(left)].next;
            let next_right = self.explainfind[usize::from(right)].next;
            assert!(next_left != left || next_right != right);
            if next_left != left {
                left = self.explainfind[usize::from(left)].next;
            }
            if next_right != right {
                right = self.explainfind[usize::from(right)].next;
            }
        }
    }

    fn get_nodes<'a>(&'a self, mut node: Id, anscestor: Id) -> Vec<&'a ExplainNode<L>> {
        let mut nodes = vec![];
        loop {
            let next = self.explainfind[usize::from(node)].next;
            if next == node {
                return nodes;
            } else {
                assert!(next != node);
                nodes.push(&self.explainfind[usize::from(node)]);
                node = next;
            }
        }
    }

    fn explain_enodes(&self, left: Id, right: Id) -> Explanation<L> {
        let mut proof = vec![self.node_to_explanation(left)];
        let anscestor = self.common_anscestor(left, right);
        let left_nodes = self.get_nodes(left, anscestor);
        let right_nodes = self.get_nodes(right, anscestor);

        for (i, node) in left_nodes.iter().chain(right_nodes.iter()).enumerate() {
            let mut direction = node.is_rewrite_forward;
            let mut next = node.next;
            let mut current = node.current;
            if i >= left_nodes.len() {
                direction = !direction;
                std::mem::swap(&mut next, &mut current);
            }
            

            match &node.justification {
                Justification::Rule(name) => {
                    if direction {
                        proof.last_mut().unwrap().is_rewritten_forward = true;
                    }
                    proof.last_mut().unwrap().next_rule = Some(name.clone());
    
                    let mut rewritten = self.node_to_explanation(next);
                    if !direction {
                        rewritten.is_rewritten_backward = true;
                    }
                    proof.push(rewritten);
                }
                Justification::Congruence => {
                    // add the children proofs to the last explanation
                    let current_node = &self.explainfind[usize::from(current)].node;
                    let next_node = &self.explainfind[usize::from(next)].node;

                    for (i, (left_child, right_child)) in current_node.children().iter().zip(next_node.children().iter()).enumerate() {
                        let subproof = self.explain_enodes(*left_child, *right_child);
                        proof.last_mut().unwrap().child_proofs[i].extend(subproof);
                    }
                }
            }
        }

        proof.into_iter().map(|term| Rc::new(term)).collect()
    }
}
