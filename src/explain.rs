use crate::{Id, UnionFind, Language, Analysis, HashMap, PatternAst, Subst, ENodeOrVar, EClass, Rewrite, Var};
use std::rc::Rc;
use std::fmt::{self, Debug, Display, Formatter};
use symbolic_expressions::{Sexp};

#[derive(Debug, Clone)]
pub(crate) enum Justification {
    Rule(String),
    Congruence
}


#[derive(Debug, Clone)]
struct ExplainNode<L: Language> {
    node: L,
    next: Id,
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

pub type Proof<L> = Vec<Rc<Explanation<L>>>;

#[derive(Debug, Clone)]
pub struct Explanation<L: Language> {
    node: L,
    is_rewritten_forward: bool,
    is_rewritten_backward: bool,
    next_rule: Option<String>,
    // one proof per child of the node
    child_proofs: Vec<Proof<L>>,
}

impl <L: Language> Explanation<L> {
    pub fn new(node: L, child_proofs: Vec<Proof<L>>) -> Explanation<L> {
        Explanation {
            node,
            is_rewritten_forward: false,
            is_rewritten_backward: false,
            next_rule: None,
            child_proofs,
        }
    }
}

#[derive(Debug, Clone, Eq)]
pub struct FlatExplanation<L: Language> {
    node: L,
    is_rewritten_forward: bool,
    is_rewritten_backward: bool,
    next_rule: Option<String>,
    children: Vec<FlatExplanation<L>>,
}

impl<L: Language + Display> Display for FlatExplanation<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.to_sexp().to_string();
        write!(f, "{}", s)
    }
}

impl<L: Language> PartialEq for FlatExplanation<L> {
    fn eq(&self, other: &FlatExplanation<L>) -> bool {
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

impl<L: Language + Display> FlatExplanation<L> {
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

impl <L: Language> FlatExplanation<L> {
    pub fn new(node: L, children: Vec<FlatExplanation<L>>) -> FlatExplanation<L> {
        FlatExplanation {
            node,
            is_rewritten_forward: false,
            is_rewritten_backward: false,
            next_rule: None,
            children,
        }
    }

    pub fn rewrite(&self, lhs: &PatternAst<L>, rhs: &PatternAst<L>) -> FlatExplanation<L> {
        let lhs_nodes = lhs.as_ref();
        let mut bindings = Default::default();
        self.make_bindings(lhs_nodes, lhs_nodes.len()-1, &mut bindings);
        FlatExplanation::from_pattern(rhs.as_ref(), rhs.as_ref().len()-1, &bindings)
    }

    fn from_pattern(pattern: &[ENodeOrVar<L>], location: usize, bindings: &HashMap<Var, &FlatExplanation<L>>) -> FlatExplanation<L> {
        match &pattern[location] {
            ENodeOrVar::Var(var) => {
                bindings.get(var).unwrap().clone().clone()
            }
            ENodeOrVar::ENode(node) => {
                let children = node.fold(vec![], |mut acc, child| {
                    acc.push(FlatExplanation::from_pattern(pattern, usize::from(child), bindings));
                    acc
                });
                FlatExplanation::new(node.clone(), children)
            }
        }

    }


    fn make_bindings<'a>(&'a self, pattern: &[ENodeOrVar<L>], location: usize, bindings: &mut HashMap<Var, &'a FlatExplanation<L>>) {
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
    fn node_to_explanation(&self, node_id: Id) -> FlatExplanation<L> {
        let node = self.explainfind[usize::from(node_id)].node.clone();
        let children = node.fold(vec![], |mut sofar, child| {
            sofar.push(self.node_to_explanation(child));
            sofar
        });
        FlatExplanation::new(node, children)
    }

    fn make_rule_table<'a, N: Analysis<L>>(&self, rules: &[&'a Rewrite<L, N>]) -> HashMap<String, &'a Rewrite<L, N>> {
        let mut table: HashMap<String, &Rewrite<L, N>> = Default::default();
        for r in rules {
            table.insert(r.name.clone(), r);
        }
        table
    }

    // if the rewrite is just patterns, then it can check it
    fn check_rewrite<N: Analysis<L>>(&self, current: &FlatExplanation<L>, next: &FlatExplanation<L>, rewrite: &Rewrite<L, N>) -> bool {
        if let Some(lhs) = rewrite.searcher.get_pattern_ast() {
            if let Some(rhs) = rewrite.applier.get_pattern_ast() {
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
                let current_explanation = self.node_to_explanation(Id::from(i));
                let next_explanation = self.node_to_explanation(explain_node.next);
                match &explain_node.justification {
                    Justification::Rule(rule_name) => {
                        if !self.check_rewrite(&current_explanation, &next_explanation, rule_table.get(rule_name).unwrap()) {
                            return false;
                        }
                    }
                    _ => ()
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

    pub fn add(&mut self, node: L) -> Id{
        let set = self.unionfind.make_set();
        self.uncanon_memo.insert(node.clone(), set);
        self.explainfind.push(ExplainNode { node, justification: Justification::Congruence, next: set, is_rewrite_forward: false });
        set
    }

    // add_match uses the memo in order to re-discover matches
    // given a substitution.
    // This requires that congruence has been restored and the memo is up to date.
    pub(crate) fn add_match<N>(&mut self, eclass: Id, pattern: &PatternAst<L>, subst: &Subst, classes: &HashMap<Id, EClass<L, N>>) -> Id {
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
                    let node = pattern_node.clone().map_children(|i| new_ids[usize::from(i)]);
                    let new_congruent_node = pattern_node.clone().map_children(|i| match_ids[usize::from(i)]);
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
                        assert!(node == self.explainfind[usize::from(congruent_id)].node.clone().map_children(|id| self.find(id)));
                        

                        let new_congruent_id = self.add(new_congruent_node);
                        match_ids.push(new_congruent_id);
                        // make the congruent_id we found the leader
                        self.union(new_congruent_id, congruent_id, self.find(congruent_id), new_congruent_id, Some(Justification::Congruence));
                    }
                }
            }
        }

        let last_id = *match_ids.last().unwrap();
        assert_eq!(self.find(last_id), self.find(eclass));
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
            self.explainfind[usize::from(next)].justification = self.explainfind[usize::from(node)].justification.clone();
            self.explainfind[usize::from(next)].is_rewrite_forward = !self.explainfind[usize::from(node)].is_rewrite_forward;
            self.explainfind[usize::from(next)].next = node;
        }
    }

    pub(crate) fn union(&mut self, node1: Id, node2: Id, canon_id1: Id, canon_id2: Id, justification_maybe: Option<Justification>) -> Id {
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
}
