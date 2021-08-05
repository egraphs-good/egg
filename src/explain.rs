use crate::{Id, UnionFind, Language, HashMap, PatternAst, Subst, ENodeOrVar};
use std::fmt::Debug;

#[derive(Debug, Clone)]
pub(crate) enum Justification {
    Rule(String),
    Congruence
}


#[derive(Debug, Clone)]
struct ExplainNode<L: Language> {
    enode: L,
    next: Id,
    justification: Justification,
    is_rewrite_forward: bool,
}

#[derive(Debug, Clone)]
pub struct Explain<L: Language> {
    unionfind: UnionFind,
    explainfind: Vec<ExplainNode<L>>,
    pub memo: HashMap<L, Id>,
    uncanon_memo: HashMap<L, Id>,
}

impl<L: Language> Default for Explain<L> {
    fn default() -> Self {
        Self::new()
    }
}

impl<L: Language> Explain<L> {
    pub fn new() -> Self {
        Explain {
            unionfind: Default::default(),
            explainfind: vec![],
            memo: Default::default(),
            uncanon_memo: Default::default(),
        }
    }

    pub fn add(&mut self, enode: L) -> Id{
        let set = self.unionfind.make_set();
        self.uncanon_memo.insert(enode.clone(), set);
        self.explainfind.push(ExplainNode { enode, justification: Justification::Congruence, next: set, is_rewrite_forward: false });
        set
    }

    pub fn add_match(&mut self, class: Id, pattern: &PatternAst<L>, subst: &Subst) {
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
                ENodeOrVar::ENode(enode) => {

                }
            }
        }
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

    pub(crate) fn union(&mut self, node1: Id, node2: Id, justification_maybe: Option<Justification>) -> Id {
        
        if let Some(justification) = justification_maybe {
            self.make_leader(node1);
            self.explainfind[usize::from(node1)].next = node1;
            self.explainfind[usize::from(node1)].justification = justification;
            self.explainfind[usize::from(node1)].is_rewrite_forward = true;
            self.unionfind.union(node1, node2)
        } else {
            // Act like a normal union find when the rule is not provided.
            self.unionfind.union_roots(node1, node2)
        }
    }
}
