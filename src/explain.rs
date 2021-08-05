use crate::{Id, UnionFind, Language, Analysis, HashMap, PatternAst, Subst, ENodeOrVar, EClass};
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
    // a map from updated enodes to their original enode ids
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

    // add_match uses the memo in order to re-discover matches
    // given a substitution.
    // If the memo is not sufficiently up-to-date, the eclass is searched for the un-updated enode.
    pub(crate) fn add_match<N>(&mut self, pattern: &PatternAst<L>, subst: &Subst, classes: &HashMap<Id, EClass<L, N>>) -> Id {
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
                        println!("Found");
                        new_ids.push(self.find(*existing_id));
                        match_ids.push(*existing_id);
                    } else {
                        println!("Searching!");
                        let congruent_id = *self.memo.get(&node).unwrap_or_else(|| {
                            for (pnode, pid) in &classes.get(&node.children()[0]).unwrap().parents {
                                if pnode.clone().map_children(|id| self.find(id)) == node {
                                    return pid;
                                }
                            }
                            panic!("Didn't find matching parent for pattern");
                        });
                        new_ids.push(self.find(congruent_id));
                        assert!(node == self.explainfind[usize::from(congruent_id)].enode.clone().map_children(|id| self.find(id)));
                        

                        let new_congruent_id = self.add(new_congruent_node);
                        match_ids.push(new_congruent_id);
                        // make the congruent_id we found the leader
                        self.union(new_congruent_id, congruent_id, self.find(congruent_id), new_congruent_id, Some(Justification::Congruence));
                    }
                }
            }
        }

        *match_ids.last().unwrap()
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
            self.explainfind[usize::from(node1)].next = node1;
            self.explainfind[usize::from(node1)].justification = justification;
            self.explainfind[usize::from(node1)].is_rewrite_forward = true;
            self.unionfind.union_roots(canon_id1, canon_id2)
        } else {
            // Act like a normal union find when the rule is not provided.
            self.unionfind.union_roots(canon_id1, canon_id2)
        }
    }
}
