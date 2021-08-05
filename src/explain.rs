use crate::{Id, UnionFind, Language, HashMap};
use std::fmt::Debug;

#[derive(Debug, Clone)]
struct Justification {
    next: Id,
    rule_name: String,
    is_rewrite_forward: bool,
}

#[derive(Debug, Clone)]
struct ExplainNode<L: Language> {
    enode: L,
    justification: Option<Justification>,
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
        self.explainfind.push(ExplainNode { enode, justification: None});
        set
    }

    pub fn find(&self, current: Id) -> Id {
        self.unionfind.find(current)
    }

    pub fn find_mut(&mut self, current: Id) -> Id {
        self.unionfind.find_mut(current)
    }

    fn make_leader(&mut self, node: Id) {
        let my_justification = self.explainfind[usize::from(node)].justification.clone();
        if let Some(justification) = my_justification {
            self.make_leader(justification.next);
            self.explainfind[usize::from(justification.next)].justification = Some(Justification {
                next: node,
                rule_name: justification.rule_name,
                is_rewrite_forward: !justification.is_rewrite_forward,
            });
        }
    }

    pub fn union(&mut self, node1: Id, node2: Id, rule_name: Option<String>) -> Id {
        if let Some(name) = rule_name {
            self.make_leader(node1);
            self.explainfind[usize::from(node1)].justification = Some(Justification {
                next: node2,
                rule_name: name,
                is_rewrite_forward: true,
            });
            self.unionfind.union(node1, node2)
        } else {
            self.unionfind.union_roots(node1, node2)
        }
    }
}
