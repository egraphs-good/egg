use log::*;
use std::collections::HashMap;

use crate::{
    expr::Expr,
    unionfind::{UnionFind, UnionResult},
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
// TODO no pub u32
pub struct Eid(pub u32);
pub type ENode = Expr<Eid>;

impl ENode {
    pub fn write_label(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Expr::Var(s) => write!(f, "v{}", s.0),
            Expr::Const(i) => write!(f, "c{}", i.0),
            Expr::Op(op, _) => write!(f, "o{}", op.0),
        }
    }
}

#[derive(Debug, Default)]
pub struct EGraph {
    // TODO no pub
    nodes: HashMap<ENode, Eid>,
    pub leaders: UnionFind,
    pub classes: HashMap<Eid, Vec<ENode>>,
}

pub struct AddResult {
    pub was_there: bool,
    pub id: Eid,
}

// helper function that doens't require mut on the whole egraph
pub fn find(uf: &mut UnionFind, id: Eid) -> Eid {
    Eid(uf.find(id.0))
}

impl EGraph {
    fn check(&self) {
        assert_eq!(self.nodes.len(), self.leaders.len());

        // make sure the classes map contains exactly the unique leaders
        let sets = self.leaders.build_sets();

        assert_eq!(sets.len(), self.classes.len());
        for l in sets.keys() {
            let id = Eid(*l);
            assert!(self.classes.contains_key(&id));
        }

        // make sure that total size of classes == all nodes
        let sum_classes = self.classes.values().map(|c| c.len()).sum();
        assert_eq!(self.nodes.len(), sum_classes);
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn get_eclass(&self, eclass_id: Eid) -> &[ENode] {
        self.classes
            .get(&eclass_id)
            .unwrap_or_else(|| panic!("Couldn't find eclass {:?}", eclass_id))
    }

    pub fn add(&mut self, enode: ENode) -> AddResult {
        self.check();

        trace!("Adding       {:?}", enode);

        // make sure that the enodes children are already in the set
        if cfg!(debug_assertions) {
            for id in enode.children() {
                assert!(id.0 < self.len() as u32);
            }
        }

        // hash cons
        let result = match self.nodes.get(&enode) {
            None => {
                let next_id = Eid(self.leaders.make_set());
                trace!("Added  {:4}: {:?}", next_id.0, enode);
                self.classes.insert(next_id, vec![enode.clone()]);
                self.nodes.insert(enode, next_id);
                AddResult {
                    was_there: false,
                    id: next_id,
                }
            }
            Some(id) => {
                trace!("Added *{:4}: {:?}", id.0, enode);
                AddResult {
                    was_there: true,
                    id: *id,
                }
            }
        };

        self.check();
        result
    }

    pub fn just_find(&self, id: Eid) -> Eid {
        Eid(self.leaders.just_find(id.0))
    }

    pub fn rebuild(&mut self) {
        // TODO don't copy so much
        let mut new_classes = HashMap::new();

        for (leader, class) in self.classes.iter() {
            let mut new_nodes = Vec::with_capacity(class.len());
            for node in class {
                new_nodes.push(node.map_ids(|id| Eid(self.leaders.just_find(id.0))));
            }

            new_classes.insert(*leader, new_nodes);
        }
        self.classes = new_classes;

        self.nodes.clear();
        for (leader, class) in &self.classes {
            for node in class {
                self.nodes.insert(node.clone(), *leader);
            }
        }
    }

    pub fn union(&mut self, id1: Eid, id2: Eid) -> Eid {
        self.check();

        trace!("Unioning {} and {}", id1.0, id2.0);

        let (from, to) = match self.leaders.union(id1.0, id2.0) {
            UnionResult::SameSet(leader) => return Eid(leader),
            UnionResult::Unioned { from, to } => (Eid(from), Eid(to)),
        };

        // remove the smaller class, merging into the bigger class
        let from_class = self.classes.remove(&from).unwrap();
        let to_class = self.classes.remove(&to).unwrap();

        let mut new_nodes = Vec::with_capacity(from_class.len() + to_class.len());
        for node in from_class.into_iter().chain(to_class) {
            new_nodes.push(node.map_ids(|id| Eid(self.leaders.find(id.0))));
        }

        self.classes.insert(to, new_nodes);

        self.check();
        trace!("Unioned {} -> {}", from.0, to.0);
        trace!("Leaders: {:?}", self.leaders);
        for (leader, class) in &self.classes {
            trace!("  {:?}: {:?}", leader, class);
        }
        to
    }

    pub fn dot(&self, filename: &str) {
        use std::fs::File;
        use std::io::prelude::*;

        let dot = crate::dot::Dot::new(self);
        let mut file = File::create(filename).unwrap();
        write!(file, "{}", dot).unwrap();
        info!("Writing {}...\n{}", filename, dot);
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::expr::{op, var};

    #[test]
    fn simple_add() {
        crate::init_logger();
        let mut egraph = EGraph::default();

        let x = egraph.add(var(0)).id;
        let x2 = egraph.add(var(0)).id;
        let _plus = egraph.add(op(0, vec![x, x2])).id;

        let y = egraph.add(var(1)).id;

        egraph.union(x, y);
        egraph.rebuild();

        egraph.dot("foo.dot");

        assert_eq!(2 + 2, 4);
    }
}
