use log::*;
use std::collections::HashMap;

use crate::{
    expr::{Id, Node},
    unionfind::{UnionFind, UnionResult},
};

#[derive(Debug)]
pub struct EGraph<N: Node> {
    // TODO no pub
    nodes: HashMap<N, Id>,
    pub leaders: UnionFind,
    pub classes: HashMap<Id, Vec<N>>,
}

impl<N: Node> Default for EGraph<N> {
    fn default() -> EGraph<N> {
        EGraph {
            nodes: HashMap::default(),
            leaders: UnionFind::default(),
            classes: HashMap::default(),
        }
    }
}

pub struct AddResult {
    pub was_there: bool,
    pub id: Id,
}

impl<N: Node> EGraph<N> {
    fn check(&self) {
        assert_eq!(self.nodes.len(), self.leaders.len());

        // make sure the classes map contains exactly the unique leaders
        let sets = self.leaders.build_sets();

        assert_eq!(sets.len(), self.classes.len());
        for l in sets.keys() {
            assert!(self.classes.contains_key(&l));
        }

        // make sure that total size of classes == all nodes
        let sum_classes = self.classes.values().map(|c| c.len()).sum();
        assert_eq!(self.nodes.len(), sum_classes);
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn get_eclass(&self, eclass_id: Id) -> &[N] {
        self.classes
            .get(&eclass_id)
            .unwrap_or_else(|| panic!("Couldn't find eclass {:?}", eclass_id))
    }

    pub fn add(&mut self, enode: N) -> AddResult {
        self.check();

        trace!("Adding       {:?}", enode);

        // make sure that the enodes children are already in the set
        if cfg!(debug_assertions) {
            for &id in enode.children() {
                assert!(id < self.len() as u32);
            }
        }

        // hash cons
        let result = match self.nodes.get(&enode) {
            None => {
                let next_id = self.leaders.make_set();
                trace!("Added  {:4}: {:?}", next_id, enode);
                self.classes.insert(next_id, vec![enode.clone()]);
                self.nodes.insert(enode, next_id);
                AddResult {
                    was_there: false,
                    id: next_id,
                }
            }
            Some(id) => {
                trace!("Added *{:4}: {:?}", id, enode);
                AddResult {
                    was_there: true,
                    id: *id,
                }
            }
        };

        self.check();
        result
    }

    pub fn just_find(&self, id: Id) -> Id {
        self.leaders.just_find(id)
    }

    pub fn rebuild(&mut self) {
        // TODO don't copy so much
        let mut new_classes = HashMap::new();

        for (leader, class) in self.classes.iter() {
            let mut new_nodes = Vec::with_capacity(class.len());
            for node in class {
                let n = node.clone().map_children(|id| self.leaders.just_find(id));
                new_nodes.push(n);
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

    pub fn union(&mut self, id1: Id, id2: Id) -> Id {
        self.check();

        trace!("Unioning {} and {}", id1, id2);

        let (from, to) = match self.leaders.union(id1, id2) {
            UnionResult::SameSet(leader) => return leader,
            UnionResult::Unioned { from, to } => (from, to),
        };

        // remove the smaller class, merging into the bigger class
        let from_class = self.classes.remove(&from).unwrap();
        let to_class = self.classes.remove(&to).unwrap();

        let mut new_nodes = Vec::with_capacity(from_class.len() + to_class.len());
        for node in from_class.into_iter().chain(to_class) {
            new_nodes.push(node.map_children(|id| self.leaders.find(id)));
        }

        self.classes.insert(to, new_nodes);

        self.check();
        trace!("Unioned {} -> {}", from, to);
        trace!("Leaders: {:?}", self.leaders);
        for (leader, class) in &self.classes {
            trace!("  {:?}: {:?}", leader, class);
        }
        to
    }

    pub fn dot(&self, filename: &str)
    where
        N: std::fmt::Display,
    {
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

    use crate::expr::tests::{op, var};

    #[test]
    fn simple_add() {
        crate::init_logger();
        let mut egraph = EGraph::default();

        let x = egraph.add(var("x")).id;
        let x2 = egraph.add(var("x")).id;
        let _plus = egraph.add(op("+", vec![x, x2])).id;

        let y = egraph.add(var("y")).id;

        egraph.union(x, y);
        egraph.rebuild();

        egraph.dot("foo.dot");

        assert_eq!(2 + 2, 4);
    }
}
