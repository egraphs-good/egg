mod dot;

use std::collections::HashMap;

/// EClass Id
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Id(usize);

pub enum ENode {
    Var(String),
    Const(i32),
    Plus(Id, Id),
    Times(Id, Id),
}

impl ENode {
    fn write_label(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ENode::Var(s) => write!(f, "'{}'", s),
            ENode::Const(i) => write!(f, "{}", i),
            ENode::Plus(..) => write!(f, "+"),
            ENode::Times(..) => write!(f, "*"),
        }
    }
    fn fill_children(&self, vec: &mut Vec<Id>) {
        assert_eq!(vec.len(), 0);
        match self {
            ENode::Var(_) => (),
            ENode::Const(_) => (),
            ENode::Plus(l, r) => {
                vec.push(*l);
                vec.push(*r);
            }
            ENode::Times(l, r) => {
                vec.push(*l);
                vec.push(*r);
            }
        }
    }
}

#[derive(Default)]
pub struct EGraph {
    nodes: Vec<ENode>,
    leaders: Vec<Id>,
    classes: HashMap<Id, Vec<Id>>,
}

impl EGraph {
    fn check(&self) {
        assert_eq!(self.nodes.len(), self.leaders.len());

        // make sure the classes map contains exactly the unique leaders
        let mut unique_leaders = self.leaders.clone();
        unique_leaders.sort();
        unique_leaders.dedup();

        assert_eq!(unique_leaders.len(), self.classes.len());
        for ul in &unique_leaders {
            assert!(self.classes.contains_key(ul));
        }

        // make sure that total size of classes == all nodes
        let sum_classes = self.classes.values().map(|c| c.len()).sum();
        assert_eq!(self.nodes.len(), sum_classes);
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn add(&mut self, enode: ENode) -> Id {
        self.check();

        // make sure that the enodes children are already in the set
        if cfg!(debug_assertions) {
            let mut ids = Vec::new();
            enode.fill_children(&mut ids);
            for Id(i) in ids {
                assert!(i < self.len());
            }
        }

        let next_id = Id(self.len());
        self.nodes.push(enode);
        self.leaders.push(next_id);
        self.classes.insert(next_id, vec![next_id]);

        self.check();

        next_id
    }

    fn union(&mut self, id1: Id, id2: Id) -> Id {
        self.check();

        let mut leader1 = self.leaders[id1.0];
        let mut leader2 = self.leaders[id2.0];

        // already unioned
        if leader1 == leader2 {
            return leader1;
        }

        // make leader2 bigger
        {
            let class1 = &self.classes[&leader1];
            let class2 = &self.classes[&leader2];
            if class1.len() > class2.len() {
                std::mem::swap(&mut leader1, &mut leader2);
            }
        }

        // remove the bigger class, merging into the smaller class
        let smaller_class = self.classes.remove(&leader1).unwrap();
        let bigger_class = self.classes.get_mut(&leader2).unwrap();

        bigger_class.reserve(smaller_class.len());
        for id in smaller_class {
            // TODO transform the nodes that are merged
            self.leaders[id.0] = leader2;
            bigger_class.push(id)
        }

        self.check();
        leader2
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    fn var(s: &str) -> ENode {
        ENode::Var(s.into())
    }

    fn dot(egraph: &EGraph, name: &str) {
        use std::fs::File;
        use std::io::prelude::*;

        let dot = dot::Dot::new(&egraph);
        let mut file = File::create(format!("{}.dot", name)).unwrap();
        write!(file, "{}", dot).unwrap();
        println!("{}", dot);
    }

    #[test]
    fn simple_add() {
        let mut egraph = EGraph::default();

        let x = egraph.add(var("x"));
        let plus = egraph.add(ENode::Plus(x, x));

        let y = egraph.add(var("y"));

        egraph.union(x, y);

        dot(&egraph, "foo");

        assert_eq!(2 + 2, 4);
    }
}
