mod dot;
mod parse;

use std::collections::HashMap;

use log::{info, trace};

/// EClass Id
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Id(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
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

    fn map_ids(&self, mut f: impl FnMut(Id) -> Id) -> ENode {
        match self {
            ENode::Var(_) => self.clone(),
            ENode::Const(_) => self.clone(),
            ENode::Plus(l, r) => ENode::Plus(f(*l), f(*r)),
            ENode::Times(l, r) => ENode::Times(f(*l), f(*r)),
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

#[derive(Debug, Default, PartialEq)]
pub struct EGraph {
    nodes: HashMap<ENode, Id>,
    leaders: Vec<Id>,
    classes: HashMap<Id, Vec<ENode>>,
}

#[derive(Debug, PartialEq)]
pub struct Pattern {
    nodes: Vec<ENode>,
    lhs: Id,
    rhs: Id,
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

        // make sure that all values of the union find are leaders
        for leader in &self.leaders {
            assert_eq!(leader, &self.leaders[leader.0]);
        }
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn add(&mut self, enode: ENode) -> Id {
        self.check();

        trace!("Adding       {:?}", enode);

        // make sure that the enodes children are already in the set
        if cfg!(debug_assertions) {
            let mut ids = Vec::new();
            enode.fill_children(&mut ids);
            for id in ids {
                assert!(id.0 < self.len());
            }
        }

        // hash cons
        let id = match self.nodes.get(&enode) {
            None => {
                let next_id = Id(self.len());
                trace!("Added  {:4}: {:?}", next_id.0, enode);
                self.leaders.push(next_id);
                self.classes.insert(next_id, vec![enode.clone()]);
                self.nodes.insert(enode, next_id);
                next_id
            }
            Some(id) => {
                trace!("Added *{:4}: {:?}", id.0, enode);
                *id
            }
        };

        self.check();
        id
    }

    // pub fn pattern_match(&mut self, pattern: &Pattern) -> EGraph {
    //     // stores (PatternId, EClassId) matches
    //     let mut database = HashSet::new();

    //     for (leader, class) in self.classes.iter() {
    //         let mut stack = Vec::new();
    //         stack.push((start, node));

    //         while let Some((p, n)) = stack.pop() {
    //             use ENode::*;
    //             match (p, n) {
    //                 (Var(s), _) => (),
    //                 (Plus(pl, pr), Plus(nl, nr)) => {
    //                     stack.push((pl, nl));
    //                     stack.push((pr, nr));
    //                 }
    //             }
    //         }
    //     }
    // }

    fn get_eclass(&self, eclass_id: Id) -> &[ENode] {
        self.classes
            .get(&eclass_id)
            .unwrap_or_else(|| panic!("Couldn't find eclass {:?}", eclass_id))
    }

    fn match_node_against_eclass(
        &self,
        mut var_mapping: HashMap<String, Id>,
        pattern: &Pattern,
        eclass: Id,
        pattern_node: ENode,
    ) -> Vec<HashMap<String, Id>> {
        if let ENode::Var(s) = pattern_node {
            match var_mapping.get(&s) {
                None => {
                    var_mapping.insert(s, eclass);
                }
                Some(&prev_mapped_eclass) => {
                    if eclass != prev_mapped_eclass {
                        return vec![];
                    }
                }
            }

            return vec![var_mapping];
        }

        let mut new_mappings = Vec::new();

        for class_node in self.get_eclass(eclass) {
            use ENode::*;
            match (&pattern_node, class_node) {
                (Var(_), _) => panic!("pattern isn't a var at this point"),
                (Plus(pl, pr), Plus(nl, nr)) => {
                    let left_mappings = self.match_node_against_eclass(
                        var_mapping.clone(),
                        pattern,
                        *nl,
                        pattern.nodes[pl.0].clone(),
                    );

                    for vm in left_mappings {
                        new_mappings.extend(self.match_node_against_eclass(
                            vm,
                            pattern,
                            *nr,
                            pattern.nodes[pr.0].clone(),
                        ))
                    }
                }
                (Times(_pl, _pr), Times(_nl, _nr)) => unimplemented!(),
                _ => (),
            }
        }

        new_mappings
    }

    fn rebuild(&mut self) {
        // TODO don't copy so much
        let mut new_classes = HashMap::new();

        for (leader, class) in self.classes.iter() {
            let new_nodes: Vec<_> = class
                .iter()
                .map(|node| node.map_ids(|id| self.leaders[id.0]))
                .collect();

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

    fn union(&mut self, id1: Id, id2: Id) -> Id {
        self.check();

        trace!("Unioning {} and {}", id1.0, id2.0);

        let mut leader1 = self.leaders[id1.0];
        let mut leader2 = self.leaders[id2.0];

        // already unioned
        if leader1 == leader2 {
            trace!("Already unioned...");
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

        // remove the smaller class, merging into the bigger class
        let smaller_class = self.classes.remove(&leader1).unwrap();
        let bigger_class = self.classes.remove(&leader2).unwrap();

        let mut new_nodes = Vec::with_capacity(smaller_class.len() + bigger_class.len());
        for node in smaller_class.into_iter().chain(bigger_class) {
            let old_leader = self.nodes[&node];
            self.leaders[old_leader.0] = leader2;
            // let new_node = node.map_ids(|id| self.leaders[id.0]);
            // new_nodes.push(new_node);
            new_nodes.push(node);
            trace!("{:?}", new_nodes);
        }

        self.classes.insert(leader2, new_nodes);

        self.check();
        trace!("Unioned {} -> {}", leader1.0, leader2.0);
        trace!("Leaders: {:?}", self.leaders);
        for (leader, class) in &self.classes {
            trace!("  {:?}: {:?}", leader, class);
        }
        leader2
    }
}

#[cfg(test)]
fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
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
        info!("Writing {}.dot ...\n{}", name, dot);
    }

    #[test]
    fn simple_add() {
        crate::init_logger();
        let mut egraph = EGraph::default();

        let x = egraph.add(var("x"));
        let x2 = egraph.add(var("x"));
        let plus = egraph.add(ENode::Plus(x, x2));

        let y = egraph.add(var("y"));

        egraph.union(x, y);
        egraph.rebuild();

        dot(&egraph, "foo");

        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn simple_match() {
        crate::init_logger();
        let mut egraph = EGraph::default();

        let x = egraph.add(var("x"));
        let y = egraph.add(var("y"));
        let plus = egraph.add(ENode::Plus(x, y));

        let z = egraph.add(var("z"));
        let w = egraph.add(var("w"));
        let plus2 = egraph.add(ENode::Plus(z, w));

        egraph.union(plus, plus2);
        egraph.rebuild();

        let commute_plus = Pattern {
            nodes: vec![
                var("a"),
                var("b"),
                ENode::Plus(Id(0), Id(1)),
                ENode::Plus(Id(1), Id(0)),
            ],
            lhs: Id(2),
            rhs: Id(3),
        };

        let mappings = egraph.match_node_against_eclass(
            HashMap::new(),
            &commute_plus,
            egraph.leaders[plus.0],
            commute_plus.nodes[commute_plus.lhs.0].clone(),
        );

        let mut expected1 = HashMap::new();
        expected1.insert("a".into(), x);
        expected1.insert("b".into(), y);

        let mut expected2 = HashMap::new();
        expected2.insert("a".into(), z);
        expected2.insert("b".into(), w);

        let expected_mappings = vec![expected1, expected2];
        assert_eq!(expected_mappings, mappings);

        info!("Here are the mappings!");
        for m in mappings {
            info!("mappings: {:?}", m);
        }
    }
}
