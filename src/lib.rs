use std::collections::HashSet;

use ena::unify::{InPlace, UnificationTable};
use petgraph::prelude::*;

#[derive(Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Copy)]
struct Key(u32);

unsafe impl petgraph::graph::IndexType for Key {
    fn new(x: usize) -> Self {
        Key(x as u32)
    }
    fn index(&self) -> usize {
        self.0 as usize
    }
    fn max() -> Self {
        Key(std::u32::MAX)
    }
}

#[derive(Debug, Clone)]
struct EClass(HashSet<Key>);

impl ena::unify::UnifyKey for Key {
    type Value = EClass;

    fn index(&self) -> u32 {
        self.0
    }
    fn from_index(u: u32) -> Self {
        Key(u)
    }
    fn tag() -> &'static str {
        "Key"
    }
}

impl ena::unify::UnifyValue for EClass {
    type Error = ();
    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, Self::Error> {
        let union = value1.0.union(&value2.0);
        Ok(EClass(union.cloned().collect()))
    }
}

#[derive(Debug)]
pub enum Op {
    Plus,
    Times,
}

#[derive(Debug)]
pub enum EValue {
    Op(Op),
    Const(i32),
    Var(String),
}

type InnerEGraph = Graph<ENode, EEdge, Directed, Key>;

#[derive(Debug, Default)]
pub struct EGraph {
    graph: InnerEGraph,
    union: UnificationTable<InPlace<Key>>,
}

#[derive(Debug)]
struct EEdge;

#[derive(Debug)]
struct ENode {
    value: EValue,
}

#[derive(Debug)]
struct Pattern {
    lhs: InnerEGraph,
    rhs: InnerEGraph,
}



fn pattern_match(graph: &InnerEGraph, pattern: &Pattern) {
    let lroot = Key::default();
    for node in graph.node_indices() {
    }
}

#[cfg(test)]
mod tests {

    use super::*;


    fn var(s: &str) -> EValue {
        EValue::Var(s.into())
    }

    fn dot(graph: &InnerEGraph, name: &str) {
        use std::fs::File;
        use std::io::prelude::*;
        use petgraph::dot::{Config, Dot};
        let mut file = File::create(format!("{}.dot", name)).unwrap();
        write!(file, "{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel])).unwrap();
    }

    #[test]
    fn it_works() {
        let mut graph = InnerEGraph::default();
        let x = graph.add_node(ENode { value: var("x") });
        let plus = graph.add_node(ENode {
            value: EValue::Op(Op::Plus),
        });

        graph.add_edge(x, plus, EEdge);
        graph.add_edge(x, plus, EEdge);

        let lhs = {
            let mut graph = InnerEGraph::default();
            let a = graph.add_node(ENode { value: var("a") });
            let plus = graph.add_node(ENode {
                value: EValue::Op(Op::Plus),
            });
            graph.add_edge(a, plus, EEdge);
            graph.add_edge(a, plus, EEdge);
            graph
        };

        let rhs = {
            let mut graph = InnerEGraph::default();
            let a = graph.add_node(ENode { value: var("a") });
            let two = graph.add_node(ENode { value: EValue::Const(2) });
            let times = graph.add_node(ENode {
                value: EValue::Op(Op::Times),
            });
            graph.add_edge(a, times, EEdge);
            graph.add_edge(two, times, EEdge);
            graph
        };

        dot(&lhs, "lhs");
        dot(&rhs, "rhs");

        assert_eq!(2 + 2, 4);
    }
}
