use std::fmt;

use crate::{EGraph, Id};

pub struct Dot<'a> {
    egraph: &'a EGraph,
}

impl<'a> Dot<'a> {
    pub fn new(egraph: &EGraph) -> Dot {
        Dot { egraph }
    }
}

impl<'a> fmt::Display for Dot<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "digraph {{\n")?;

        // set compound=true to enable edges to clusters
        write!(f, "  compound=true\n")?;

        // define all the nodes, clustered by eclass
        for (leader, class) in &self.egraph.classes {
            write!(f, "  subgraph cluster_{} {{\n", leader.0)?;
            write!(f, "  style=dotted")?;
            for id in class {
                let node = &self.egraph.nodes[id.0];
                write!(f, "    {}[label = \"", id.0)?;
                node.write_label(f)?;
                write!(f, "\"]\n")?;
            }
            write!(f, "  }}\n")?;
        }

        let mut children = Vec::new();
        for (i, node) in self.egraph.nodes.iter().enumerate() {
            node.fill_children(&mut children);
            for child in &children {
                // write the edge to the child, but clip it to the eclass with lhead
                let child_leader = self.egraph.leaders[child.0];
                write!(
                    f,
                    "  {} -> {} [lhead = cluster_{}]\n",
                    i, child.0, child_leader.0
                )?;
            }
            children.clear();
        }

        write!(f, "}}")
    }
}
