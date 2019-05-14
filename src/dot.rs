//! EGraph visualization with [GraphViz]
//!
//! Use the `Dot` struct to visualize an [`EGraph`]
//!
//! ```
//! use egg::{
//!   expr::tests::{TestLang, var, op},
//!   egraph::EGraph,
//!   dot::Dot,
//! };
//!
//! // make an egraph
//! let mut egraph = EGraph::<TestLang>::default();
//! let x = egraph.add(var("x"));
//! let y = egraph.add(var("y"));
//! egraph.add(op("+", vec![x.id, y.id]));
//!
//! // create a `Dot` so we can visualize it
//! let dot = Dot::new(&egraph);
//! let output = format!("{}", dot);
//! ```
//!
//! [`EGraph`]: ../egraph/struct.EGraph.html
//! [GraphViz]: https://graphviz.gitlab.io/

use std::fmt::{Display, Formatter, Result};

use crate::{egraph::EGraph, expr::Language};

/// A wrapper for an [`EGraph`] that implements `Display` so you can
/// print it.
///
/// [`EGraph`]: ../egraph/struct.EGraph.html
pub struct Dot<'a, L: Language> {
    egraph: &'a EGraph<L>,
}

impl<'a, L: Language> Dot<'a, L> {
    /// Given a reference to an `EGraph`, makes a `Dot`.
    pub fn new(egraph: &EGraph<L>) -> Dot<L> {
        Dot { egraph }
    }
}

impl<'a, L: Language> Display for Dot<'a, L> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "digraph {{\n")?;

        // set compound=true to enable edges to clusters
        write!(f, "  compound=true\n")?;

        // define all the nodes, clustered by eclass
        for class in self.egraph.classes() {
            write!(f, "  subgraph cluster_{} {{\n", class.id)?;
            write!(f, "    style=dotted\n")?;
            for (i, node) in class.iter().enumerate() {
                write!(f, "    {}.{}[label = \"{}\"]\n", class.id, i, node.symbol())?;
            }
            write!(f, "  }}\n")?;
        }

        for class in self.egraph.classes() {
            for (i_in_class, node) in class.iter().enumerate() {
                for (arg_i, child) in node.children().iter().enumerate() {
                    // write the edge to the child, but clip it to the eclass with lhead
                    let child_leader = self.egraph.just_find(*child);
                    write!(
                        f,
                        // {}.0 to pick an arbitrary node in the cluster
                        "  {}.{} -> {}.0 [lhead = cluster_{}, label = {}]\n",
                        class.id, i_in_class, child, child_leader, arg_i
                    )?;
                }
            }
        }

        write!(f, "}}")
    }
}
