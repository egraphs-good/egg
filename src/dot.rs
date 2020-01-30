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
//! let mut egraph = EGraph::<TestLang, ()>::default();
//! let x = egraph.add(var("x"));
//! let y = egraph.add(var("y"));
//! egraph.add(op("+", vec![x.id, y.id]));
//!
//! // create a `Dot` and then compile it assuming `dot` is on the system
//! egraph.dot().to_svg("target/doc/foo.svg").unwrap();
//! ```
//!
//! [`EGraph`]: ../egraph/struct.EGraph.html
//! [GraphViz]: https://graphviz.gitlab.io/

use std::ffi::OsStr;
use std::fmt::{self, Display, Formatter};
use std::io::{Error, ErrorKind, Result, Write};
use std::path::Path;

use crate::{egraph::EGraph, expr::Language};

/// A wrapper for an [`EGraph`] that implements `Display` so you can
/// print it.
///
/// [`EGraph`]: ../egraph/struct.EGraph.html
pub struct Dot<'a, L, M> {
    egraph: &'a EGraph<L, M>,
}

impl<'a, L, M> Dot<'a, L, M> {
    /// Given a reference to an `EGraph`, makes a `Dot`.
    pub fn new(egraph: &EGraph<L, M>) -> Dot<L, M> {
        Dot { egraph }
    }
}

impl<'a, L: Language + Display, M> Dot<'a, L, M> {
    pub fn to_png(&self, filename: impl AsRef<Path>) -> Result<()> {
        self.run_dot(&["-Tpng".as_ref(), "-o".as_ref(), filename.as_ref()])
    }

    pub fn to_svg(&self, filename: impl AsRef<Path>) -> Result<()> {
        self.run_dot(&["-Tsvg".as_ref(), "-o".as_ref(), filename.as_ref()])
    }

    pub fn to_pdf(&self, filename: impl AsRef<Path>) -> Result<()> {
        self.run_dot(&["-Tpdf".as_ref(), "-o".as_ref(), filename.as_ref()])
    }

    pub fn to_dot(&self, filename: impl AsRef<Path>) -> Result<()> {
        let mut file = std::fs::File::create(filename)?;
        write!(file, "{}", self)?;
        Ok(())
    }

    pub fn run_dot<S, I>(&self, args: I) -> Result<()>
    where
        S: AsRef<OsStr>,
        I: IntoIterator<Item = S>,
    {
        self.run("dot", args)
    }

    pub fn run<S1, S2, I>(&self, program: S1, args: I) -> Result<()>
    where
        S1: AsRef<OsStr>,
        S2: AsRef<OsStr>,
        I: IntoIterator<Item = S2>,
    {
        use std::process::{Command, Stdio};
        let mut child = Command::new(program)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .spawn()?;
        let stdin = child.stdin.as_mut().expect("Failed to open stdin");
        write!(stdin, "{}", self)?;
        match child.wait()?.code() {
            Some(0) => Ok(()),
            Some(e) => Err(Error::new(
                ErrorKind::Other,
                format!("dot program returned error code {}", e),
            )),
            None => Err(Error::new(
                ErrorKind::Other,
                "dot program was killed by a signal",
            )),
        }
    }
}

impl<'a, L: Language + Display, M> Display for Dot<'a, L, M> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        writeln!(f, "digraph egraph {{")?;

        // set compound=true to enable edges to clusters
        writeln!(f, "  compound=true")?;

        // define all the nodes, clustered by eclass
        for class in self.egraph.classes() {
            writeln!(f, "  subgraph cluster_{} {{", class.id)?;
            writeln!(f, "    style=dotted")?;
            for (i, node) in class.iter().enumerate() {
                writeln!(f, "    {}.{}[label = \"{}\"]", class.id, i, node.op)?;
            }
            writeln!(f, "  }}")?;
        }

        for class in self.egraph.classes() {
            for (i_in_class, node) in class.iter().enumerate() {
                for (arg_i, child) in node.children.iter().enumerate() {
                    // write the edge to the child, but clip it to the eclass with lhead
                    let child_leader = self.egraph.find(*child);
                    writeln!(
                        f,
                        // {}.0 to pick an arbitrary node in the cluster
                        "  {}.{} -> {}.0 [lhead = cluster_{}, label = {}]",
                        class.id, i_in_class, child, child_leader, arg_i
                    )?;
                }
            }
        }

        write!(f, "}}")
    }
}
