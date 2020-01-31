/*!
EGraph visualization with [GraphViz]

Use the [`Dot`] struct to visualize an [`EGraph`]

[`Dot`]: struct.Dot.html
[`EGraph`]: ../egraph/struct.EGraph.html
[GraphViz]: https://graphviz.gitlab.io/
!*/

use std::ffi::OsStr;
use std::fmt::{self, Debug, Display, Formatter};
use std::io::{Error, ErrorKind, Result, Write};
use std::path::Path;

use crate::{egraph::EGraph, expr::Language};

/**
A wrapper for an [`EGraph`] that can output [GraphViz] for
visualization.

# Example

```
use egg::{EGraph, TestLang, var, op};

let mut egraph = EGraph::<TestLang, ()>::default();
let x = egraph.add(var("x")).id;
let y = egraph.add(var("0")).id;
let add = egraph.add(op("+", vec![x, y])).id;
egraph.union(add, x);
egraph.rebuild();

// create a Dot and dump it to a file
egraph.dot().to_png("target/foo.dot").unwrap();

// Dot implements std::fmt::Display
println!("My egraph dot file: {}", egraph.dot());

// create a Dot and then compile it assuming `dot` is on the system
egraph.dot().to_svg("target/foo.svg").unwrap();
egraph.dot().to_png("target/foo.png").unwrap();
egraph.dot().to_pdf("target/foo.pdf").unwrap();
```

Note that self-edges (from an enode to its containing eclass) will be
rendered improperly due to a deficiency in GraphViz.
So the example above will render with an from the "+" enode to itself
instead of to its own eclass.

[`EGraph`]: ../egraph/struct.EGraph.html
[GraphViz]: https://graphviz.gitlab.io/
**/
pub struct Dot<'a, L, M> {
    egraph: &'a EGraph<L, M>,
}

impl<'a, L, M> Dot<'a, L, M> {
    /// Given a reference to an `EGraph`, makes a `Dot`.
    /// See also the more convenient
    /// [`EGraph::dot`](../egraph/struct.EGraph.html#method.dot).
    pub fn new(egraph: &EGraph<L, M>) -> Dot<L, M> {
        Dot { egraph }
    }
}

impl<'a, L: Language + Display, M> Dot<'a, L, M> {
    /// Writes the `Dot` to a .dot file with the given filename.
    /// Does _not_ require a `dot` binary.
    pub fn to_dot(&self, filename: impl AsRef<Path>) -> Result<()> {
        let mut file = std::fs::File::create(filename)?;
        write!(file, "{}", self)?;
        Ok(())
    }

    /// Renders the `Dot` to a .png file with the given filename.
    /// Requires a `dot` binary to be on your `$PATH`.
    pub fn to_png(&self, filename: impl AsRef<Path>) -> Result<()> {
        self.run_dot(&["-Tpng".as_ref(), "-o".as_ref(), filename.as_ref()])
    }

    /// Renders the `Dot` to a .svg file with the given filename.
    /// Requires a `dot` binary to be on your `$PATH`.
    pub fn to_svg(&self, filename: impl AsRef<Path>) -> Result<()> {
        self.run_dot(&["-Tsvg".as_ref(), "-o".as_ref(), filename.as_ref()])
    }

    /// Renders the `Dot` to a .pdf file with the given filename.
    /// Requires a `dot` binary to be on your `$PATH`.
    pub fn to_pdf(&self, filename: impl AsRef<Path>) -> Result<()> {
        self.run_dot(&["-Tpdf".as_ref(), "-o".as_ref(), filename.as_ref()])
    }

    /// Invokes `dot` with the given arguments, piping this formatted
    /// `Dot` into stdin.
    pub fn run_dot<S, I>(&self, args: I) -> Result<()>
    where
        S: AsRef<OsStr>,
        I: IntoIterator<Item = S>,
    {
        self.run("dot", args)
    }

    /// Invokes some program with the given arguments, piping this
    /// formatted `Dot` into stdin.
    ///
    /// Can be used to run a different binary than `dot`:
    /// ```no_run
    /// # use egg::*;
    /// # let egraph = EGraph::<TestLang, ()>::default();
    /// egraph.dot().run(
    ///     "/path/to/my/dot",
    ///     &["arg1", "-o", "outfile"]
    /// ).unwrap();
    /// ```
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

impl<'a, L: Language, M: Debug> Debug for Dot<'a, L, M> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "Dot({:?})", self.egraph)
    }
}

impl<'a, L: Language + Display, M> Display for Dot<'a, L, M> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        writeln!(f, "digraph egraph {{")?;

        // set compound=true to enable edges to clusters
        writeln!(f, "  compound=true")?;
        writeln!(f, "  clusterrank=local")?;

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

                    if child_leader == class.id {
                        writeln!(
                            f,
                            // {}.0 to pick an arbitrary node in the cluster
                            "  {}.{} -> {}.{}:n [lhead = cluster_{}, label = {}]",
                            class.id, i_in_class, class.id, i_in_class, class.id, arg_i
                        )?;
                    } else {
                        writeln!(
                            f,
                            // {}.0 to pick an arbitrary node in the cluster
                            "  {}.{} -> {}.0 [lhead = cluster_{}, label = {}]",
                            class.id, i_in_class, child, child_leader, arg_i
                        )?;
                    }
                }
            }
        }

        write!(f, "}}")
    }
}
