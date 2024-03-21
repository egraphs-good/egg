/*!
EGraph visualization with [GraphViz]

Use the [`Dot`] struct to visualize an [`EGraph`](crate::EGraph)

[GraphViz]: https://graphviz.gitlab.io/
!*/

use std::ffi::OsStr;
use std::fmt::{self, Debug, Display, Formatter};
use std::io::{Error, ErrorKind, Result, Write};
use std::path::Path;

use crate::{raw::EGraphResidual, Language};

/**
A wrapper for an [`EGraphResidual`] that can output [GraphViz] for
visualization.

The [`EGraphResidual::dot`] method creates `Dot`s.

# Example

```no_run
use egg::{*, rewrite as rw};

let rules = &[
    rw!("mul-commutes"; "(* ?x ?y)" => "(* ?y ?x)"),
    rw!("mul-two";      "(* ?x 2)" => "(<< ?x 1)"),
];

let mut egraph: EGraph<SymbolLang, ()> = Default::default();
egraph.add_expr(&"(/ (* 2 a) 2)".parse().unwrap());
let egraph = Runner::default().with_egraph(egraph).run(rules).egraph;

// Dot implements std::fmt::Display
println!("My egraph dot file: {}", egraph.dot());

// create a Dot and then compile it assuming `dot` is on the system
egraph.dot().to_svg("target/foo.svg").unwrap();
egraph.dot().to_png("target/foo.png").unwrap();
egraph.dot().to_pdf("target/foo.pdf").unwrap();
egraph.dot().to_dot("target/foo.dot").unwrap();
```

Note that self-edges (from an enode to its containing eclass) will be
rendered improperly due to a deficiency in GraphViz.
So the example above will render with an from the "+" enode to itself
instead of to its own eclass.

[GraphViz]: https://graphviz.gitlab.io/
**/
pub struct Dot<'a, L: Language> {
    pub(crate) egraph: &'a EGraphResidual<L>,
    /// A list of strings to be output top part of the dot file.
    pub config: Vec<String>,
    /// Whether or not to anchor the edges in the output.
    /// True by default.
    pub use_anchors: bool,
}

impl<'a, L> Dot<'a, L>
where
    L: Language + Display,
{
    /// Writes the `Dot` to a .dot file with the given filename.
    /// Does _not_ require a `dot` binary.
    pub fn to_dot(&self, filename: impl AsRef<Path>) -> Result<()> {
        let mut file = std::fs::File::create(filename)?;
        write!(file, "{}", self)
    }

    /// Adds a line to the dot output.
    /// Indentation and a newline will be added automatically.
    pub fn with_config_line(mut self, line: impl Into<String>) -> Self {
        self.config.push(line.into());
        self
    }

    /// Set whether or not to anchor the edges in the output.
    pub fn with_anchors(mut self, use_anchors: bool) -> Self {
        self.use_anchors = use_anchors;
        self
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
    /// # let mut egraph: EGraph<SymbolLang, ()> = Default::default();
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

    // gives back the appropriate label and anchor
    fn edge(&self, i: usize, len: usize) -> (String, String) {
        assert!(i < len);
        let s = |s: &str| s.to_string();
        if !self.use_anchors {
            return (s(""), format!("label={}", i));
        }
        match (len, i) {
            (1, 0) => (s(""), s("")),
            (2, 0) => (s(":sw"), s("")),
            (2, 1) => (s(":se"), s("")),
            (3, 0) => (s(":sw"), s("")),
            (3, 1) => (s(":s"), s("")),
            (3, 2) => (s(":se"), s("")),
            (_, _) => (s(""), format!("label={}", i)),
        }
    }
}

impl<'a, L: Language> Debug for Dot<'a, L> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_tuple("Dot").field(self.egraph).finish()
    }
}

impl<'a, L> Display for Dot<'a, L>
where
    L: Language + Display,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        writeln!(f, "digraph egraph {{")?;

        // set compound=true to enable edges to clusters
        writeln!(f, "  compound=true")?;
        writeln!(f, "  clusterrank=local")?;

        for line in &self.config {
            writeln!(f, "  {}", line)?;
        }

        let classes = self.egraph.generate_class_nodes();

        // define all the nodes, clustered by eclass
        for (&id, class) in &classes {
            writeln!(f, "  subgraph cluster_{} {{", id)?;
            writeln!(f, "    style=dotted")?;
            for (i, node) in class.iter().enumerate() {
                writeln!(f, "    {}.{}[label = \"{}\"]", id, i, node)?;
            }
            writeln!(f, "  }}")?;
        }

        for (&id, class) in &classes {
            for (i_in_class, node) in class.iter().enumerate() {
                let mut arg_i = 0;
                node.try_for_each(|child| {
                    // write the edge to the child, but clip it to the eclass with lhead
                    let (anchor, label) = self.edge(arg_i, node.len());
                    let child_leader = self.egraph.find(child);

                    if child_leader == id {
                        writeln!(
                            f,
                            // {}.0 to pick an arbitrary node in the cluster
                            "  {}.{}{} -> {}.{}:n [lhead = cluster_{}, {}]",
                            id, i_in_class, anchor, id, i_in_class, id, label
                        )?;
                    } else {
                        writeln!(
                            f,
                            // {}.0 to pick an arbitrary node in the cluster
                            "  {}.{}{} -> {}.0 [lhead = cluster_{}, {}]",
                            id, i_in_class, anchor, child, child_leader, label
                        )?;
                    }
                    arg_i += 1;
                    Ok(())
                })?;
            }
        }

        write!(f, "}}")
    }
}
