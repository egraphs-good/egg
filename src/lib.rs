#![warn(missing_docs)]
/*!

`egg` (**e**-**g**raphs **g**ood) is a e-graph library optimized for equality saturation.

This is the API documentation.

The [tutorial](tutorials/index.html) is a good starting point if you're new to
e-graphs, equality saturation, or Rust.

The [tests](https://github.com/mwillsey/egg/tree/master/tests)
on Github provide some more elaborate examples.

There is also a [paper](https://arxiv.org/abs/2004.03082)
describing `egg` and some of its technical novelties.

!*/

mod macros;

pub mod tutorials;

mod dot;
mod eclass;
mod egraph;
mod extract;
mod language;
mod machine;
mod pattern;
mod rewrite;
mod run;
mod subst;
mod unionfind;
mod util;

/// A key to identify [`EClass`](struct.EClass.html)es within an
/// [`EGraph`](struct.EGraph.html).
#[derive(Clone, Copy, Default, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Id(u32);

impl From<usize> for Id {
    fn from(n: usize) -> Id {
        Id(n as u32)
    }
}

impl From<Id> for usize {
    fn from(id: Id) -> usize {
        id.0 as usize
    }
}

impl std::fmt::Debug for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::fmt::Display for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub(crate) use unionfind::UnionFind;

pub use {
    dot::Dot,
    eclass::EClass,
    egraph::EGraph,
    extract::*,
    language::*,
    pattern::{ENodeOrVar, Pattern, PatternAst, SearchMatches},
    rewrite::{Applier, Condition, ConditionEqual, ConditionalApplier, Rewrite, Searcher},
    run::*,
    subst::{Subst, Var},
    util::*,
};

#[cfg(test)]
fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
}

#[doc(hidden)]
pub mod test;
