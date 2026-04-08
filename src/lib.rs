#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]
#![allow(clippy::test_attr_in_doctest)]
/*!

`egg` (**e**-**g**raphs **g**ood) is a e-graph library optimized for equality saturation.

This is the API documentation.

The [tutorial](tutorials) is a good starting point if you're new to
e-graphs, equality saturation, or Rust.

The [tests](https://github.com/egraphs-good/egg/tree/main/tests)
on Github provide some more elaborate examples.

There is also a [paper](https://arxiv.org/abs/2004.03082)
describing `egg` and some of its technical novelties.

## Logging

Many parts of `egg` dump useful logging info using the [`log`](https://docs.rs/log/) crate.
The easiest way to see this info is to use the [`env_logger`](https://docs.rs/env_logger/)
crate in your binary or test.
The simplest way to enable `env_logger` is to put the following line near the top of your `main`:
`env_logger::init();`.
Then, set the environment variable `RUST_LOG=egg=info`, or use `warn` or `debug` instead of info
for less or more logging.

*/
#![doc = "## Simple Example\n```"]
#![doc = include_str!("../tests/simple.rs")]
#![doc = "\n```"]

extern crate alloc;

/// Crate-internal prelude that re-exports `alloc` / `core` items normally
/// provided by `std`.  Every module imports `use crate::no_std_prelude::*;`
/// instead of scattering `#[allow(unused_imports)] use alloc::{…}` blocks.
pub(crate) mod no_std_prelude {
    pub use alloc::{
        borrow::{Cow, ToOwned},
        boxed::Box,
        collections::{BinaryHeap, VecDeque},
        format,
        rc::Rc,
        string::{String, ToString},
        sync::Arc,
        vec,
        vec::Vec,
    };
}

// Hidden re-exports used by the `define_language!` macro so downstream crates
// don't need `extern crate alloc`.
#[doc(hidden)]
pub mod __private {
    pub use alloc::{format, string::ToString, vec, vec::Vec};
    pub use core::result::Result;
}

mod macros;

#[cfg(feature = "std")]
#[doc(hidden)]
pub mod test;

pub mod tutorials;

#[cfg(feature = "std")]
mod dot;
mod eclass;
mod egraph;
mod explain;
mod extract;
mod language;
#[cfg(feature = "lp")]
mod lp_extract;
mod machine;
mod multipattern;
mod pattern;
mod rewrite;
mod run;
mod sexp;
mod subst;
mod unionfind;
mod util;

/// A key to identify [`EClass`]es within an
/// [`EGraph`].
#[derive(Clone, Copy, Default, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde-1", serde(transparent))]
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

impl core::fmt::Debug for Id {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl core::fmt::Display for Id {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub(crate) use {explain::Explain, unionfind::UnionFind};

pub use {
    eclass::EClass,
    egraph::{EGraph, LanguageMapper, SimpleLanguageMapper},
    explain::{
        Explanation, FlatExplanation, FlatTerm, Justification, TreeExplanation, TreeTerm,
        UnionEqualities,
    },
    extract::*,
    language::*,
    multipattern::*,
    pattern::{ENodeOrVar, Pattern, PatternAst, SearchMatches},
    rewrite::{Applier, Condition, ConditionEqual, ConditionalApplier, Rewrite, Searcher},
    run::*,
    subst::{Subst, Var},
    util::*,
};

#[cfg(feature = "std")]
pub use dot::Dot;

#[cfg(feature = "lp")]
pub use lp_extract::*;

#[cfg(all(test, feature = "std"))]
fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
}
