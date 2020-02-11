/*!
[`EGraph`]s (and almost everything else in this crate) are
parameterized over the language given by the user (by implementing
the [`Language`] trait).

If your Language implements [`FromStr`] (and Languages derived using
[`define_language!`] do), you can easily create [`RecExpr`]s to add to
an [`EGraph`].

[`EGraph`]: struct.EGraph.html
[`Language`]: trait.Language.html
[`RecExpr`]: struct.RecExpr.html
[`define_language!`]: macro.define_language.html
[`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html

Add `egg` to your `Cargo.toml` like this:
```toml
[dependencies]
egg = "0.0.0"
```

```
use egg::{*, rewrite as rw};

define_language! {
    enum SimpleLanguage {
        Num(i32),
        Add = "+",
        Mul = "*",
        // language items are parsed in order, and we want symbol to
        // be a fallback, so we put it last
        Symbol(String),
    }
}

let rules: &[Rewrite<SimpleLanguage, ()>] = &[
    rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
    rw!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),

    rw!("add-0"; "(+ ?a 0)" => "?a"),
    rw!("mul-0"; "(* ?a 0)" => "0"),
    rw!("mul-1"; "(* ?a 1)" => "?a"),
];

let start = "(+ 0 (* 1 foo))".parse().unwrap();
let (egraph, report) = SimpleRunner::default().run_expr(start, &rules);
println!(
    "Stopped after {} iterations, reason: {:?}",
    report.iterations.len(),
    report.stop_reason
);
```
!*/

mod macros;

pub(crate) mod unionfind;

mod dot;
mod eclass;
mod egraph;
mod expr;
mod extract;
mod parse;
mod pattern;
mod rewrite;
mod run;

pub use dot::Dot;
pub use eclass::{EClass, Metadata};
pub use egraph::EGraph;
pub use expr::{ENode, Id, Language, QuestionMarkName, RecExpr};
pub use extract::*;
pub use parse::ParseError;
pub use pattern::{Pattern, SearchMatches, WildMap};
pub use rewrite::{Applier, Condition, ConditionEqual, ConditionalApplier, Rewrite, Searcher};
pub use run::*;

#[cfg(test)]
fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
}

#[cfg(test)]
use std::path::{Path, PathBuf};
#[cfg(test)]
fn tmp(filename: impl AsRef<Path>) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(filename);
    path
}
