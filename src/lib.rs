/*!
[`EGraph`]s (and almost everything else in this crate) are
parameterized over the language given by the user (by implementing
the [`Language`] trait).

A typical usage would either implement [`Language`] or use the
provided [`TestLang`]. From there, you can use the functionality
from the [`ParsableLanguage`] trait module to create expressions
and add them to the EGraph.

[`EGraph`]: egraph/struct.EGraph.html
[`Language`]: expr/trait.Language.html
[`TestLang`]: expr/tests/struct.TestLang.html
[`ParsableLanguage`]: parse/trait.ParsableLanguage.html

```
use egg::*;

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
    rw("commute-add").p("(+ ?a ?b)").a("(+ ?b ?a)").mk(),
    rw("commute-mul").p("(* ?a ?b)").a("(* ?b ?a)").mk(),

    rw("add-0").p("(+ ?a 0)").a("?a").mk(),
    rw("mul-0").p("(* ?a 0)").a("0").mk(),
    rw("mul-1").p("(* ?a 1)").a("?a").mk(),
];

let start = SimpleLanguage::parse_expr("(+ 0 (* 1 foo))").unwrap();

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
pub use egraph::{AddResult, EGraph};
pub use expr::{
    tests::{op, var, TestLang},
    ENode, Expr, Id, Language, Name, QuestionMarkName, RecExpr,
};
pub use extract::*;
pub use parse::{ParsableLanguage, ParseError};
pub use pattern::{EClassMatches, Pattern, WildMap};
pub use rewrite::{rw, Applier, Rewrite};
pub use run::*;

#[cfg(test)]
fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
}
