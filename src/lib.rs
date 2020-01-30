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
use egg::{
    define_language,
    rewrite::{rw, Rewrite},
    parse::ParsableLanguage,
    run::{Runner, SimpleRunner},
};

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

mod unionfind;

pub mod dot;
pub mod egraph;
pub mod expr;
pub mod extract;
pub mod parse;
pub mod pattern;
pub mod rewrite;
pub mod run;

#[cfg(test)]
fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
}
