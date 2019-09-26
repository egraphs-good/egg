//!
//! [`EGraph`]s (and almost everything else in this crate) are
//! parameterized over the language given by the user (by implementing
//! the [`Language`] trait).
//!
//! A typical usage would either implement [`Language`] or use the
//! provided [`TestLang`]. From there, you can use the functionality
//! from the [`ParsableLanguage`] trait module to create expressions
//! and add them to the EGraph.
//!
//! [`EGraph`]: egraph/struct.EGraph.html
//! [`Language`]: expr/trait.Language.html
//! [`TestLang`]: expr/tests/struct.TestLang.html
//! [`ParsableLanguage`]: parse/trait.ParsableLanguage.html

mod macros;

mod unionfind;

pub mod dot;
pub mod egraph;
pub mod expr;
pub mod extract;
pub mod parse;
pub mod pattern;

#[cfg(test)]
fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
}
