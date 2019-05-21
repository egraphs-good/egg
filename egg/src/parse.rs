use std::error::Error;
use std::fmt;
use std::str::FromStr;

use symbolic_expressions::{parser::parse_str, Sexp, SexpError};

use crate::{
    expr::{Expr, Language, RecExpr},
    pattern::{Pattern, Rewrite},
};

#[derive(Debug, Clone)]
pub struct ParseError(String);
pub type Result<T> = std::result::Result<T, ParseError>;

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ParseError: {}", self.0)
    }
}

impl Error for ParseError {
    fn description(&self) -> &str {
        &self.0
    }

    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

impl From<SexpError> for ParseError {
    fn from(e: SexpError) -> ParseError {
        ParseError(e.to_string())
    }
}

fn parse_term<L: ParsableLanguage>(sexp: &Sexp) -> Result<Pattern<L>>
where
    L::Constant: FromStr,
    L::Variable: FromStr,
    L::Operator: FromStr,
    L::Wildcard: FromStr,
{
    match sexp {
        Sexp::String(s) => {
            if s.trim() != s || s.is_empty() {
                panic!("There's whitespace!")
            }
            s.parse::<L::Wildcard>()
                .map(Pattern::Wildcard)
                .or_else(|_| s.parse().map(|c| Pattern::Expr(Expr::Constant(c))))
                .or_else(|_| s.parse().map(|v| Pattern::Expr(Expr::Variable(v))))
                .map_err(|_| ParseError("bad".into()))
        }

        Sexp::List(vec) => {
            assert!(!vec.is_empty());
            let mut sexps = vec.iter();

            let op = match sexps.next().unwrap() {
                Sexp::String(s) => s
                    .parse::<L::Operator>()
                    .map_err(|_| ParseError(format!("bad op: {}", s)))?,
                op_sexp => return Err(ParseError(format!("expected op, got {}", op_sexp))),
            };

            let children: Result<Vec<Pattern<L>>> = sexps.map(|s| parse_term(s)).collect();

            Ok(Pattern::Expr(Expr::Operator(op, children?)))
        }
        Sexp::Empty => Err(ParseError("empty!".into())),
    }
}

pub fn pat_to_expr<L: Language>(pat: Pattern<L>) -> Result<RecExpr<L>> {
    match pat {
        Pattern::Wildcard(w) => Err(ParseError(format!(
            "Found wildcard {:?} instead of expr term",
            w
        ))),
        Pattern::Expr(e) => Ok(e.map_children_result(pat_to_expr)?.into()),
    }
}

/// A trait to parse stuff from a `Langauge`.
///
/// This is blanket-impled for any `Langauge` whose domains all
/// implement [`FromStr`]. [`TestLang`] is a parsable langauge.
///
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
/// [`TestLang`]: ../expr/tests/struct.TestLang.html
pub trait ParsableLanguage: Language
where
    Self::Constant: FromStr,
    Self::Variable: FromStr,
    Self::Operator: FromStr,
    Self::Wildcard: FromStr,
{
    fn parse_pattern(&self, s: &str) -> Result<Pattern<Self>> {
        let sexp = parse_str(s.trim())?;
        parse_term(&sexp)
    }

    fn parse_rewrite(&self, name: &str, lhs: &str, rhs: &str) -> Result<Rewrite<Self>> {
        Ok(Rewrite {
            name: name.into(),
            lhs: self.parse_pattern(lhs)?,
            rhs: self.parse_pattern(rhs)?,
        })
    }

    fn parse_expr(&self, s: &str) -> Result<RecExpr<Self>> {
        let pat = self.parse_pattern(s)?;
        pat_to_expr(pat)
    }
}

impl<L: Language> ParsableLanguage for L
where
    Self::Constant: FromStr,
    Self::Variable: FromStr,
    Self::Operator: FromStr,
    Self::Wildcard: FromStr,
{
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::expr::tests::{op, var, TestLang};

    #[test]
    fn simple_parse() {
        let expr: RecExpr<TestLang> = op("+", vec![var("x").into(), var("x").into()]).into();

        let expr2 = TestLang.parse_expr("(+ x x)").unwrap();

        assert_eq!(expr, expr2);
    }
}
