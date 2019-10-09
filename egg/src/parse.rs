use std::error::Error;
use std::fmt;
use std::str::FromStr;

use symbolic_expressions::{parser::parse_str, Sexp, SexpError};

use crate::{
    egraph::Metadata,
    expr::{Expr, Language, QuestionMarkName, RecExpr},
    pattern::{Pattern, Rewrite, WildcardKind},
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
    L: FromStr,
{
    match sexp {
        Sexp::String(s) => {
            if s.trim() != s || s.is_empty() {
                panic!("There's whitespace!")
            }
            s.parse::<QuestionMarkName>()
                .map(|q| {
                    let kind = if q.as_ref().ends_with("...") {
                        WildcardKind::ZeroOrMore
                    } else {
                        WildcardKind::Single
                    };
                    Pattern::Wildcard(q, kind)
                })
                .or_else(|_| s.parse().map(|t| Pattern::Expr(Box::new(Expr::unit(t)))))
                .map_err(|_| ParseError(format!("Couldn't parse '{}'", s)))
        }

        Sexp::List(vec) => {
            assert!(!vec.is_empty());
            let mut sexps = vec.iter();

            let op = match sexps.next().unwrap() {
                Sexp::String(s) => s
                    .parse::<L>()
                    .map_err(|_| ParseError(format!("bad op: {}", s)))?,
                op_sexp => return Err(ParseError(format!("expected op, got {}", op_sexp))),
            };

            let children: Result<Vec<Pattern<L>>> = sexps.map(|s| parse_term(s)).collect();

            Ok(Pattern::Expr(Expr::new(op, children?.into()).into()))
        }
        Sexp::Empty => Err(ParseError("empty!".into())),
    }
}

pub fn pat_to_expr<L: Language>(pat: Pattern<L>) -> Result<RecExpr<L>> {
    match pat {
        Pattern::Wildcard(w, _) => Err(ParseError(format!(
            "Found wildcard {:?} instead of expr term",
            w
        ))),
        Pattern::Expr(e) => Ok(e.map_children_result(pat_to_expr)?.into()),
    }
}

/// A trait to parse stuff from a `Language`.
///
/// This is blanket-impled for any `Language` whose domains all
/// implement [`FromStr`]. [`TestLang`] is a parsable language.
///
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
/// [`TestLang`]: ../expr/tests/struct.TestLang.html
pub trait ParsableLanguage: Language
where
    Self: FromStr,
{
    fn parse_pattern(s: &str) -> Result<Pattern<Self>> {
        let sexp = parse_str(s.trim())?;
        parse_term(&sexp)
    }

    fn parse_rewrite<M: Metadata<Self>>(
        name: &str,
        lhs: &str,
        rhs: &str,
    ) -> Result<Rewrite<Self, M>> {
        Ok(Rewrite::simple_rewrite(
            name,
            Self::parse_pattern(lhs)?,
            Self::parse_pattern(rhs)?,
        ))
    }

    fn parse_expr(s: &str) -> Result<RecExpr<Self>> {
        let pat = Self::parse_pattern(s)?;
        pat_to_expr(pat)
    }
}

impl<L: Language> ParsableLanguage for L where Self: FromStr {}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::expr::tests::{op, var, TestLang};

    #[test]
    fn simple_parse() {
        let expr: RecExpr<TestLang> = op("+", vec![var("x").into(), var("x").into()]);

        let expr2 = TestLang::parse_expr("(+ x x)").unwrap();

        assert_eq!(expr, expr2);
    }
}
