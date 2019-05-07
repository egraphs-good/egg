use std::error::Error;
use std::fmt;
use std::str::FromStr;

use symbolic_expressions::{parser::parse_str, Sexp, SexpError};

use crate::{
    expr::{Expr, FlatExpr, Id, Language},
    pattern::{FlatPattern, Pattern, Rewrite},
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

struct Parser<L: Language> {
    pattern: FlatPattern<L>,
}

impl<L: Language> Parser<L>
where
    L::Constant: FromStr,
    L::Variable: FromStr,
    L::Operator: FromStr,
    L::Wildcard: FromStr,
{
    fn new() -> Parser<L> {
        Parser {
            pattern: FlatPattern::default(),
        }
    }

    fn parse_term(&mut self, sexp: &Sexp) -> Result<Id> {
        match sexp {
            Sexp::String(s) => {
                if s.trim() != s || s.is_empty() {
                    panic!("There's whitespace!")
                }
                s.parse::<L::Wildcard>()
                    .map(Pattern::Wildcard)
                    .or_else(|_| s.parse().map(|c| Pattern::Expr(Expr::Constant(c))))
                    .or_else(|_| s.parse().map(|v| Pattern::Expr(Expr::Variable(v))))
                    .map(|p| self.pattern.add(p))
                    .map_err(|_| ParseError("bad".into()))
            }

            Sexp::List(vec) => {
                assert!(vec.len() > 0);
                let mut sexps = vec.iter();

                let op = match sexps.next().unwrap() {
                    Sexp::String(s) => s
                        .parse::<L::Operator>()
                        .map_err(|_| ParseError(format!("bad op: {}", s)))?,
                    op_sexp => return Err(ParseError(format!("expected op, got {}", op_sexp))),
                };

                let children: Result<Vec<Id>> = sexps.map(|s| self.parse_term(s)).collect();

                let pat = Pattern::Expr(Expr::Operator(op, children?));
                Ok(self.pattern.add(pat))
            }
            Sexp::Empty => panic!(),
        }
    }
}

pub trait ParsableLanguage: Language
where
    Self::Constant: FromStr,
    Self::Variable: FromStr,
    Self::Operator: FromStr,
    Self::Wildcard: FromStr,
{
    fn parse_pattern(&self, s: &str) -> Result<FlatPattern<Self>> {
        let sexp = parse_str(s.trim())?;
        let mut parser = Parser::new();
        parser.pattern.root = parser.parse_term(&sexp)?;
        assert!(parser.pattern.nodes.len() > 0);
        Ok(parser.pattern)
    }

    fn parse_rewrite(&self, name: &str, lhs: &str, rhs: &str) -> Result<Rewrite<Self>> {
        Ok(Rewrite {
            name: name.into(),
            lhs: self.parse_pattern(lhs)?,
            rhs: self.parse_pattern(rhs)?,
        })
    }

    fn parse_expr(&self, s: &str) -> Result<FlatExpr<Self>> {
        let pat = self.parse_pattern(s)?;

        let expr_nodes: Result<Vec<_>> = pat
            .nodes
            .into_iter()
            .map(|p| match p {
                Pattern::Wildcard(w) => Err(ParseError(format!(
                    "Found wildcard {:?} instead of expr term",
                    w
                ))),
                Pattern::Expr(e) => Ok(e),
            })
            .collect();

        Ok(FlatExpr {
            root: pat.root,
            nodes: expr_nodes?,
        })
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
        let mut expr = FlatExpr::default();

        // SimpleExpr doesn't do hashcons
        let a = expr.add(var("x"));
        let b = expr.add(var("x"));
        expr.root = expr.add(op("+", vec![a, b]));

        let expr2 = TestLang.parse_expr("(+ x x)").unwrap();

        assert_eq!(expr, expr2);
    }
}
