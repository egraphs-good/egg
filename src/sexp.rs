//! Minimal s-expression type.
//!
//! When the `std` feature is enabled, this re-exports from `symbolic_expressions`.
//! In `no_std` mode, a minimal compatible implementation is provided.

#[cfg(feature = "std")]
pub(crate) use symbolic_expressions::{Sexp, SexpError};

#[cfg(not(feature = "std"))]
pub(crate) use self::minimal::*;

#[cfg(not(feature = "std"))]
mod minimal {
    use alloc::fmt;
    use alloc::string::String;
    use alloc::vec::Vec;

    /// A minimal s-expression type compatible with `symbolic_expressions::Sexp`.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum Sexp {
        /// A string atom.
        String(String),
        /// A list of sub-expressions.
        List(Vec<Sexp>),
        /// An empty s-expression.
        Empty,
    }

    impl fmt::Display for Sexp {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Sexp::String(s) => {
                    if s.contains(' ') || s.contains('(') || s.contains(')') || s.is_empty() {
                        write!(f, "\"{}\"", s)
                    } else {
                        write!(f, "{}", s)
                    }
                }
                Sexp::List(items) => {
                    write!(f, "(")?;
                    for (i, item) in items.iter().enumerate() {
                        if i > 0 {
                            write!(f, " ")?;
                        }
                        write!(f, "{}", item)?;
                    }
                    write!(f, ")")
                }
                Sexp::Empty => write!(f, "()"),
            }
        }
    }

    /// Error type for s-expression parsing.
    #[derive(Debug, Clone)]
    pub struct SexpError {
        /// Description of the parse error.
        pub message: String,
    }

    impl fmt::Display for SexpError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "S-expression parse error: {}", self.message)
        }
    }

    impl core::error::Error for SexpError {}

    impl core::str::FromStr for Sexp {
        type Err = SexpError;

        fn from_str(s: &str) -> Result<Self, Self::Err> {
            parse(s)
        }
    }

    fn parse(input: &str) -> Result<Sexp, SexpError> {
        let input = input.trim();
        if input.is_empty() {
            return Err(SexpError {
                message: String::from("empty input"),
            });
        }

        let (sexp, rest) = parse_one(input)?;
        let rest = rest.trim();
        if rest.is_empty() {
            Ok(sexp)
        } else {
            Err(SexpError {
                message: String::from("trailing input"),
            })
        }
    }

    fn parse_one(input: &str) -> Result<(Sexp, &str), SexpError> {
        let input = input.trim_start();
        if input.is_empty() {
            return Err(SexpError {
                message: String::from("unexpected end of input"),
            });
        }

        if input.starts_with('(') {
            let mut rest = &input[1..];
            let mut items = Vec::new();
            loop {
                rest = rest.trim_start();
                if rest.is_empty() {
                    return Err(SexpError {
                        message: String::from("unclosed parenthesis"),
                    });
                }
                if rest.starts_with(')') {
                    rest = &rest[1..];
                    break;
                }
                let (item, new_rest) = parse_one(rest)?;
                items.push(item);
                rest = new_rest;
            }
            if items.is_empty() {
                Ok((Sexp::Empty, rest))
            } else {
                Ok((Sexp::List(items), rest))
            }
        } else if input.starts_with('"') {
            let end = input[1..].find('"').ok_or_else(|| SexpError {
                message: String::from("unclosed string"),
            })? + 1;
            let s = &input[1..end];
            Ok((Sexp::String(String::from(s)), &input[end + 1..]))
        } else {
            let end = input
                .find(|c: char| c.is_whitespace() || c == '(' || c == ')')
                .unwrap_or(input.len());
            let atom = &input[..end];
            Ok((Sexp::String(String::from(atom)), &input[end..]))
        }
    }
}
