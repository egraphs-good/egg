use std::fmt;
use std::str::FromStr;

use crate::*;
use fmt::{Debug, Display, Formatter};
use thiserror::Error;

/// A variable for use in [`Pattern`]s or [`Subst`]s.
///
/// This implements [`FromStr`], and will only parse if it has a
/// leading `?`.
///
/// [`FromStr`]: std::str::FromStr
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(Symbol);

#[derive(Debug, Error)]
pub enum VarParseError {
    #[error("pattern variable {0:?} should have a leading question mark")]
    MissingQuestionMark(String),
}

impl FromStr for Var {
    type Err = VarParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use VarParseError::*;

        if s.starts_with('?') && s.len() > 1 {
            Ok(Var(s.into()))
        } else {
            Err(MissingQuestionMark(s.to_owned()))
        }
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl Debug for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

/// A substitution mapping [`Var`]s to eclass [`Id`]s.
///
#[derive(Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Subst {
    pub(crate) vec: smallvec::SmallVec<[(Var, Id); 3]>,
}

impl Subst {
    /// Create a `Subst` with the given initial capacity
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            vec: smallvec::SmallVec::with_capacity(capacity),
        }
    }

    /// Insert something, returning the old `Id` if present.
    pub fn insert(&mut self, var: Var, id: Id) -> Option<Id> {
        for pair in &mut self.vec {
            if pair.0 == var {
                return Some(std::mem::replace(&mut pair.1, id));
            }
        }
        self.vec.push((var, id));
        None
    }

    /// Retrieve a `Var`, returning `None` if not present.
    #[inline(never)]
    pub fn get(&self, var: Var) -> Option<&Id> {
        self.vec
            .iter()
            .find_map(|(v, id)| if *v == var { Some(id) } else { None })
    }
}

impl std::ops::Index<Var> for Subst {
    type Output = Id;

    fn index(&self, var: Var) -> &Self::Output {
        match self.get(var) {
            Some(id) => id,
            None => panic!("Var '{}={}' not found in {:?}", var.0, var, self),
        }
    }
}

impl Debug for Subst {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let len = self.vec.len();
        write!(f, "{{")?;
        for i in 0..len {
            let (var, id) = &self.vec[i];
            write!(f, "{}: {}", var, id)?;
            if i < len - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn var_parse() {
        assert_eq!(Var::from_str("?a").unwrap().to_string(), "?a");
        assert_eq!(Var::from_str("?abc 123").unwrap().to_string(), "?abc 123");
        assert!(Var::from_str("a").is_err());
        assert!(Var::from_str("a?").is_err());
        assert!(Var::from_str("?").is_err());
    }
}
