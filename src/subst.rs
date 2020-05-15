use crate::Id;
use indexmap::IndexSet;
use once_cell::sync::Lazy;

use std::fmt;
use std::str::FromStr;
use std::sync::Mutex;

static STRINGS: Lazy<Mutex<IndexSet<String>>> = Lazy::new(Default::default);

/// A variable for use in [`Pattern`]s or [`Subst`]s.
///
/// This implements [`FromStr`], and will only parse if it has a
/// leading `?`.
///
/// [`Pattern`]: struct.Pattern.html
/// [`Subst`]: struct.Subst.html
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(u32);

impl FromStr for Var {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with('?') {
            let mut strings = STRINGS.lock().unwrap();
            let (i, _) = strings.insert_full(s.to_owned());
            Ok(Var(i as u32))
        } else {
            Err(format!("{} doesn't start with '?'", s))
        }
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let i = self.0 as usize;
        let strings = STRINGS.lock().unwrap();
        let s = strings.get_index(i).unwrap();
        write!(f, "{}", s)
    }
}

/// A substitition mapping [`Var`]s to eclass [`Id`]s.
///
/// [`Var`]: struct.Var.html
/// [`Id`]: type.Id.html
#[derive(Debug, Default, Clone)]
pub struct Subst {
    vec: smallvec::SmallVec<[(Var, Id); 3]>,
}

impl Subst {
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
    pub fn get(&self, var: &Var) -> Option<&Id> {
        self.vec
            .iter()
            .find_map(|(v, id)| if v == var { Some(id) } else { None })
    }
}

impl std::ops::Index<&Var> for Subst {
    type Output = Id;

    fn index(&self, var: &Var) -> &Self::Output {
        match self.get(var) {
            Some(id) => id,
            None => panic!("Var '{}={}' not found in {:?}", var.0, var, self),
        }
    }
}
