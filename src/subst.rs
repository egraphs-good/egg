use crate::Id;
use std::str::FromStr;

/// A variable for use in [`Pattern`]s or [`Subst`]s.
///
/// This implements [`FromStr`].
///
/// [`Pattern`]: enum.Pattern.html
/// [`Subst`]: struct.Subst.html
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Var(String);

/// A substitition mapping [`Var`]s to eclass [`Id`]s.
///
/// [`Var`]: struct.Var.html
/// [`Id`]: type.Id.html
#[derive(Debug, Default, Clone)]
pub struct Subst {
    vec: smallvec::SmallVec<[(Var, Id); 3]>,
}

impl Subst {
    pub(crate) fn singleton(var: Var, id: Id) -> Self {
        let mut subst = Self::default();
        subst.insert(var, id);
        subst
    }

    pub(crate) fn insert(&mut self, var: Var, id: Id) -> Option<Id> {
        for pair in &mut self.vec {
            if pair.0 == var {
                return Some(std::mem::replace(&mut pair.1, id));
            }
        }
        self.vec.push((var, id));
        None
    }

    pub(crate) fn get(&self, var: &Var) -> Option<&Id> {
        self.vec
            .iter()
            .find_map(|(v, id)| if v == var { Some(id) } else { None })
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&Var, &Id)> {
        self.vec.iter().map(|pair| (&pair.0, &pair.1))
    }
}

impl FromStr for Var {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with('?') {
            Ok(Var(s.to_owned()))
        } else {
            Err(format!("{} doesn't start with '?'", s))
        }
    }
}

impl std::ops::Index<&Var> for Subst {
    type Output = Id;

    fn index(&self, var: &Var) -> &Self::Output {
        self.get(var).unwrap()
    }
}
