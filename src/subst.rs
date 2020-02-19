use crate::Id;
use indexmap::IndexSet;
use once_cell::sync::Lazy;
use std::str::FromStr;
use std::sync::Mutex;

static STRINGS: Lazy<Mutex<IndexSet<String>>> = Lazy::new(Default::default);

/// A variable for use in [`Pattern`]s or [`Subst`]s.
///
/// This implements [`FromStr`], and will only parse if it has a
/// leading `?`.
///
/// [`Pattern`]: enum.Pattern.html
/// [`Subst`]: struct.Subst.html
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
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

impl std::ops::Index<&Var> for Subst {
    type Output = Id;

    fn index(&self, var: &Var) -> &Self::Output {
        self.get(var).unwrap()
    }
}
