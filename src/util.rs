use std::{fmt, iter::FromIterator};
use symbolic_expressions::Sexp;

use fmt::{Debug, Display, Formatter};

#[cfg(feature = "serde-1")]
use ::serde::{Deserialize, Serialize};

#[allow(unused_imports)]
use crate::*;

/// An interned string.
///
/// This is provided by the [`symbol_table`](https://crates.io/crates/symbol_table) crate.
///
/// Internally, `egg` frequently compares [`Var`]s and elements of
/// [`Language`]s. To keep comparisons fast, `egg` provides [`Symbol`] a simple
/// wrapper providing interned strings.
///
/// You may wish to use [`Symbol`] in your own [`Language`]s to increase
/// performance and keep enode sizes down (a [`Symbol`] is only 4 bytes,
/// compared to 24 for a `String`.)
///
/// A [`Symbol`] is simply a wrapper around an integer.
/// When creating a [`Symbol`] from a string, `egg` looks up it up in a global
/// table, returning the index (inserting it if not found).
/// That integer is used to cheaply implement
/// `Copy`, `Clone`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, and `Hash`.
///
/// The internal symbol cache leaks the strings, which should be
/// fine if you only put in things like variable names and identifiers.
///
/// # Example
/// ```rust
/// use egg::Symbol;
///
/// assert_eq!(Symbol::from("foo"), Symbol::from("foo"));
/// assert_eq!(Symbol::from("foo"), "foo".parse().unwrap());
///
/// assert_ne!(Symbol::from("foo"), Symbol::from("bar"));
/// ```
///
pub use symbol_table::GlobalSymbol as Symbol;

pub(crate) type BuildHasher = fxhash::FxBuildHasher;

// pub(crate) type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasher>;
// pub(crate) type HashSet<K> = hashbrown::HashSet<K, BuildHasher>;

pub(crate) use hashmap::*;

#[cfg(feature = "deterministic")]
mod hashmap {
    pub(crate) type HashMap<K, V> = super::IndexMap<K, V>;
    pub(crate) type HashSet<K> = super::IndexSet<K>;
}
#[cfg(not(feature = "deterministic"))]
mod hashmap {
    use super::BuildHasher;
    pub(crate) type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasher>;
    pub(crate) type HashSet<K> = hashbrown::HashSet<K, BuildHasher>;
}

pub(crate) fn hashmap_with_capacity<K, V>(cap: usize) -> hashmap::HashMap<K, V> {
    hashmap::HashMap::with_capacity_and_hasher(cap, <_>::default())
}

pub(crate) type IndexMap<K, V> = indexmap::IndexMap<K, V, BuildHasher>;
pub(crate) type IndexSet<K> = indexmap::IndexSet<K, BuildHasher>;

pub(crate) type Instant = quanta::Instant;
pub(crate) type Duration = std::time::Duration;

pub(crate) fn concat_vecs<T>(to: &mut Vec<T>, mut from: Vec<T>) {
    if to.len() < from.len() {
        std::mem::swap(to, &mut from)
    }
    to.extend(from);
}

pub(crate) fn pretty_print(
    buf: &mut String,
    sexp: &Sexp,
    width: usize,
    level: usize,
) -> std::fmt::Result {
    use std::fmt::Write;
    if let Sexp::List(list) = sexp {
        let indent = sexp.to_string().len() > width;
        write!(buf, "(")?;

        for (i, val) in list.iter().enumerate() {
            if indent && i > 0 {
                writeln!(buf)?;
                for _ in 0..level {
                    write!(buf, "  ")?;
                }
            }
            pretty_print(buf, val, width, level + 1)?;
            if !indent && i < list.len() - 1 {
                write!(buf, " ")?;
            }
        }

        write!(buf, ")")?;
        Ok(())
    } else {
        // I don't care about quotes
        write!(buf, "{}", sexp.to_string().trim_matches('"'))
    }
}

/// A wrapper that uses display implementation as debug
pub(crate) struct DisplayAsDebug<T>(pub T);

impl<T: Display> Debug for DisplayAsDebug<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

/** A data structure to maintain a queue of unique elements.

Notably, insert/pop operations have O(1) expected amortized runtime complexity.
*/
#[derive(Clone)]
#[cfg_attr(feature = "serde-1", derive(Serialize, Deserialize))]
pub(crate) struct UniqueQueue<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    set: hashbrown::HashSet<T>,
    queue: std::collections::VecDeque<T>,
}

impl<T> Default for UniqueQueue<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    fn default() -> Self {
        UniqueQueue {
            set: hashbrown::HashSet::default(),
            queue: std::collections::VecDeque::new(),
        }
    }
}

impl<T> UniqueQueue<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    pub fn insert(&mut self, t: T) {
        if self.set.insert(t.clone()) {
            self.queue.push_back(t);
        }
    }

    pub fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        for t in iter.into_iter() {
            self.insert(t);
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        let res = self.queue.pop_front();
        res.as_ref().map(|t| self.set.remove(t));
        res
    }

    pub fn is_empty(&self) -> bool {
        let r = self.queue.is_empty();
        debug_assert_eq!(r, self.set.is_empty());
        r
    }
}

impl<T> IntoIterator for UniqueQueue<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    type Item = T;

    type IntoIter = <std::collections::VecDeque<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.queue.into_iter()
    }
}

impl<A> FromIterator<A> for UniqueQueue<A>
where
    A: Eq + std::hash::Hash + Clone,
{
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        let mut queue = UniqueQueue::default();
        for t in iter {
            queue.insert(t);
        }
        queue
    }
}
