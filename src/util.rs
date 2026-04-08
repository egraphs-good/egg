use core::fmt::{self, Debug, Display, Formatter};
use core::iter::FromIterator;

use alloc::string::String;
use alloc::vec::Vec;

use crate::sexp::Sexp;

#[cfg(feature = "serde-1")]
use serde::{Deserialize, Serialize};

#[allow(unused_imports)]
use crate::*;

// --- Symbol ---

/// An interned string.
///
/// This is provided by the [`symbol_table`](https://crates.io/crates/symbol_table) crate
/// when the `std` feature is enabled.
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
#[cfg(feature = "std")]
pub use symbol_table::GlobalSymbol as Symbol;

#[cfg(not(feature = "std"))]
pub use self::no_std_symbol::Symbol;

#[cfg(not(feature = "std"))]
mod no_std_symbol {
    use alloc::boxed::Box;
    use alloc::string::String;
    use alloc::vec::Vec;
    use core::num::NonZeroU32;
    use spin::Mutex;

    static SYMBOLS: Mutex<Vec<&'static str>> = Mutex::new(Vec::new());

    /// An interned string backed by a global table (no_std version).
    ///
    /// Semantically identical to `symbol_table::GlobalSymbol`:
    /// 4 bytes, `Copy`, `Eq`, `Hash`, `Ord`.
    #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub struct Symbol(NonZeroU32);

    impl Symbol {
        /// Returns the string this symbol represents.
        pub fn as_str(&self) -> &'static str {
            let table = SYMBOLS.lock();
            table[(self.0.get() - 1) as usize]
        }
    }

    impl From<&str> for Symbol {
        fn from(s: &str) -> Self {
            let mut table = SYMBOLS.lock();
            for (i, &existing) in table.iter().enumerate() {
                if existing == s {
                    return Symbol(NonZeroU32::new((i + 1) as u32).expect("symbol index overflow"));
                }
            }
            let leaked: &'static str = Box::leak(String::from(s).into_boxed_str());
            table.push(leaked);
            Symbol(NonZeroU32::new(table.len() as u32).expect("symbol index overflow"))
        }
    }

    impl From<String> for Symbol {
        fn from(s: String) -> Self {
            Symbol::from(s.as_str())
        }
    }

    impl core::str::FromStr for Symbol {
        type Err = core::convert::Infallible;
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            Ok(Symbol::from(s))
        }
    }

    impl core::fmt::Display for Symbol {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "{}", self.as_str())
        }
    }

    impl core::fmt::Debug for Symbol {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "{}", self.as_str())
        }
    }

    #[cfg(feature = "serde-1")]
    impl serde::Serialize for Symbol {
        fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.serialize_str(self.as_str())
        }
    }

    #[cfg(feature = "serde-1")]
    impl<'de> serde::Deserialize<'de> for Symbol {
        fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            let s = <&str>::deserialize(deserializer)?;
            Ok(Symbol::from(s))
        }
    }
}

// --- Hashing ---

pub(crate) type BuildHasher = rustc_hash::FxBuildHasher;

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

// --- Timing ---

#[cfg(feature = "std")]
pub(crate) type Instant = quanta::Instant;

#[cfg(not(feature = "std"))]
pub(crate) type Instant = no_std_instant::Instant;

pub(crate) type Duration = core::time::Duration;

#[cfg(not(feature = "std"))]
mod no_std_instant {
    /// A no-op instant for `no_std` environments.
    ///
    /// Time limits are effectively disabled; iteration and node limits still work.
    #[derive(Clone, Copy, Debug)]
    pub struct Instant;

    impl Instant {
        /// Returns a no-op instant.
        pub fn now() -> Self {
            Instant
        }

        /// Always returns `Duration::ZERO`.
        pub fn elapsed(&self) -> core::time::Duration {
            core::time::Duration::ZERO
        }
    }
}

// --- Utilities ---

pub(crate) fn concat_vecs<T>(to: &mut Vec<T>, mut from: Vec<T>) {
    if to.len() < from.len() {
        core::mem::swap(to, &mut from)
    }
    to.extend(from);
}

pub(crate) fn pretty_print(
    buf: &mut String,
    sexp: &Sexp,
    width: usize,
    level: usize,
) -> fmt::Result {
    use fmt::Write;
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
    T: Eq + core::hash::Hash + Clone,
{
    set: hashbrown::HashSet<T, BuildHasher>,
    queue: alloc::collections::VecDeque<T>,
}

impl<T> Default for UniqueQueue<T>
where
    T: Eq + core::hash::Hash + Clone,
{
    fn default() -> Self {
        UniqueQueue {
            set: hashbrown::HashSet::with_hasher(BuildHasher::default()),
            queue: alloc::collections::VecDeque::new(),
        }
    }
}

impl<T> UniqueQueue<T>
where
    T: Eq + core::hash::Hash + Clone,
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
    T: Eq + core::hash::Hash + Clone,
{
    type Item = T;

    type IntoIter = <alloc::collections::VecDeque<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.queue.into_iter()
    }
}

impl<A> FromIterator<A> for UniqueQueue<A>
where
    A: Eq + core::hash::Hash + Clone,
{
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        let mut queue = UniqueQueue::default();
        for t in iter {
            queue.insert(t);
        }
        queue
    }
}
