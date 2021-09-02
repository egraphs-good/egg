use std::fmt;
use std::str::FromStr;
use std::sync::Mutex;
use symbolic_expressions::Sexp;

use fmt::{Debug, Display, Formatter};
use once_cell::sync::Lazy;

#[allow(unused_imports)]
use crate::*;

pub(crate) type BuildHasher = fxhash::FxBuildHasher;

pub(crate) type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasher>;
pub(crate) type HashSet<K> = hashbrown::HashSet<K, BuildHasher>;

pub(crate) type IndexMap<K, V> = indexmap::IndexMap<K, V, BuildHasher>;
pub(crate) type IndexSet<K> = indexmap::IndexSet<K, BuildHasher>;

pub(crate) type Instant = instant::Instant;
pub(crate) type Duration = instant::Duration;

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

static STRINGS: Lazy<Mutex<IndexSet<&'static str>>> = Lazy::new(Default::default);

/// An interned string.
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
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(u32);

impl Symbol {
    /// Get the string that this symbol represents
    pub fn as_str(self) -> &'static str {
        let i = self.0 as usize;
        let strings = STRINGS
            .lock()
            .unwrap_or_else(|err| panic!("Failed to acquire egg's global string cache: {}", err));
        strings.get_index(i).unwrap()
    }
}

fn leak(s: &str) -> &'static str {
    Box::leak(s.to_owned().into_boxed_str())
}

fn intern(s: &str) -> Symbol {
    let mut strings = STRINGS
        .lock()
        .unwrap_or_else(|err| panic!("Failed to acquire egg's global string cache: {}", err));
    let i = match strings.get_full(s) {
        Some((i, _)) => i,
        None => strings.insert_full(leak(s)).0,
    };
    Symbol(i as u32)
}

impl<S: AsRef<str>> From<S> for Symbol {
    fn from(s: S) -> Self {
        intern(s.as_ref())
    }
}

impl FromStr for Symbol {
    type Err = std::convert::Infallible;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.into())
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self.as_str(), f)
    }
}

impl Debug for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(self.as_str(), f)
    }
}

/// A wrapper that uses display implementation as debug
pub(crate) struct DisplayAsDebug<T>(pub T);

impl<T: Display> Debug for DisplayAsDebug<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}
