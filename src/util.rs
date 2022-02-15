use std::str::FromStr;
use std::sync::RwLock;
use std::{fmt, hash::Hash};
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

const SHARD_BITS: u32 = 7;
const N_SHARDS: usize = 1 << SHARD_BITS;
#[allow(clippy::assertions_on_constants)]
static STRINGS: Lazy<Vec<RwLock<IndexSet<&'static str>>>> = Lazy::new(|| {
    assert!(SHARD_BITS < 8);
    let mut vec = Vec::with_capacity(N_SHARDS);
    vec.resize_with(N_SHARDS, Default::default);
    vec
});

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
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde-1", serde(from = "&str", into = "String"))]
pub struct Symbol([u8; 4]);

impl Symbol {
    /// Get the string that this symbol represents
    pub fn as_str(&self) -> &str {
        let byte = self.0[0];
        if byte & 0x80 == 0x80 {
            let str_len = (byte & 0x7f) as usize;
            let bytes = &self.0[1..str_len + 1];
            std::str::from_utf8(bytes).unwrap()
        } else {
            let shard_i = byte as usize;
            let mut bytes = self.0;
            bytes[0] = 0;
            let i = u32::from_be_bytes(bytes) as usize;
            let strings = STRINGS[shard_i].read().unwrap_or_else(|err| {
                panic!("Failed to acquire egg's global string cache: {}", err)
            });
            strings.get_index(i).unwrap()
        }
    }

    fn from_index(shard_i: usize, i: usize) -> Self {
        assert!(shard_i < N_SHARDS);
        let i_limit = 1 << (8 * 3);
        assert!(i < i_limit, "Can't represent index {} in a Symbol", i);
        let mut bytes = (i as u32).to_be_bytes();
        assert_eq!(bytes[0], 0);
        bytes[0] = shard_i as u8;
        Self(bytes)
    }
}

fn leak(s: &str) -> &'static str {
    Box::leak(s.to_owned().into_boxed_str())
}

fn intern(s: &str) -> Symbol {
    if s.len() < 4 {
        let mut bytes = [0; 4];
        bytes[1..s.len() + 1].copy_from_slice(s.as_bytes());
        bytes[0] = (s.len() as u8) | 0x80;
        return Symbol(bytes);
    }

    let shard_i = {
        let mut hasher = std::hash::BuildHasher::build_hasher(&BuildHasher::default());
        s.hash(&mut hasher);
        std::hash::Hasher::finish(&hasher) as usize % N_SHARDS
    };

    let strings = STRINGS[shard_i]
        .read()
        .unwrap_or_else(|err| panic!("Failed to acquire egg's global string cache: {}", err));
    if let Some((i, _)) = strings.get_full(s) {
        return Symbol::from_index(shard_i, i);
    }
    // Release the read lock.
    drop(strings);

    let mut strings = STRINGS[shard_i]
        .write()
        .unwrap_or_else(|err| panic!("Failed to acquire egg's global string cache: {}", err));
    let i = match strings.get_full(s) {
        Some((i, _)) => i, // The string was inserted in the meantime.
        None => strings.insert_full(leak(s)).0,
    };
    Symbol::from_index(shard_i, i)
}

impl<S: AsRef<str>> From<S> for Symbol {
    fn from(s: S) -> Self {
        intern(s.as_ref())
    }
}

impl From<Symbol> for String {
    fn from(s: Symbol) -> Self {
        s.as_str().into()
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_symbol() {
        for &s in &["", "f", "x", "foo", "foobar", "foooooooo\n\n", "⌣"] {
            let sym = Symbol::from(s);
            assert_eq!(sym.0, Symbol::from(s).0);
            assert_eq!(sym, Symbol::from(s));
            assert_eq!(sym.as_str(), s);
        }
    }
}
