use std::fmt;
use std::str::FromStr;
use std::sync::Mutex;

use indexmap::IndexSet;
use once_cell::sync::Lazy;

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
/// [`Var`]: struct.Var.html
/// [`Symbol`]: struct.Symbol.html
/// [`Language`]: trait.Language.html
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

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}
