//!
//! [`EGraph`]s (and almost everything else in this crate) are
//! parameterized over the language given by the user (by implementing
//! the [`Language`] trait).
//!
//! A typical usage would either implement [`Language`] or use the
//! provided [`TestLang`]. From there, you can use the functionality
//! from the [`ParsableLanguage`] trait module to create expressions
//! and add them to the EGraph.
//!
//! [`EGraph`]: egraph/struct.EGraph.html
//! [`Language`]: expr/trait.Language.html
//! [`TestLang`]: expr/tests/struct.TestLang.html
//! [`ParsableLanguage`]: parse/trait.ParsableLanguage.html

#![warn(clippy::correctness)]
#![warn(clippy::style)]
#![warn(clippy::complexity)]
#![warn(clippy::perf)]
#![warn(clippy::cargo)]
// #![warn(clippy::pedantic)]
// #![warn(clippy::nursery)]

mod unionfind;

pub mod dot;
pub mod egraph;
pub mod expr;
pub mod extract;
pub mod parse;
pub mod pattern;

#[cfg(test)]
fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
}

pub mod util {
    pub type HashMap<K, V> = fxhash::FxHashMap<K, V>;
    pub type HashSet<K> = fxhash::FxHashSet<K>;

    #[cfg(test)]
    pub fn hashset<K>(ks: &[K]) -> HashSet<K>
    where
        K: Clone + std::hash::Hash + Eq,
    {
        ks.iter().cloned().collect()
    }

    #[cfg(test)]
    pub fn hashmap<K, KRef, V>(kvs: &[(KRef, V)]) -> HashMap<K, V>
    where
        K: Clone + std::hash::Hash + Eq,
        KRef: std::borrow::Borrow<K>,
        V: Clone,
    {
        kvs.iter()
            .map(|(k, v)| (k.borrow().clone(), v.clone()))
            .collect()
    }
}
