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

pub(crate) mod util {
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
