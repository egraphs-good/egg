pub(crate) use hashmap::*;

pub(crate) type BuildHasher = fxhash::FxBuildHasher;

#[cfg(feature = "deterministic")]
mod hashmap {
    use super::BuildHasher;
    pub(crate) type HashMap<K, V> = indexmap::IndexMap<K, V, BuildHasher>;
    pub(crate) type HashSet<K> = indexmap::IndexSet<K, BuildHasher>;

    pub(crate) type Entry<'a, K, V> = indexmap::map::Entry<'a, K, V>;
}
#[cfg(not(feature = "deterministic"))]
mod hashmap {
    use super::BuildHasher;
    pub(crate) type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasher>;
    pub(crate) type HashSet<K> = hashbrown::HashSet<K, BuildHasher>;
    pub(crate) type Entry<'a, K, V> = hashbrown::hash_map::Entry<'a, K, V, BuildHasher>;
}
