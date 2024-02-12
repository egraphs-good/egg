use std::fmt::{Debug, Formatter};
use std::hash::{BuildHasher, Hash};
use std::iter;
use std::iter::FromIterator;

use hashbrown::hash_table;

pub(super) type DHMIdx = u32;

/// Similar to [`HashMap`](std::collections::HashMap) but with deterministic iteration order
///
/// Accessing individual elements has similar performance to a [`HashMap`](std::collections::HashMap)
/// (faster than an `IndexMap`), but iteration requires allocation
///
#[derive(Clone)]
pub(super) struct DHashMap<K, V, S = crate::util::BuildHasher> {
    data: hash_table::HashTable<(K, V, DHMIdx)>,
    hasher: S,
}

impl<K, V, S: Default> Default for DHashMap<K, V, S> {
    fn default() -> Self {
        DHashMap {
            data: Default::default(),
            hasher: Default::default(),
        }
    }
}

pub(super) struct VacantEntry<'a, K, V> {
    len: DHMIdx,
    entry: hash_table::VacantEntry<'a, (K, V, DHMIdx)>,
    k: K,
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    pub(super) fn insert(self, v: V) {
        self.entry.insert((self.k, v, self.len));
    }
}

pub(super) enum Entry<'a, K, V> {
    Occupied((K, &'a mut V)),
    Vacant(VacantEntry<'a, K, V>),
}

#[inline]
fn hash_one(hasher: &impl BuildHasher, hash: impl Hash) -> u64 {
    use core::hash::Hasher;
    let mut hasher = hasher.build_hasher();
    hash.hash(&mut hasher);
    hasher.finish()
}

#[inline]
fn eq<'a, K: Eq, V>(k: &'a K) -> impl Fn(&(K, V, DHMIdx)) -> bool + 'a {
    move |x| &x.0 == k
}

#[inline]
fn hasher_fn<'a, K: Hash, V, S: BuildHasher>(
    hasher: &'a S,
) -> impl Fn(&(K, V, DHMIdx)) -> u64 + 'a {
    move |x| hash_one(hasher, &x.0)
}

impl<K: Hash + Eq, V, S: BuildHasher> DHashMap<K, V, S> {
    #[inline]
    pub(super) fn entry(&mut self, k: K) -> (Entry<'_, K, V>, u64) {
        let hash = hash_one(&mut self.hasher, &k);
        let len = self.data.len() as DHMIdx;
        let entry = match self.data.entry(hash, eq(&k), hasher_fn(&self.hasher)) {
            hash_table::Entry::Occupied(entry) => Entry::Occupied((k, &mut entry.into_mut().1)),
            hash_table::Entry::Vacant(entry) => Entry::Vacant(VacantEntry { len, entry, k }),
        };
        (entry, hash)
    }

    #[inline]
    pub(super) fn insert_with_hash(&mut self, hash: u64, k: K, v: V) {
        debug_assert!({
            let (v, hash2) = self.get(&k);
            v.is_none() && hash == hash2
        });
        let len = self.data.len() as DHMIdx;
        self.data
            .insert_unique(hash, (k, v, len), hasher_fn(&self.hasher));
    }

    #[inline]
    pub(super) fn remove_nth(&mut self, hash: u64, idx: usize) {
        debug_assert_eq!(self.data.len() - 1, idx);
        let idx = idx as DHMIdx;
        match self.data.find_entry(hash, |x| x.2 == idx) {
            Ok(x) => x.remove(),
            Err(_) => unreachable!(),
        };
    }

    #[inline]
    pub(super) fn len(&self) -> usize {
        self.data.len()
    }

    #[inline]
    pub(super) fn get(&self, k: &K) -> (Option<&V>, u64) {
        let hash = hash_one(&self.hasher, k);
        (self.data.find(hash, eq(k)).map(|x| &x.1), hash)
    }

    pub(super) fn clear(&mut self) {
        self.data.clear()
    }
}

impl<'a, K, V, S> IntoIterator for &'a DHashMap<K, V, S> {
    type Item = (&'a K, &'a V);

    // TODO replace with TAIT
    type IntoIter = iter::Map<
        std::vec::IntoIter<Option<(&'a K, &'a V)>>,
        fn(Option<(&'a K, &'a V)>) -> (&'a K, &'a V),
    >;

    #[inline(never)]
    fn into_iter(self) -> Self::IntoIter {
        let mut data: Vec<_> = iter::repeat(None).take(self.data.len()).collect();
        for (k, v, i) in &self.data {
            data[*i as usize] = Some((k, v))
        }
        data.into_iter().map(Option::unwrap)
    }
}

impl<K: Hash + Eq, V, S: Default + BuildHasher> FromIterator<(K, V)> for DHashMap<K, V, S> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut res = Self::default();
        iter.into_iter().for_each(|(k, v)| {
            let hash = hash_one(&mut res.hasher, &k);
            res.insert_with_hash(hash, k, v)
        });
        res
    }
}

impl<K: Debug, V: Debug, S> Debug for DHashMap<K, V, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self).finish()
    }
}

#[cfg(test)]
mod test {
    use crate::raw::dhashmap::DHashMap;
    use std::fmt::Debug;
    use std::hash::{Hash, Hasher};

    #[derive(Eq, PartialEq, Debug, Clone)]
    struct BadHash<T>(T);

    impl<T> Hash for BadHash<T> {
        fn hash<H: Hasher>(&self, _: &mut H) {}
    }

    fn test<K: Hash + Eq + Clone + Debug, V: Eq + Clone + Debug, const N: usize>(arr: [(K, V); N]) {
        let mut map: DHashMap<K, V> = DHashMap::default();
        let mut hashes = Vec::new();
        for (k, v) in arr.iter().cloned() {
            let (r, hash) = map.get(&k);
            assert!(r.is_none());
            hashes.push(hash);
            map.insert_with_hash(hash, k, v)
        }
        assert_eq!(map.len(), N);
        for (i, (k, v)) in arr.iter().enumerate().rev() {
            let (r, hash) = map.get(k);
            assert_eq!(Some(hash), hashes.pop());
            assert_eq!(r, Some(v));
            map.remove_nth(hash, i);
            let (r2, hash2) = map.get(k);
            assert_eq!(hash2, hash);
            assert_eq!(r2, None);
            assert_eq!(map.len(), i);
        }
    }

    #[test]
    fn test_base() {
        test([('a', "a"), ('b', "b"), ('c', "c")])
    }

    #[test]
    fn test_bad_hash() {
        test([
            (BadHash('a'), "a"),
            (BadHash('b'), "b"),
            (BadHash('c'), "c"),
        ])
    }
}
