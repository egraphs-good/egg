use std::cell::Cell;
use std::fmt::Debug;

// The Key bound on UnionFind is necessary to derive clone. We only
// instantiate UnionFind in one place (EGraph), so this type bound
// isn't intrusive

#[derive(Debug, Clone)]
pub struct UnionFind<K: Key, V> {
    parents: Vec<Cell<K>>,
    sizes: Vec<u32>,
    values: Vec<Option<V>>,
    n_leaders: usize,
}

impl<K: Key, V> Default for UnionFind<K, V> {
    fn default() -> Self {
        UnionFind {
            parents: Vec::new(),
            sizes: Vec::new(),
            values: Vec::new(),
            n_leaders: 0,
        }
    }
}

pub trait Key: Copy + PartialEq {
    fn index(self) -> usize;
    fn from_index(index: usize) -> Self;
}

impl Key for u32 {
    #[inline(always)]
    fn index(self) -> usize {
        self as usize
    }
    fn from_index(index: usize) -> Self {
        index as Self
    }
}

pub trait Value: Sized {
    type Error: Debug;
    fn merge<K: Key>(
        unionfind: &mut UnionFind<K, Self>,
        value1: Self,
        value2: Self,
    ) -> Result<Self, Self::Error>;
}

impl Value for () {
    type Error = std::convert::Infallible;
    fn merge<K: Key>(
        _: &mut UnionFind<K, Self>,
        _value1: Self,
        _value2: Self,
    ) -> Result<Self, Self::Error> {
        Ok(())
    }
}

#[inline(always)]
fn find<K: Key>(parents: &[Cell<K>], mut current: K) -> K {
    loop {
        let parent = parents[current.index()].get();
        if current == parent {
            return current;
        }
        let grandparent = parents[parent.index()].get();
        parents[current.index()].set(grandparent);
        current = grandparent;
    }
}

impl<K: Key, V> UnionFind<K, V> {
    pub fn total_size(&self) -> usize {
        debug_assert_eq!(self.parents.len(), self.sizes.len());
        debug_assert_eq!(self.parents.len(), self.values.len());
        self.parents.len()
    }

    pub fn number_of_classes(&self) -> usize {
        self.n_leaders
    }

    pub fn make_set(&mut self, value: V) -> K {
        let new = Key::from_index(self.total_size());
        self.parents.push(Cell::new(new));
        self.sizes.push(1);
        self.values.push(Some(value));
        self.n_leaders += 1;
        new
    }

    pub fn find(&self, current: K) -> K {
        find(&self.parents, current)
    }

    pub fn get(&self, query: K) -> &V {
        let leader = self.find(query);
        self.values[leader.index()].as_ref().unwrap()
    }

    #[allow(dead_code)]
    pub fn get_mut(&mut self, query: K) -> &mut V {
        let leader = self.find(query);
        self.values[leader.index()].as_mut().unwrap()
    }

    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.values.iter().filter_map(Option::as_ref)
    }

    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.values.iter_mut().filter_map(Option::as_mut)
    }

    // this is useful when you want to mutate the values, but still be
    // able to perform lookups
    pub fn split<'a>(&'a mut self) -> (impl Fn(K) -> K + 'a, impl Iterator<Item = &mut V>) {
        let parents = &self.parents;
        let values = self.values.iter_mut().filter_map(Option::as_mut);
        (move |k| find(parents, k), values)
    }
}

impl<K: Key, V: Value> UnionFind<K, V> {
    pub fn union(&mut self, set1: K, set2: K) -> Result<(K, bool), V::Error> {
        let mut root1 = self.find(set1);
        let mut root2 = self.find(set2);

        if root1 == root2 {
            return Ok((root1, false));
        }

        // make root1 the bigger one, then union into that one
        let size1 = self.sizes[root1.index()];
        let size2 = self.sizes[root2.index()];
        if size1 < size2 {
            // don't need to swap sizes, we just add them
            std::mem::swap(&mut root1, &mut root2)
        }

        let value1 = self.values[root1.index()].take().unwrap();
        let value2 = self.values[root2.index()].take().unwrap();

        let value = Value::merge(self, value1, value2);
        self.n_leaders -= 1;
        self.values[root1.index()] = Some(value?);

        self.parents[root2.index()].set(root1);
        self.sizes[root1.index()] = size1 + size2;

        Ok((root1, true))
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use indexmap::{indexmap, indexset, IndexMap, IndexSet};
    use std::hash::Hash;

    impl<K: Key + Eq + Hash, V> UnionFind<K, V> {
        fn build_sets(&self) -> IndexMap<K, IndexSet<K>> {
            let mut map: IndexMap<K, IndexSet<K>> = IndexMap::default();

            for i in (0..self.total_size()).map(Key::from_index) {
                let leader = self.find(i);
                let actual_set = map.entry(leader).or_default();
                actual_set.insert(i);
            }

            map
        }
    }

    fn make_union_find(n: u32) -> UnionFind<u32, ()> {
        let mut uf = UnionFind::default();
        for _ in 0..n {
            uf.make_set(());
        }
        uf
    }

    #[test]
    fn union_find() {
        let n = 10;

        let mut uf = make_union_find(n);

        // test the initial condition of everyone in their own set
        for i in 0..n {
            assert_eq!(uf.find(i), i);
            assert_eq!(uf.find(i), i);
        }

        // make sure build_sets works
        let expected_sets = (0..n)
            .map(|i| (i, indexset!(i)))
            .collect::<IndexMap<_, _>>();
        assert_eq!(uf.build_sets(), expected_sets);

        // these should all merge into 0, because it's the largest class
        // after the first merge
        assert_eq!(uf.union(0, 1), Ok((0, true)));
        assert_eq!(uf.union(1, 2), Ok((0, true)));
        assert_eq!(uf.union(3, 2), Ok((0, true)));

        // build up another set
        assert_eq!(uf.union(6, 7), Ok((6, true)));
        assert_eq!(uf.union(8, 9), Ok((8, true)));
        assert_eq!(uf.union(7, 9), Ok((6, true)));

        // make sure union on same set returns leader and false
        assert_eq!(uf.union(1, 3), Ok((0, false)));
        assert_eq!(uf.union(7, 8), Ok((6, false)));

        // check set structure
        let expected_sets = indexmap!(
            0 => indexset!(0, 1, 2, 3),
            4 => indexset!(4),
            5 => indexset!(5),
            6 => indexset!(6, 7, 8, 9),
        );
        assert_eq!(uf.build_sets(), expected_sets);

        // make sure that the set sizes are right
        for (leader, set) in uf.build_sets() {
            assert_eq!(uf.sizes[leader as usize], set.len() as u32);
        }

        // compress all paths
        for i in 0..n {
            // make sure the leader is a leader
            let leader = uf.find(i);
            assert_eq!(uf.find(leader), leader);

            // make sure the path is compressed
            assert_eq!(uf.parents[i as usize].get(), leader);

            // make sure this didn't change the set structure
            assert_eq!(uf.build_sets(), expected_sets);
        }

        // make sure that the set sizes are still right
        for (leader, set) in uf.build_sets() {
            assert_eq!(uf.sizes[leader as usize], set.len() as u32);
        }
    }
}
