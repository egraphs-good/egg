use crate::Id;
use std::cell::Cell;
use std::fmt::Debug;

// The Key bound on UnionFind is necessary to derive clone. We only
// instantiate UnionFind in one place (EGraph), so this type bound
// isn't intrusive

#[derive(Debug, Clone, Default)]
pub struct UnionFind {
    parents: Vec<Cell<Id>>,
}

impl UnionFind {
    pub fn make_set(&mut self) -> Id {
        let id = self.parents.len() as Id;
        self.parents.push(Cell::new(id));
        id
    }

    #[inline(always)]
    fn parent(&self, query: Id) -> Id {
        self.parents[query as usize].get()
    }

    #[inline(always)]
    fn set_parent(&self, query: Id, new_parent: Id) {
        self.parents[query as usize].set(new_parent)
    }

    pub fn find(&self, mut current: Id) -> Id {
        loop {
            let parent = self.parent(current);
            if current == parent {
                return parent;
            }
            // do path halving and proceed
            let grandparent = self.parent(parent);
            self.set_parent(current, grandparent);
            current = grandparent;
        }
    }

    /// Returns (new_leader, old_leader)
    pub fn union(&mut self, set1: Id, set2: Id) -> (Id, Id) {
        let root1 = self.find(set1);
        let root2 = self.find(set2);

        if root1 == root2 {
            (root1, root2)
        } else {
            self.set_parent(root2, root1);
            (root1, root2)
        }
    }
}

#[cfg(test)]
mod tests {
    // FIXME
    // use super::*;

    // use indexmap::{indexmap, indexset, IndexMap, IndexSet};
    // use std::hash::Hash;

    // impl<K: Key + Eq + Hash, V> UnionFind<K, V> {
    //     fn build_sets(&self) -> IndexMap<K, IndexSet<K>> {
    //         let mut map: IndexMap<K, IndexSet<K>> = IndexMap::default();

    //         for i in (0..self.total_size()).map(Key::from_index) {
    //             let leader = self.find(i);
    //             let actual_set = map.entry(leader).or_default();
    //             actual_set.insert(i);
    //         }

    //         map
    //     }
    // }

    // fn make_union_find(n: u32) -> UnionFind<u32, ()> {
    //     let mut uf = UnionFind::default();
    //     for _ in 0..n {
    //         uf.make_set(());
    //     }
    //     uf
    // }

    // #[test]
    // fn union_find() {
    //     let n = 10;

    //     let mut uf = make_union_find(n);

    //     // test the initial condition of everyone in their own set
    //     for i in 0..n {
    //         assert_eq!(uf.find(i), i);
    //         assert_eq!(uf.find(i), i);
    //     }

    //     // make sure build_sets works
    //     let expected_sets = (0..n)
    //         .map(|i| (i, indexset!(i)))
    //         .collect::<IndexMap<_, _>>();
    //     assert_eq!(uf.build_sets(), expected_sets);

    //     // these should all merge into 0, because it's the largest class
    //     // after the first merge
    //     assert_eq!(uf.union(0, 1), Ok((0, true)));
    //     assert_eq!(uf.union(1, 2), Ok((0, true)));
    //     assert_eq!(uf.union(3, 2), Ok((0, true)));

    //     // build up another set
    //     assert_eq!(uf.union(6, 7), Ok((6, true)));
    //     assert_eq!(uf.union(8, 9), Ok((8, true)));
    //     assert_eq!(uf.union(7, 9), Ok((6, true)));

    //     // make sure union on same set returns leader and false
    //     assert_eq!(uf.union(1, 3), Ok((0, false)));
    //     assert_eq!(uf.union(7, 8), Ok((6, false)));

    //     // check set structure
    //     let expected_sets = indexmap!(
    //         0 => indexset!(0, 1, 2, 3),
    //         4 => indexset!(4),
    //         5 => indexset!(5),
    //         6 => indexset!(6, 7, 8, 9),
    //     );
    //     assert_eq!(uf.build_sets(), expected_sets);

    //     // make sure that the set sizes are right
    //     for (leader, set) in uf.build_sets() {
    //         assert_eq!(uf.sizes[leader as usize], set.len() as u32);
    //     }

    //     // compress all paths
    //     for i in 0..n {
    //         // make sure the leader is a leader
    //         let leader = uf.find(i);
    //         assert_eq!(uf.find(leader), leader);

    //         // make sure the path is compressed
    //         assert_eq!(uf.parents[i as usize].get(), leader);

    //         // make sure this didn't change the set structure
    //         assert_eq!(uf.build_sets(), expected_sets);
    //     }

    //     // make sure that the set sizes are still right
    //     for (leader, set) in uf.build_sets() {
    //         assert_eq!(uf.sizes[leader as usize], set.len() as u32);
    //     }
    // }
}
