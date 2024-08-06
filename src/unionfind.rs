use crate::{AtomicId, Id};

use std::fmt::Debug;

#[derive(Debug, Default, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct UnionFind {
    // Because the correctness of the structure does not depend on exact shape of the tree but only
    // on the fact whether the root is correct, relaxed atomic operations can be used.
    // They may race not produce the same structure as a sequential algorithm, but the structure
    // is going to be correct nonetheless, at minimal synchronization cost.
    parents: Vec<AtomicId>,
}

impl UnionFind {
    pub fn make_set(&mut self) -> Id {
        let idx = self.parents.len();
        self.parents.push(AtomicId::from(idx));
        Id::from(idx)
    }

    pub fn size(&self) -> usize {
        self.parents.len()
    }

    fn parent(&self, query: Id) -> &AtomicId {
        &self.parents[usize::from(query)]
    }

    fn parent_mut(&mut self, query: Id) -> &mut AtomicId {
        &mut self.parents[usize::from(query)]
    }

    fn parent_relaxed(&self, query: Id) -> Id {
        self.parent(query).load_relaxed()
    }

    fn set_parent_mut(&mut self, query: Id, new_parent: Id) {
        *self.parent_mut(query).0.get_mut() = new_parent.0;
    }

    fn set_parent_relaxed(&self, query: Id, new_parent: Id) {
        self.parents[usize::from(query)].store_relaxed(new_parent);
    }

    pub fn find(&self, mut current: Id) -> Id {
        // Because another thread might be running the same function, `parent` and `grandparent`
        // might not refer to actual parent and grandparent after assignment.
        // However, they are guaranteed to point to some ancestor, which is enough for this
        // function to keep the invariants of the unionfind.
        let mut parent = self.parent_relaxed(current);
        while current != parent {
            let grandparent = self.parent_relaxed(parent);
            self.set_parent_relaxed(current, grandparent);
            current = grandparent;
            parent = self.parent_relaxed(current);
        }
        current
    }

    /// Given two leader ids, unions the two eclasses making root1 the leader.
    pub fn union(&mut self, root1: Id, root2: Id) -> Id {
        self.set_parent_mut(root2, root1);
        root1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ids(us: impl IntoIterator<Item = usize>) -> Vec<AtomicId> {
        us.into_iter().map(|u| u.into()).collect()
    }

    #[test]
    fn union_find() {
        let n = 10;
        let id = Id::from;

        let mut uf = UnionFind::default();
        for _ in 0..n {
            uf.make_set();
        }

        // test the initial condition of everyone in their own set
        assert!(ids(0..n)
            .into_iter()
            .zip(uf.parents.iter())
            .all(|(a, b)| a.load_relaxed() == b.load_relaxed()));

        // build up one set
        uf.union(id(0), id(1));
        uf.union(id(0), id(2));
        uf.union(id(0), id(3));

        // build up another set
        uf.union(id(6), id(7));
        uf.union(id(6), id(8));
        uf.union(id(6), id(9));

        // this should compress all paths
        for i in 0..n {
            uf.find(id(i));
        }

        // indexes:         0, 1, 2, 3, 4, 5, 6, 7, 8, 9
        let expected = vec![0, 0, 0, 0, 4, 5, 6, 6, 6, 6];
        assert!(ids(expected)
            .into_iter()
            .zip(uf.parents.iter())
            .all(|(a, b)| a.load_relaxed() == b.load_relaxed()));
    }
}
