use crate::Id;
use std::fmt::Debug;


#[derive(Debug, Clone, Default)]
pub struct UnionFind {
    parents: Vec<Id>,
}

impl UnionFind {
    pub fn make_set(&mut self) -> Id {
        let id = Id::from(self.parents.len());
        self.parents.push(id);
        id
    }

    fn is_root(&self, query: Id) -> bool {
        query == self.parents[usize::from(query)]
    }

    // we use unsafe slice accesses internally, but all public Ids
    // coming in are checked first
    #[inline(always)]
    unsafe fn parent(&self, query: Id) -> Id {
        *self.parents.get_unchecked(usize::from(query))
    }

    #[inline(always)]
    unsafe fn parent_mut(&mut self, query: Id) -> &mut Id {
        self.parents.get_unchecked_mut(usize::from(query))
    }

    pub fn find(&self, mut current: Id) -> Id {
        assert!(usize::from(current) < self.parents.len());
        unsafe {
            while current != self.parent(current) {
                current = self.parent(current)
            }
        }
        current
    }

    pub fn find_mut(&mut self, mut current: Id) -> Id {
        assert!(usize::from(current) < self.parents.len());
        unsafe {
            while current != self.parent(current) {
                let grandparent = self.parent(self.parent(current));
                *self.parent_mut(current) = grandparent;
                current = grandparent;
            }
        }
        current
    }

    /// Returns (new_leader, old_leader)
    pub fn union(&mut self, root1: Id, root2: Id) -> (Id, Id) {
        assert!(self.is_root(root1));
        assert!(self.is_root(root2));
        assert_ne!(root1, root2);

        unsafe {
            *self.parent_mut(root2) = root1;
        }
        (root1, root2)
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     use indexmap::{indexmap, indexset, IndexMap, IndexSet};

//     impl UnionFind {
//         pub fn build_sets(&mut self) -> IndexMap<Id, IndexSet<Id>> {
//             let mut map: IndexMap<Id, IndexSet<Id>> = Default::default();

//             for i in 0..self.parents.len() {
//                 let i = Id::from(i);
//                 let leader = self.find_mut(i);
//                 map.entry(leader).or_default().insert(i);
//             }

//             map
//         }
//     }

//     fn make_union_find(n: usize) -> UnionFind {
//         let mut uf = UnionFind::default();
//         for _ in 0..n {
//             uf.make_set();
//         }
//         uf
//     }

//     #[test]
//     fn union_find() {
//         let n = 10;

//         fn id(u: usize) -> Id {
//             u.into()
//         }

//         let mut uf = make_union_find(n);

//         // test the initial condition of everyone in their own set
//         for i in 0..n {
//             let i = Id::from(i);
//             assert_eq!(uf.find_mut(i), i);
//             assert_eq!(uf.find_mut(i), i);
//         }

//         // make sure build_sets works
//         let expected_sets = (0..n)
//             .map(|i| (id(i), indexset!(id(i))))
//             .collect::<IndexMap<_, _>>();
//         assert_eq!(uf.build_sets(), expected_sets);

//         // build up one set
//         assert_eq!(uf.union(id(0), id(1)), (id(0), id(1)));
//         assert_eq!(uf.union(id(1), id(2)), (id(0), id(2)));
//         assert_eq!(uf.union(id(3), id(2)), (id(0), id(3)));

//         // build up another set
//         assert_eq!(uf.union(id(6), id(7)), (id(6), id(7)));
//         assert_eq!(uf.union(id(8), id(9)), (id(8), id(9)));
//         assert_eq!(uf.union(id(7), id(9)), (id(6), id(8)));

//         // make sure union on same set returns to == from
//         assert_eq!(uf.union(id(1), id(3)), (id(0), id(0)));
//         assert_eq!(uf.union(id(7), id(8)), (id(6), id(6)));

//         // check set structure
//         let expected_sets = indexmap!(
//             id(0) => indexset!(id(0), id(1), id(2), id(3)),
//             id(4) => indexset!(id(4)),
//             id(5) => indexset!(id(5)),
//             id(6) => indexset!(id(6), id(7), id(8), id(9)),
//         );
//         assert_eq!(uf.build_sets(), expected_sets);

//         // all paths should be compressed at this point
//         for i in 0..n {
//             assert_eq!(uf.parent(id(i)), uf.find_mut(id(i)));
//         }
//     }
// }
