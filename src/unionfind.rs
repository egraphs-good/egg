use crate::util::{HashMap, HashSet};

#[derive(Debug, Default)]
pub struct UnionFind {
    parents: Vec<u32>,
    sizes: Vec<u32>,
}

#[derive(Debug, PartialEq)]
pub enum UnionResult {
    Unioned { from: u32, to: u32 },
    SameSet(u32),
}

impl UnionFind {
    pub fn new() -> UnionFind {
        UnionFind::default()
    }

    pub fn len(&self) -> usize {
        self.parents.len()
    }

    pub fn make_set(&mut self) -> u32 {
        let new = self.len() as u32;
        self.parents.push(new);
        self.sizes.push(1);
        new
    }

    #[inline(always)]
    fn parent(&self, query: u32) -> Option<u32> {
        let parent = self.parents[query as usize];
        if query == parent {
            None
        } else {
            Some(parent)
        }
    }

    pub fn just_find(&self, query: u32) -> u32 {
        let mut current = query;
        while let Some(parent) = self.parent(current) {
            current = parent;
        }
        current
    }

    pub fn find(&mut self, query: u32) -> u32 {
        let root = self.just_find(query);

        // do simple path compression with another loop
        let mut current = query;
        while let Some(parent) = self.parent(current) {
            self.parents[current as usize] = root;
            current = parent;
        }

        current
    }

    pub fn union(&mut self, set1: u32, set2: u32) -> UnionResult {
        let mut root1 = self.find(set1);
        let mut root2 = self.find(set2);

        if root1 == root2 {
            return UnionResult::SameSet(root1);
        }

        // make root1 the bigger one, then union into that one
        let size1 = self.sizes[root1 as usize];
        let size2 = self.sizes[root2 as usize];
        if size1 < size2 {
            // don't need to swap sizes, we just add them
            std::mem::swap(&mut root1, &mut root2)
        }

        self.parents[root2 as usize] = root1;
        self.sizes[root1 as usize] = size1 + size2;

        UnionResult::Unioned {
            from: root2,
            to: root1,
        }
    }

    pub fn build_sets(&self) -> HashMap<u32, HashSet<u32>> {
        let mut map: HashMap<u32, HashSet<u32>> = HashMap::default();

        for i in 0..self.len() {
            let i = i as u32;
            let leader = self.just_find(i);
            let actual_set = map.entry(leader).or_default();
            actual_set.insert(i);
        }

        map
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::util::{hashmap, hashset};

    fn make_union_find(n: u32) -> UnionFind {
        let mut uf = UnionFind::new();
        for _ in 0..n {
            uf.make_set();
        }
        uf
    }

    #[test]
    fn union_find() {
        let n = 10;

        let mut uf = make_union_find(n);

        // test the initial condition of everyone in their own set
        for i in 0..n {
            assert_eq!(uf.parent(i), None);
            assert_eq!(uf.just_find(i), i);
            assert_eq!(uf.find(i), i);
        }

        // make sure build_sets works
        let expected_sets = (0..n)
            .map(|i| (i, hashset(&[i])))
            .collect::<HashMap<_, _>>();
        assert_eq!(uf.build_sets(), expected_sets);

        use UnionResult::*;

        // these should all merge into 0, because it's the largest class
        // after the first merge
        assert_eq!(uf.union(0, 1), Unioned { from: 1, to: 0 });
        assert_eq!(uf.union(1, 2), Unioned { from: 2, to: 0 });
        assert_eq!(uf.union(3, 2), Unioned { from: 3, to: 0 });

        // build up another set
        assert_eq!(uf.union(6, 7), Unioned { from: 7, to: 6 });
        assert_eq!(uf.union(8, 9), Unioned { from: 9, to: 8 });
        assert_eq!(uf.union(7, 9), Unioned { from: 8, to: 6 });

        // make sure union on same set returns leader
        assert_eq!(uf.union(1, 3), SameSet(0));
        assert_eq!(uf.union(7, 8), SameSet(6));

        // check set structure
        let expected_sets = hashmap(&[
            (0, hashset(&[0, 1, 2, 3])),
            (4, hashset(&[4])),
            (5, hashset(&[5])),
            (6, hashset(&[6, 7, 8, 9])),
        ]);
        assert_eq!(uf.build_sets(), expected_sets);

        // make sure that the set sizes are right
        for (leader, set) in uf.build_sets() {
            assert_eq!(uf.sizes[leader as usize], set.len() as u32);
        }

        // make sure that at least one set isn't flat
        assert!((0..n).any(|i| uf.parents[i as usize] != uf.just_find(i)));

        // compress all paths
        for i in 0..n {
            // make sure the leader is a leader
            let leader = uf.find(i);
            assert_eq!(uf.parent(leader), None);

            // make sure the path is compressed
            assert_eq!(uf.parents[i as usize], leader);

            // make sure this didn't change the set structure
            assert_eq!(uf.build_sets(), expected_sets);
        }

        // make sure that the set sizes are still right
        for (leader, set) in uf.build_sets() {
            assert_eq!(uf.sizes[leader as usize], set.len() as u32);
        }
    }
}
