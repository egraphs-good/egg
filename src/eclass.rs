use std::fmt::Debug;
use std::iter::ExactSizeIterator;

use crate::{
    unionfind::{Key, UnionFind, Value},
    ENode, Id, Language,
};

pub trait Metadata<L>: Sized + Debug {
    type Error: Debug;
    fn merge(&self, other: &Self) -> Self;
    // TODO should make be allowed to modify?
    fn make(enode: ENode<L, &Self>) -> Self;
    fn modify(_eclass: &mut EClass<L, Self>) {}
}

impl<L: Language> Metadata<L> for () {
    type Error = std::convert::Infallible;
    fn merge(&self, _other: &()) {}
    fn make(_enode: ENode<L, &()>) {}
}

#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct EClass<L, M> {
    pub id: Id,
    pub nodes: Vec<ENode<L>>,
    pub metadata: M,
    #[cfg(feature = "parent-pointers")]
    pub(crate) parents: indexmap::IndexSet<usize>,
}

impl<L, M> EClass<L, M> {
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = &ENode<L>> {
        self.nodes.iter()
    }
}

impl<L: Language, M: Metadata<L>> Value for EClass<L, M> {
    type Error = std::convert::Infallible;
    fn merge<K: Key>(
        _unionfind: &mut UnionFind<K, Self>,
        to: Self,
        from: Self,
    ) -> Result<Self, Self::Error> {
        let mut less = to.nodes;
        let mut more = from.nodes;

        // make sure less is actually smaller
        if more.len() < less.len() {
            std::mem::swap(&mut less, &mut more);
        }

        more.extend(less);

        let mut eclass = EClass {
            id: to.id,
            nodes: more,
            metadata: to.metadata.merge(&from.metadata),
            #[cfg(feature = "parent-pointers")]
            parents: {
                let mut parents = to.parents;
                parents.extend(from.parents);
                parents
            },
        };

        M::modify(&mut eclass);
        Ok(eclass)
    }
}
