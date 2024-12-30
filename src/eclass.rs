use std::fmt::Debug;
use std::iter::ExactSizeIterator;

use crate::*;

/// An equivalence class of enodes.
#[non_exhaustive]
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct EClass<L, D> {
    /// This eclass's id.
    pub id: Id,
    /// The equivalent enodes in this equivalence class.
    pub nodes: Vec<L>,
    /// The analysis data associated with this eclass.
    ///
    /// Modifying this field will _not_ cause changes to propagate through the e-graph.
    /// Prefer [`EGraph::set_analysis_data`] instead.
    pub data: D,
    /// The original Ids of parent enodes.
    pub(crate) parents: Vec<Id>,
}

impl<L, D> EClass<L, D> {
    /// Returns `true` if the `eclass` is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Returns the number of enodes in this eclass.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Iterates over the enodes in this eclass.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &L> {
        self.nodes.iter()
    }

    /// Iterates over the non-canonical ids of parent enodes of this eclass.
    pub fn parents(&self) -> impl ExactSizeIterator<Item = Id> + '_ {
        self.parents.iter().copied()
    }
}

impl<L: Language, D> EClass<L, D> {
    /// Iterates over the childless enodes in this eclass.
    pub fn leaves(&self) -> impl Iterator<Item = &L> {
        self.nodes.iter().filter(|&n| n.is_leaf())
    }

    /// Asserts that the childless enodes in this eclass are unique.
    pub fn assert_unique_leaves(&self)
    where
        L: Language,
    {
        let mut leaves = self.leaves();
        if let Some(first) = leaves.next() {
            assert!(
                leaves.all(|l| l == first),
                "Different leaves in eclass {}: {:?}",
                self.id,
                self.leaves().collect::<crate::util::HashSet<_>>()
            );
        }
    }

    /// Run some function on each matching e-node in this class.
    pub fn for_each_matching_node<Err>(
        &self,
        node: &L,
        mut f: impl FnMut(&L) -> Result<(), Err>,
    ) -> Result<(), Err>
    where
        L: Language,
    {
        if self.nodes.len() < 50 {
            self.nodes
                .iter()
                .filter(|n| node.matches(n))
                .try_for_each(f)
        } else {
            debug_assert!(node.all(|id| id == Id::from(0)));
            debug_assert!(self.nodes.windows(2).all(|w| w[0] < w[1]));
            let mut start = self.nodes.binary_search(node).unwrap_or_else(|i| i);
            let discrim = node.discriminant();
            while start > 0 {
                if self.nodes[start - 1].discriminant() == discrim {
                    start -= 1;
                } else {
                    break;
                }
            }
            let mut matching = self.nodes[start..]
                .iter()
                .take_while(|&n| n.discriminant() == discrim)
                .filter(|n| node.matches(n));
            debug_assert_eq!(
                matching.clone().count(),
                self.nodes.iter().filter(|n| node.matches(n)).count(),
                "matching node {:?}\nstart={}\n{:?} != {:?}\nnodes: {:?}",
                node,
                start,
                matching.clone().collect::<HashSet<_>>(),
                self.nodes
                    .iter()
                    .filter(|n| node.matches(n))
                    .collect::<HashSet<_>>(),
                self.nodes
            );
            matching.try_for_each(&mut f)
        }
    }
}
