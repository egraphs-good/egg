use crate::Id;
use std::fmt::Debug;
use std::iter::ExactSizeIterator;
use std::ops::{Deref, DerefMut};

/// An equivalence class of enodes.
#[non_exhaustive]
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct RawEClass<D> {
    /// This eclass's id.
    pub id: Id,
    /// Arbitrary data associated with this eclass.
    pub(super) raw_data: D,
    /// The original Ids of parent enodes.
    pub(super) parents: Vec<Id>,
}

impl<D> RawEClass<D> {
    /// Iterates over the non-canonical ids of parent enodes of this eclass.
    pub fn parents(&self) -> impl ExactSizeIterator<Item = Id> + '_ {
        self.parents.iter().copied()
    }

    /// Consumes `self` returning the stored data and an iterator similar to [`parents`](RawEClass::parents)
    pub fn destruct(self) -> (D, impl ExactSizeIterator<Item = Id>) {
        (self.raw_data, self.parents.into_iter())
    }
}

impl<D> Deref for RawEClass<D> {
    type Target = D;

    fn deref(&self) -> &D {
        &self.raw_data
    }
}

impl<D> DerefMut for RawEClass<D> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.raw_data
    }
}
