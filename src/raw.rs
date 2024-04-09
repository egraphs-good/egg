mod dhashmap;
mod eclass;
mod egraph;
mod semi_persistent;

/// One variant of semi_persistence
pub mod semi_persistent1;

mod bitset;
/// Another variant of semi_persistence
pub mod semi_persistent2;
mod unionfind;

pub use eclass::RawEClass;
pub use egraph::{EGraphResidual, RawEGraph, UnionInfo};
use semi_persistent::Sealed;
pub use semi_persistent::{AsUnwrap, UndoLogT};
pub use unionfind::UnionFind;
