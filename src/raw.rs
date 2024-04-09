mod dhashmap;
mod eclass;
mod egraph;
mod semi_persistent;

/// One variant of semi_persistence
pub mod semi_persistent1;

mod bitset;
pub(crate) mod language;
/// Another variant of semi_persistence
pub mod semi_persistent2;
mod unionfind;
pub(crate) mod util;

pub use eclass::RawEClass;
pub use egraph::{EGraphResidual, RawEGraph, UnionInfo};
pub use language::*;
use semi_persistent::Sealed;
pub use semi_persistent::{AsUnwrap, UndoLogT};
pub use unionfind::UnionFind;
