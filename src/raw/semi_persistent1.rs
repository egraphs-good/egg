use crate::raw::{AsUnwrap, RawEClass, RawEGraph, Sealed, UndoLogT, UnionFind};
use crate::{Id, Language};
use std::fmt::Debug;

/// Stored information required to restore the egraph to a previous state
///
/// see [`push1`](RawEGraph::push1) and [`pop1`](RawEGraph::pop1)
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct PushInfo {
    node_count: usize,
    union_count: usize,
    memo_log_count: usize,
    pop_parents_count: usize,
}

impl PushInfo {
    /// Returns the result of [`EGraphResidual::number_of_uncanonical_nodes`](super::EGraphResidual::number_of_uncanonical_nodes)
    /// from the state where `self` was created
    pub fn number_of_uncanonical_nodes(&self) -> usize {
        self.node_count
    }
}

#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
struct UnionInfo {
    old_id: Id,
    old_parents: Vec<Id>,
    added_after: u32,
}

/// Value for [`UndoLogT`] that enables [`push1`](RawEGraph::push1) and [`raw_pop1`](RawEGraph::raw_pop1)
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct UndoLog {
    // Mirror of the union find without path compression
    undo_find: UnionFind,
    pop_parents: Vec<Id>,
    union_log: Vec<UnionInfo>,
    memo_log: Vec<u64>,
}

impl Default for UndoLog {
    fn default() -> Self {
        UndoLog {
            undo_find: Default::default(),
            pop_parents: Default::default(),
            union_log: vec![UnionInfo {
                old_id: Id::from(0),
                old_parents: vec![],
                added_after: 0,
            }],
            memo_log: Default::default(),
        }
    }
}

impl Sealed for UndoLog {}

impl<L: Language, D> UndoLogT<L, D> for UndoLog {
    fn add_node(&mut self, _: &L, canon_children: &[Id], node_id: Id) {
        let new = self.undo_find.make_set();
        debug_assert_eq!(new, node_id);
        self.pop_parents.extend(canon_children);
        self.union_log.last_mut().unwrap().added_after += canon_children.len() as u32;
    }

    fn union(&mut self, id1: Id, id2: Id, old_parents: Vec<Id>) {
        self.undo_find.union(id1, id2);
        self.union_log.push(UnionInfo {
            old_id: id2,
            added_after: 0,
            old_parents,
        })
    }

    fn insert_memo(&mut self, hash: u64) {
        self.memo_log.push(hash);
    }

    fn clear(&mut self) {
        self.union_log.truncate(1);
        self.union_log[0].added_after = 0;
        self.memo_log.clear();
        self.undo_find.clear();
    }

    #[inline]
    fn is_enabled(&self) -> bool {
        true
    }
}

impl<L: Language, D, U: AsUnwrap<UndoLog>> RawEGraph<L, D, U> {
    /// Create a [`PushInfo`] representing the current state of the egraph
    /// which can later be passed into [`raw_pop1`](RawEGraph::raw_pop1)
    ///
    /// Requires [`self.is_clean()`](RawEGraph::is_clean)
    ///
    /// # Example
    /// ```
    /// use egg::{raw::*, SymbolLang as S};
    /// use egg::raw::semi_persistent1::UndoLog;
    /// let mut egraph = RawEGraph::<S, (), UndoLog>::default();
    /// let a = egraph.add_uncanonical(S::leaf("a"));
    /// let fa = egraph.add_uncanonical(S::new("f", vec![a]));
    /// let c = egraph.add_uncanonical(S::leaf("c"));
    /// egraph.rebuild();
    /// let old = egraph.clone();
    /// let restore_point = egraph.push1();
    /// let b = egraph.add_uncanonical(S::leaf("b"));
    /// let _fb = egraph.add_uncanonical(S::new("g", vec![b]));
    /// egraph.union(b, a);
    /// egraph.union(b, c);
    /// egraph.rebuild();
    /// egraph.pop1(restore_point);
    /// assert_eq!(format!("{:#?}", egraph.dump_uncanonical()), format!("{:#?}", old.dump_uncanonical()));
    /// assert_eq!(format!("{:#?}", egraph), format!("{:#?}", old));
    /// ```
    pub fn push1(&self) -> PushInfo {
        assert!(self.is_clean());
        let undo = self.undo_log.as_unwrap();
        PushInfo {
            node_count: self.number_of_uncanonical_nodes(),
            union_count: undo.union_log.len(),
            memo_log_count: undo.memo_log.len(),
            pop_parents_count: undo.pop_parents.len(),
        }
    }

    /// Mostly restores the egraph to the state it was it when it called [`push1`](RawEGraph::push1)
    /// to create `info`
    ///
    /// Invalidates all [`PushInfo`]s that were created after `info`
    ///
    /// The `raw_data` fields of the [`RawEClass`]s are not properly restored
    /// Instead, `split` is called to undo each union with a mutable reference to the merged data, and the two ids
    /// that were merged to create the data for the eclass of the second `id` (the eclass of the first `id` will
    /// be what's left of the merged data after the call)
    pub fn raw_pop1(&mut self, info: PushInfo, split: impl FnMut(&mut D, Id, Id) -> D) {
        let PushInfo {
            node_count,
            union_count,
            memo_log_count,
            pop_parents_count,
        } = info;
        self.pop_memo1(memo_log_count);
        self.pop_unions1(union_count, pop_parents_count, split);
        self.pop_nodes1(node_count);
    }

    fn pop_memo1(&mut self, old_count: usize) {
        assert!(self.memo.len() >= old_count);
        let memo_log = &mut self.undo_log.as_mut_unwrap().memo_log;
        let len = memo_log.len();
        for (hash, idx) in memo_log.drain(old_count..).zip(old_count..len).rev() {
            self.residual.memo.remove_nth(hash, idx);
        }
    }

    fn pop_unions1(
        &mut self,
        old_count: usize,
        pop_parents_count: usize,
        mut split: impl FnMut(&mut D, Id, Id) -> D,
    ) {
        let undo = self.undo_log.as_mut_unwrap();
        assert!(self.residual.number_of_uncanonical_nodes() >= old_count);
        for info in undo.union_log.drain(old_count..).rev() {
            for _ in 0..info.added_after {
                let id = undo.pop_parents.pop().unwrap();
                self.classes.get_mut(&id).unwrap().parents.pop();
            }
            let old_id = info.old_id;
            let new_id = undo.undo_find.parent(old_id);
            debug_assert_ne!(new_id, old_id);
            debug_assert_eq!(undo.undo_find.find(new_id), new_id);
            *undo.undo_find.parent_mut(old_id) = old_id;
            let new_class = &mut self.classes.get_mut(&new_id).unwrap();
            let cut = new_class.parents.len() - info.old_parents.len();
            debug_assert_eq!(&new_class.parents[cut..], &info.old_parents);
            new_class.parents.truncate(cut);
            let old_data = split(&mut new_class.raw_data, new_id, old_id);
            self.classes.insert(
                old_id,
                RawEClass {
                    id: old_id,
                    raw_data: old_data,
                    parents: info.old_parents,
                },
            );
        }
        let rem = undo.pop_parents.len() - pop_parents_count;
        for _ in 0..rem {
            let id = undo.pop_parents.pop().unwrap();
            self.classes.get_mut(&id).unwrap().parents.pop();
        }
        undo.union_log.last_mut().unwrap().added_after -= rem as u32;
    }

    fn pop_nodes1(&mut self, old_count: usize) {
        assert!(self.number_of_uncanonical_nodes() >= old_count);
        let undo = self.undo_log.as_mut_unwrap();
        undo.undo_find.parents.truncate(old_count);
        self.residual
            .unionfind
            .parents
            .clone_from(&undo.undo_find.parents);
        for id in (old_count..self.number_of_uncanonical_nodes()).map(Id::from) {
            self.classes.remove(&id);
        }
        self.residual.nodes.truncate(old_count);
    }
}

impl<L: Language, U: AsUnwrap<UndoLog>> RawEGraph<L, (), U> {
    /// Simplified version of [`raw_pop1`](RawEGraph::raw_pop1) for egraphs without eclass data
    pub fn pop1(&mut self, info: PushInfo) {
        self.raw_pop1(info, |_, _, _| ())
    }
}
