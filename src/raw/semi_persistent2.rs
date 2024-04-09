use crate::raw::{AsUnwrap, RawEClass, RawEGraph, Sealed, UndoLogT};
use crate::util::{Entry, HashSet};
use crate::{Id, Language};
use std::fmt::Debug;

#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
struct UndoNode {
    /// Other ENodes that were unioned with this ENode and chose it as their representative
    representative_of: Vec<Id>,
    /// Non-canonical Id's of direct parents of this non-canonical node
    parents: Vec<Id>,
}

fn visit_undo_node(id: Id, undo_find: &[UndoNode], f: &mut impl FnMut(Id, &UndoNode)) {
    let node = &undo_find[usize::from(id)];
    f(id, node);
    node.representative_of
        .iter()
        .for_each(|&id| visit_undo_node(id, undo_find, &mut *f))
}

/// Stored information required to restore the egraph to a previous state
///
/// see [`push2`](RawEGraph::push2) and [`pop2`](RawEGraph::pop2)
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct PushInfo {
    node_count: u32,
    union_count: u32,
    memo_log_count: u32,
    pop_parents_count: u32,
    congr_dup_count: u32,
}

impl PushInfo {
    /// Returns the result of [`EGraphResidual::number_of_uncanonical_nodes`](super::EGraphResidual::number_of_uncanonical_nodes)
    /// from the state where `self` was created
    pub fn number_of_uncanonical_nodes(&self) -> usize {
        self.node_count as usize
    }

    /// Returns the number of unions from the state where `self` was created
    pub fn number_of_unions(&self) -> usize {
        self.union_count as usize
    }
}

/// Value for [`UndoLogT`] that enables [`push2`](RawEGraph::push2) and [`raw_pop2`](RawEGraph::raw_pop2)
#[derive(Clone, Debug, Default)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct UndoLog {
    undo_find: Vec<UndoNode>,
    union_log: Vec<Id>,
    memo_log: Vec<u64>,
    pop_parents: Vec<Id>,
    congr_dup_log: Vec<Id>,
    // Scratch space, should be empty other that when inside `pop`
    #[cfg_attr(feature = "serde-1", serde(skip))]
    dirty: HashSet<Id>,
}

impl Sealed for UndoLog {}

impl<L: Language, D> UndoLogT<L, D> for UndoLog {
    fn add_node(&mut self, _: &L, canon: &[Id], node_id: Id) {
        debug_assert_eq!(self.undo_find.len(), usize::from(node_id));
        self.undo_find.push(UndoNode::default());
        for id in canon {
            self.undo_find[usize::from(*id)].parents.push(node_id)
        }
        self.pop_parents.extend(canon)
    }

    fn union(&mut self, id1: Id, id2: Id, _: Vec<Id>) {
        self.undo_find[usize::from(id1)].representative_of.push(id2);
        self.union_log.push(id1)
    }

    fn insert_memo(&mut self, hash: u64) {
        self.memo_log.push(hash);
    }

    fn add_congruence_duplicate(&mut self, id: Id) {
        self.congr_dup_log.push(id);
    }

    fn clear(&mut self) {
        self.union_log.clear();
        self.memo_log.clear();
        self.undo_find.clear();
        self.congr_dup_log.clear();
    }

    fn is_enabled(&self) -> bool {
        true
    }
}

impl<L: Language, D, U: AsUnwrap<UndoLog>> RawEGraph<L, D, U> {
    /// Create a [`PushInfo`] representing the current state of the egraph
    /// which can later be passed into [`raw_pop2`](RawEGraph::raw_pop2)
    ///
    /// Requires [`self.is_clean()`](RawEGraph::is_clean)
    ///
    /// # Example
    /// ```
    /// use egg::{raw::*, SymbolLang as S};
    /// use egg::raw::semi_persistent2::UndoLog;
    /// let mut egraph = RawEGraph::<S, (), UndoLog>::default();
    /// let a = egraph.add_uncanonical(S::leaf("a"));
    /// let fa = egraph.add_uncanonical(S::new("f", vec![a]));
    /// let c = egraph.add_uncanonical(S::leaf("c"));
    /// egraph.rebuild();
    /// assert_eq!(egraph.number_of_classes(), 3);
    /// assert_eq!(egraph.number_of_uncanonical_nodes(), 3);
    /// assert_eq!(egraph.total_size(), 3);
    /// let restore_point = egraph.push2();
    /// let b = egraph.add_uncanonical(S::leaf("b"));
    /// let _fb = egraph.add_uncanonical(S::new("g", vec![b]));
    /// egraph.union(b, a);
    /// egraph.union(b, c);
    /// egraph.rebuild();
    /// assert_eq!(egraph.find(a), b);
    /// assert_eq!(egraph.number_of_classes(), 3);
    /// assert_eq!(egraph.number_of_uncanonical_nodes(), 5);
    /// assert_eq!(egraph.total_size(), 6);
    /// egraph.pop2(restore_point);
    /// assert_ne!(egraph.find(a), b);
    /// assert_eq!(egraph.lookup(S::leaf("a")), Some(a));
    /// assert_eq!(egraph.lookup(S::new("f", vec![a])), Some(fa));
    /// assert_eq!(egraph.lookup(S::leaf("b")), None);
    /// assert_eq!(egraph.number_of_classes(), 3);
    /// assert_eq!(egraph.number_of_uncanonical_nodes(), 3);
    /// assert_eq!(egraph.total_size(), 3);
    /// ```
    pub fn push2(&self) -> PushInfo {
        assert!(self.is_clean());
        let undo = self.undo_log.as_unwrap();
        PushInfo {
            node_count: undo.undo_find.len() as u32,
            union_count: undo.union_log.len() as u32,
            memo_log_count: undo.memo_log.len() as u32,
            pop_parents_count: undo.pop_parents.len() as u32,
            congr_dup_count: undo.congr_dup_log.len() as u32,
        }
    }

    /// Mostly restores the egraph to the state it was it when it called [`push2`](RawEGraph::push2)
    /// to create `info`
    ///
    /// Invalidates all [`PushInfo`]s that were created after `info`
    ///
    /// The `raw_data` fields of the [`RawEClass`]s are not properly restored
    /// Instead all eclasses that have were merged into another eclass are recreated with `mk_data` and
    /// `clear` is called eclass that had another eclass merged into them
    ///
    /// After each call to either `mk_data` or `clear`, `handle_eqv` is called on each id that is in
    /// the eclass (that was handled by `mk_data` or `clear`
    ///
    /// The `state` parameter represents arbitrary state that be accessed in any of the closures
    pub fn raw_pop2<T>(
        &mut self,
        info: PushInfo,
        state: &mut T,
        clear: impl FnMut(&mut T, &mut D, Id, UndoCtx<'_, L>),
        mk_data: impl FnMut(&mut T, Id, UndoCtx<'_, L>) -> D,
        handle_eqv: impl FnMut(&mut T, &mut D, Id, UndoCtx<'_, L>),
    ) {
        let PushInfo {
            node_count,
            union_count,
            memo_log_count,
            pop_parents_count,
            congr_dup_count,
        } = info;
        self.pending.clear();
        for id in self
            .undo_log
            .as_mut_unwrap()
            .congr_dup_log
            .drain(congr_dup_count as usize..)
        {
            self.congruence_duplicates.remove(id.into());
        }
        self.pending.clear();
        self.pop_memo2(memo_log_count as usize);
        self.pop_parents2(pop_parents_count as usize);
        self.pop_unions2(
            union_count as usize,
            node_count as usize,
            state,
            clear,
            mk_data,
            handle_eqv,
        );
        self.pop_nodes2(node_count as usize);
    }

    fn pop_memo2(&mut self, old_count: usize) {
        assert!(self.memo.len() >= old_count);
        let memo_log = &mut self.undo_log.as_mut_unwrap().memo_log;
        let len = memo_log.len();
        for (hash, idx) in memo_log.drain(old_count..).zip(old_count..len).rev() {
            self.residual.memo.remove_nth(hash, idx);
        }
    }

    fn pop_parents2(&mut self, old_count: usize) {
        let undo = self.undo_log.as_mut_unwrap();

        for id in undo.pop_parents.drain(old_count..) {
            if let Some(x) = self.classes.get_mut(&id) {
                // Pop canonical parents from classes in egraph
                // Note, if `id` is not canonical then its class must have been merged into another class so it's parents will
                // be rebuilt anyway
                // If another class was merged into `id` we will be popping an incorrect parent, but again it's parents will
                // be rebuilt anyway
                x.parents.pop();
            }
            // Undo additions to undo_find parents
            let parents = &mut undo.undo_find[usize::from(id)].parents;
            parents.pop();
        }
    }

    fn pop_unions2<T>(
        &mut self,
        old_count: usize,
        node_count: usize,
        state: &mut T,
        mut clear: impl FnMut(&mut T, &mut D, Id, UndoCtx<'_, L>),
        mut mk_data: impl FnMut(&mut T, Id, UndoCtx<'_, L>) -> D,
        mut handle_eqv: impl FnMut(&mut T, &mut D, Id, UndoCtx<'_, L>),
    ) {
        let undo = self.undo_log.as_mut_unwrap();
        assert!(undo.union_log.len() >= old_count);
        for id in undo.union_log.drain(old_count..) {
            let id2 = undo.undo_find[usize::from(id)]
                .representative_of
                .pop()
                .unwrap();
            for id in [id, id2] {
                if usize::from(id) < node_count {
                    undo.dirty.insert(id);
                }
            }
        }
        let ctx = UndoCtx {
            nodes: &self.residual.nodes[..node_count],
            undo_find: &undo.undo_find[..node_count],
        };
        for root in undo.dirty.iter().copied() {
            let union_find = &mut self.residual.unionfind;
            let class = match self.classes.entry(root) {
                Entry::Vacant(vac) => {
                    let default = RawEClass {
                        id: root,
                        raw_data: mk_data(state, root, ctx),
                        parents: Default::default(),
                    };
                    vac.insert(default)
                }
                Entry::Occupied(occ) => {
                    let res = occ.into_mut();
                    clear(state, &mut res.raw_data, root, ctx);
                    res.parents.clear();
                    res
                }
            };
            class.parents.clear();
            let parents = &mut class.parents;
            let data = &mut class.raw_data;
            visit_undo_node(root, &undo.undo_find, &mut |id, node| {
                union_find.parents[usize::from(id)] = root;
                parents.extend(&node.parents);
                handle_eqv(state, data, id, ctx)
            });
            // If we call pop again we need parents added more recently at the end
            parents.sort_unstable();
        }
        undo.dirty.clear();
    }

    fn pop_nodes2(&mut self, old_count: usize) {
        assert!(self.number_of_uncanonical_nodes() >= old_count);
        for id in (old_count..self.number_of_uncanonical_nodes()).map(Id::from) {
            if self.find(id) == id {
                self.classes.remove(&id);
            }
        }
        self.residual.nodes.truncate(old_count);
        self.undo_log.as_mut_unwrap().undo_find.truncate(old_count);
        self.residual.unionfind.parents.truncate(old_count);
    }

    /// Returns the [`UndoCtx`] corresponding to the current egraph
    pub fn undo_ctx(&self) -> UndoCtx<'_, L> {
        UndoCtx {
            nodes: &self.nodes,
            undo_find: &self.undo_log.as_unwrap().undo_find,
        }
    }
}

/// The egraph is in a partially broken state during a call to [`RawEGraph::raw_pop2`] so the passed in closures
/// are given this struct which represents the aspects of the egraph that are currently usable
pub struct UndoCtx<'a, L> {
    nodes: &'a [L],
    undo_find: &'a [UndoNode],
}

impl<'a, L> Copy for UndoCtx<'a, L> {}

impl<'a, L> Clone for UndoCtx<'a, L> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, L> UndoCtx<'a, L> {
    /// Calls `f` on all nodes that are equivalent to `id`
    ///
    /// Requires `id` to be canonical
    pub fn equivalent_nodes(self, id: Id, mut f: impl FnMut(Id)) {
        visit_undo_node(id, self.undo_find, &mut |id, _| f(id))
    }

    /// Returns an iterator of the uncanonical ids of nodes that contain the uncanonical id `id`
    pub fn direct_parents(self, id: Id) -> impl ExactSizeIterator<Item = Id> + 'a {
        self.undo_find[usize::from(id)].parents.iter().copied()
    }

    /// See [`EGraphResidual::id_to_node`](super::EGraphResidual::id_to_node)
    pub fn id_to_node(self, id: Id) -> &'a L {
        &self.nodes[usize::from(id)]
    }

    /// See [`EGraphResidual::number_of_uncanonical_nodes`](super::EGraphResidual::number_of_uncanonical_nodes)
    pub fn number_of_uncanonical_nodes(self) -> usize {
        self.nodes.len()
    }
}

impl<L: Language, U: AsUnwrap<UndoLog>> RawEGraph<L, (), U> {
    /// Simplified version of [`raw_pop2`](RawEGraph::raw_pop2) for egraphs without eclass data
    pub fn pop2(&mut self, info: PushInfo) {
        self.raw_pop2(
            info,
            &mut (),
            |_, _, _, _| {},
            |_, _, _| (),
            |_, _, _, _| {},
        )
    }
}
