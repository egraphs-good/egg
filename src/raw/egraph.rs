use crate::{raw::RawEClass, Dot, HashMap, Id, Language, RecExpr, UnionFind};
use std::ops::{Deref, DerefMut};
use std::{
    borrow::BorrowMut,
    fmt::{self, Debug},
};

#[cfg(feature = "serde-1")]
use serde::{Deserialize, Serialize};

/// A [`RawEGraph`] without its classes that can be obtained by dereferencing a [`RawEGraph`].
///
/// It exists as a separate type so that it can still be used while mutably borrowing a [`RawEClass`]
///
/// See [`RawEGraph::classes_mut`], [`RawEGraph::get_class_mut`]
#[derive(Clone)]
#[cfg_attr(feature = "serde-1", derive(Serialize, Deserialize))]
pub struct EGraphResidual<L: Language> {
    unionfind: UnionFind,
    /// Stores the original node represented by each non-canonical id
    nodes: Vec<L>,
    /// Stores each enode's `Id`, not the `Id` of the eclass.
    /// Enodes in the memo are canonicalized at each rebuild, but after rebuilding new
    /// unions can cause them to become out of date.
    #[cfg_attr(feature = "serde-1", serde(with = "vectorize"))]
    memo: HashMap<L, Id>,
}

impl<L: Language> EGraphResidual<L> {
    /// Pick a representative term for a given Id.
    ///
    /// Calling this function on an uncanonical `Id` returns a representative based on how it
    /// was obtained
    pub fn id_to_expr(&self, id: Id) -> RecExpr<L> {
        let mut res = Default::default();
        let mut cache = Default::default();
        self.id_to_expr_internal(&mut res, id, &mut cache);
        res
    }

    fn id_to_expr_internal(
        &self,
        res: &mut RecExpr<L>,
        node_id: Id,
        cache: &mut HashMap<Id, Id>,
    ) -> Id {
        if let Some(existing) = cache.get(&node_id) {
            return *existing;
        }
        let new_node = self
            .id_to_node(node_id)
            .clone()
            .map_children(|child| self.id_to_expr_internal(res, child, cache));
        let res_id = res.add(new_node);
        cache.insert(node_id, res_id);
        res_id
    }

    /// Like [`id_to_expr`](EGraph::id_to_expr) but only goes one layer deep
    pub fn id_to_node(&self, id: Id) -> &L {
        &self.nodes[usize::from(id)]
    }

    /// Canonicalizes an eclass id.
    ///
    /// This corresponds to the `find` operation on the egraph's
    /// underlying unionfind data structure.
    ///
    /// # Example
    /// ```
    /// use egg::{raw::*, SymbolLang as S};
    /// let mut egraph = RawEGraph::<S, ()>::default();
    /// let x = egraph.add_uncanonical(S::leaf("x"));
    /// let y = egraph.add_uncanonical(S::leaf("y"));
    /// assert_ne!(egraph.find(x), egraph.find(y));
    ///
    /// egraph.union(x, y);
    /// egraph.rebuild();
    /// assert_eq!(egraph.find(x), egraph.find(y));
    /// ```
    pub fn find(&self, id: Id) -> Id {
        self.unionfind.find(id)
    }

    /// Same as [`find`](EGraphResidual::find) but requires mutable access since it does path compression
    pub fn find_mut(&mut self, id: Id) -> Id {
        self.unionfind.find_mut(id)
    }

    /// Returns `true` if the egraph is empty
    /// # Example
    /// ```
    /// use egg::{raw::*, SymbolLang as S};
    /// let mut egraph = RawEGraph::<S, ()>::default();
    /// assert!(egraph.is_empty());
    /// egraph.add_uncanonical(S::leaf("foo"));
    /// assert!(!egraph.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Returns the number of uncanonical enodes in the `EGraph`.
    ///
    /// # Example
    /// ```
    /// use egg::{raw::*, SymbolLang as S};
    /// let mut egraph = RawEGraph::<S, ()>::default();
    /// let x = egraph.add_uncanonical(S::leaf("x"));
    /// let y = egraph.add_uncanonical(S::leaf("y"));
    /// let fx = egraph.add_uncanonical(S::new("f", vec![x]));
    /// let fy = egraph.add_uncanonical(S::new("f", vec![y]));
    /// // only one eclass
    /// egraph.union(x, y);
    /// egraph.rebuild();
    ///
    /// assert_eq!(egraph.number_of_uncanonical_nodes(), 4);
    /// assert_eq!(egraph.number_of_classes(), 2);
    /// ```
    pub fn number_of_uncanonical_nodes(&self) -> usize {
        self.nodes.len()
    }

    /// Returns an iterator over the uncanonical ids in the egraph and the node
    /// that would be obtained by calling [`id_to_node`](EGraphResidual::id_to_node) on each of them
    pub fn uncanonical_nodes(&self) -> impl ExactSizeIterator<Item = (Id, &L)> {
        self.nodes
            .iter()
            .enumerate()
            .map(|(id, node)| (Id::from(id), node))
    }

    /// Returns the number of enodes in the `EGraph`.
    ///
    /// Actually returns the size of the hashcons index.
    /// # Example
    /// ```
    /// use egg::{*, SymbolLang as S};
    /// let mut egraph = EGraph::<S, ()>::default();
    /// let x = egraph.add(S::leaf("x"));
    /// let y = egraph.add(S::leaf("y"));
    /// // only one eclass
    /// egraph.union(x, y);
    /// egraph.rebuild();
    ///
    /// assert_eq!(egraph.total_size(), 2);
    /// assert_eq!(egraph.number_of_classes(), 1);
    /// ```
    pub fn total_size(&self) -> usize {
        self.memo.len()
    }

    /// Lookup the eclass of the given enode.
    ///
    /// You can pass in either an owned enode or a `&mut` enode,
    /// in which case the enode's children will be canonicalized.
    ///
    /// # Example
    /// ```
    /// # use egg::*;
    /// let mut egraph: EGraph<SymbolLang, ()> = Default::default();
    /// let a = egraph.add(SymbolLang::leaf("a"));
    /// let b = egraph.add(SymbolLang::leaf("b"));
    ///
    /// // lookup will find this node if its in the egraph
    /// let mut node_f_ab = SymbolLang::new("f", vec![a, b]);
    /// assert_eq!(egraph.lookup(node_f_ab.clone()), None);
    /// let id = egraph.add(node_f_ab.clone());
    /// assert_eq!(egraph.lookup(node_f_ab.clone()), Some(id));
    ///
    /// // if the query node isn't canonical, and its passed in by &mut instead of owned,
    /// // its children will be canonicalized
    /// egraph.union(a, b);
    /// egraph.rebuild();
    /// assert_eq!(egraph.lookup(&mut node_f_ab), Some(id));
    /// assert_eq!(node_f_ab, SymbolLang::new("f", vec![a, a]));
    /// ```
    pub fn lookup<B>(&self, enode: B) -> Option<Id>
    where
        B: BorrowMut<L>,
    {
        self.lookup_internal(enode).map(|id| self.find(id))
    }

    #[inline]
    fn lookup_internal<B>(&self, mut enode: B) -> Option<Id>
    where
        B: BorrowMut<L>,
    {
        let enode = enode.borrow_mut();
        enode.update_children(|id| self.find(id));
        self.memo.get(enode).copied()
    }

    /// Lookup the eclass of the given [`RecExpr`].
    ///
    /// Equivalent to the last value in [`EGraphResidual::lookup_expr_ids`].
    pub fn lookup_expr(&self, expr: &RecExpr<L>) -> Option<Id> {
        self.lookup_expr_ids(expr)
            .and_then(|ids| ids.last().copied())
    }

    /// Lookup the eclasses of all the nodes in the given [`RecExpr`].
    pub fn lookup_expr_ids(&self, expr: &RecExpr<L>) -> Option<Vec<Id>> {
        let nodes = expr.as_ref();
        let mut new_ids = Vec::with_capacity(nodes.len());
        for node in nodes {
            let node = node.clone().map_children(|i| new_ids[usize::from(i)]);
            let id = self.lookup(node)?;
            new_ids.push(id)
        }
        Some(new_ids)
    }

    /// Generate a mapping from canonical ids to the list of nodes they represent
    pub fn generate_class_nodes(&self) -> HashMap<Id, Vec<L>> {
        let mut classes = HashMap::default();
        let find = |id| self.find(id);
        for (id, node) in self.uncanonical_nodes() {
            let id = find(id);
            let node = node.clone().map_children(find);
            match classes.get_mut(&id) {
                None => {
                    classes.insert(id, vec![node]);
                }
                Some(x) => x.push(node),
            }
        }

        // define all the nodes, clustered by eclass
        for class in classes.values_mut() {
            class.sort_unstable();
            class.dedup();
        }
        classes
    }

    /// Returns a more debug-able representation of the egraph focusing on its uncanonical ids and nodes.
    ///
    /// [`EGraph`]s implement [`Debug`], but it ain't pretty. It
    /// prints a lot of stuff you probably don't care about.
    /// This method returns a wrapper that implements [`Debug`] in a
    /// slightly nicer way, just dumping enodes in each eclass.
    ///
    /// [`Debug`]: std::fmt::Debug
    pub fn dump_uncanonical(&self) -> impl Debug + '_ {
        EGraphUncanonicalDump(self)
    }

    /// Creates a [`Dot`] to visualize this egraph. See [`Dot`].
    pub fn dot(&self) -> Dot<'_, L> {
        Dot {
            egraph: self,
            config: vec![],
            use_anchors: true,
        }
    }
}

// manual debug impl to avoid L: Language bound on EGraph defn
impl<L: Language> Debug for EGraphResidual<L> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("EGraphResidual")
            .field("unionfind", &self.unionfind)
            .field("nodes", &self.nodes)
            .field("memo", &self.memo)
            .finish()
    }
}

/** A data structure to keep track of equalities between expressions.

Check out the [background tutorial](crate::tutorials::_01_background)
for more information on e-graphs in general.

# E-graphs in `egg::raw`

In `egg::raw`, the main types associated with e-graphs are
[`RawEGraph`], [`RawEClass`], [`Language`], and [`Id`].

[`RawEGraph`] and [`RawEClass`] are all generic over a
[`Language`], meaning that types actually floating around in the
egraph are all user-defined.
In particular, the e-nodes are elements of your [`Language`].
[`RawEGraph`]s and [`RawEClass`]es are additionally parameterized by some
abritrary data associated with each e-class.

Many methods of [`RawEGraph`] deal with [`Id`]s, which represent e-classes.
Because eclasses are frequently merged, many [`Id`]s will refer to the
same e-class.

[`RawEGraph`] provides a low level API for dealing with egraphs, in particular with handling the data
stored in each [`RawEClass`] so user will likely want to implemented wrappers around
[`raw_add`](RawEGraph::raw_add), [`raw_union`](RawEGraph::raw_union), and [`raw_rebuild`](RawEGraph::raw_rebuild)
to properly handle this data
 **/
#[derive(Clone)]
#[cfg_attr(feature = "serde-1", derive(Serialize, Deserialize))]
pub struct RawEGraph<L: Language, D> {
    #[cfg_attr(feature = "serde-1", serde(flatten))]
    residual: EGraphResidual<L>,
    /// Nodes which need to be processed for rebuilding. The `Id` is the `Id` of the enode,
    /// not the canonical id of the eclass.
    pending: Vec<Id>,
    classes: HashMap<Id, RawEClass<D>>,
}

impl<L: Language, D> Default for RawEGraph<L, D> {
    fn default() -> Self {
        let residual = EGraphResidual {
            unionfind: Default::default(),
            nodes: Default::default(),
            memo: Default::default(),
        };
        RawEGraph {
            residual,
            pending: Default::default(),
            classes: Default::default(),
        }
    }
}

impl<L: Language, D> Deref for RawEGraph<L, D> {
    type Target = EGraphResidual<L>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.residual
    }
}

impl<L: Language, D> DerefMut for RawEGraph<L, D> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.residual
    }
}

// manual debug impl to avoid L: Language bound on EGraph defn
impl<L: Language, D: Debug> Debug for RawEGraph<L, D> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("EGraph")
            .field("memo", &self.residual.memo)
            .field("classes", &self.classes)
            .finish()
    }
}

impl<L: Language, D> RawEGraph<L, D> {
    /// Returns an iterator over the eclasses in the egraph.
    pub fn classes(&self) -> impl ExactSizeIterator<Item = &RawEClass<D>> {
        self.classes.iter().map(|(id, class)| {
            debug_assert_eq!(*id, class.id);
            class
        })
    }

    /// Returns a mutating iterator over the eclasses in the egraph.
    /// Also returns the [`EGraphResidual`] so it can still be used while `self` is borrowed
    pub fn classes_mut(
        &mut self,
    ) -> (
        impl ExactSizeIterator<Item = &mut RawEClass<D>>,
        &mut EGraphResidual<L>,
    ) {
        let iter = self.classes.iter_mut().map(|(id, class)| {
            debug_assert_eq!(*id, class.id);
            class
        });
        (iter, &mut self.residual)
    }

    /// Returns the number of eclasses in the egraph.
    pub fn number_of_classes(&self) -> usize {
        self.classes().len()
    }

    /// Returns the eclass corresponding to `id`
    pub fn get_class<I: BorrowMut<Id>>(&self, mut id: I) -> &RawEClass<D> {
        let id = id.borrow_mut();
        *id = self.find(*id);
        self.get_class_with_cannon(*id)
    }

    /// Like [`get_class`](RawEGraph::get_class) but panics if `id` is not canonical
    pub fn get_class_with_cannon(&self, id: Id) -> &RawEClass<D> {
        self.classes
            .get(&id)
            .unwrap_or_else(|| panic!("Invalid id {}", id))
    }

    /// Returns the eclass corresponding to `id`
    /// Also returns the [`EGraphResidual`] so it can still be used while `self` is borrowed
    pub fn get_class_mut<I: BorrowMut<Id>>(
        &mut self,
        mut id: I,
    ) -> (&mut RawEClass<D>, &mut EGraphResidual<L>) {
        let id = id.borrow_mut();
        *id = self.find_mut(*id);
        self.get_class_mut_with_cannon(*id)
    }

    /// Like [`get_class_mut`](RawEGraph::get_class_mut) but panics if `id` is not canonical
    pub fn get_class_mut_with_cannon(
        &mut self,
        id: Id,
    ) -> (&mut RawEClass<D>, &mut EGraphResidual<L>) {
        (
            self.classes
                .get_mut(&id)
                .unwrap_or_else(|| panic!("Invalid id {}", id)),
            &mut self.residual,
        )
    }
}

impl<L: Language, D> RawEGraph<L, D> {
    /// Adds `enode` to a [`RawEGraph`] contained within a wrapper type `T`
    ///
    /// ## Parameters
    ///
    /// ### `get_self`
    /// Called to extract the [`RawEGraph`] from the wrapper type, and should not perform any mutation.
    ///
    /// This will likely be a simple field access or just the identity function if there is no wrapper type.
    ///
    /// ### `handle_equiv`
    /// When there already exists a node that is congruently equivalent to `enode` in the egraph
    /// this function is called with the uncanonical id of a equivalent node, and a reference to `enode`
    ///
    /// Returning `Some(id)` will cause `raw_add` to immediately return `id`
    /// (in this case `id` should represent an enode that is equivalent to the one being inserted).
    ///
    /// Returning `None` will cause `raw_add` to create a new id for `enode`, union it to the equivalent node,
    /// and then return it.
    ///
    /// ### `handle_union`
    /// Called after `handle_equiv` returns `None` with the uncanonical id of the equivalent node
    /// and the new `id` assigned to `enode`
    ///
    /// Calling [`id_to_node`](EGraphResidual::id_to_node) on the new `id` will return a reference to `enode`
    ///
    /// ### `mk_data`
    /// When there does not already exist a node  is congruently equivalent to `enode` in the egraph
    /// this function is called with the new `id` assigned to `enode` and a reference to the canonicalized version of
    /// `enode` to create to data that will be stored in the [`RawEClass`] associated with it
    ///
    /// Calling [`id_to_node`](EGraphResidual::id_to_node) on the new `id` will return a reference to `enode`
    ///
    /// Calling [`get_class`](RawEGraph::get_class) on the new `id` will cause a panic since the [`RawEClass`] is
    /// still being built
    #[inline]
    pub fn raw_add<T>(
        outer: &mut T,
        get_self: impl Fn(&mut T) -> &mut Self,
        mut enode: L,
        handle_equiv: impl FnOnce(&mut T, Id, &L) -> Option<Id>,
        handle_union: impl FnOnce(&mut T, Id, Id),
        mk_data: impl FnOnce(&mut T, Id, &L) -> D,
    ) -> Id {
        let this = get_self(outer);
        let original = enode.clone();
        if let Some(existing_id) = this.lookup_internal(&mut enode) {
            let canon_id = this.find(existing_id);
            // when explanations are enabled, we need a new representative for this expr
            if let Some(existing_id) = handle_equiv(outer, existing_id, &original) {
                existing_id
            } else {
                let this = get_self(outer);
                let new_id = this.residual.unionfind.make_set();
                debug_assert_eq!(Id::from(this.nodes.len()), new_id);
                this.residual.nodes.push(original);
                this.residual.unionfind.union(canon_id, new_id);
                handle_union(outer, existing_id, new_id);
                new_id
            }
        } else {
            let id = this.residual.unionfind.make_set();
            debug_assert_eq!(Id::from(this.nodes.len()), id);
            this.residual.nodes.push(original);

            log::trace!("  ...adding to {}", id);
            let class = RawEClass {
                id,
                raw_data: mk_data(outer, id, &enode),
                parents: Default::default(),
            };
            let this = get_self(outer);

            // add this enode to the parent lists of its children
            enode.for_each(|child| {
                this.get_class_mut(child).0.parents.push(id);
            });

            // TODO is this needed?
            this.pending.push(id);

            this.classes.insert(id, class);
            assert!(this.residual.memo.insert(enode, id).is_none());

            id
        }
    }

    /// Unions two eclasses given their ids.
    ///
    /// The given ids need not be canonical.
    ///
    /// Returns `None` if the two ids were already equivalent.
    ///
    /// Returns `Some((id, class))` if two classes were merged where `id` is the id of the newly merged class
    /// and `class` is the old `RawEClass` that merged into `id`
    #[inline]
    pub fn raw_union(&mut self, enode_id1: Id, enode_id2: Id) -> Option<(Id, RawEClass<D>)> {
        let mut id1 = self.find_mut(enode_id1);
        let mut id2 = self.find_mut(enode_id2);
        if id1 == id2 {
            return None;
        }
        // make sure class2 has fewer parents
        let class1_parents = self.classes[&id1].parents.len();
        let class2_parents = self.classes[&id2].parents.len();
        if class1_parents < class2_parents {
            std::mem::swap(&mut id1, &mut id2);
        }

        // make id1 the new root
        self.residual.unionfind.union(id1, id2);

        assert_ne!(id1, id2);
        let class2 = self.classes.remove(&id2).unwrap();
        let class1 = self.classes.get_mut(&id1).unwrap();
        assert_eq!(id1, class1.id);

        self.pending.extend(class2.parents());

        class1.parents.extend(class2.parents());
        Some((id1, class2))
    }

    #[inline]
    /// Rebuild to [`RawEGraph`] to restore congruence closure
    ///
    /// ## Parameters
    ///
    /// ### `get_self`
    /// Called to extract the [`RawEGraph`] from the wrapper type, and should not perform any mutation.
    ///
    /// This will likely be a simple field access or just the identity function if there is no wrapper type.
    ///
    /// ### `perform_union`
    /// Called on each pair of ids that needs to be unioned
    ///
    /// In order to be correct `perform_union` should call [`raw_union`](RawEGraph::raw_union)
    ///
    /// ### `handle_pending`
    /// Called with the uncanonical id of each enode whose canonical children have changned, along with a canonical
    /// version of it
    pub fn raw_rebuild<T>(
        outer: &mut T,
        get_self: impl Fn(&mut T) -> &mut Self,
        mut perform_union: impl FnMut(&mut T, Id, Id),
        mut handle_pending: impl FnMut(&mut T, Id, &L),
    ) {
        loop {
            let this = get_self(outer);
            if let Some(class) = this.pending.pop() {
                let mut node = this.id_to_node(class).clone();
                node.update_children(|id| this.find_mut(id));
                handle_pending(outer, class, &node);
                if let Some(memo_class) = get_self(outer).residual.memo.insert(node, class) {
                    perform_union(outer, memo_class, class);
                }
            } else {
                break;
            }
        }
    }

    /// Returns whether `self` is congruently closed
    ///
    /// This will always be true after calling [`raw_rebuild`](RawEGraph::raw_rebuild)
    pub fn is_clean(&self) -> bool {
        self.pending.is_empty()
    }

    /// Returns a more debug-able representation of the egraph focusing on its classes.
    ///
    /// [`EGraph`]s implement [`Debug`], but it ain't pretty. It
    /// prints a lot of stuff you probably don't care about.
    /// This method returns a wrapper that implements [`Debug`] in a
    /// slightly nicer way, just dumping enodes in each eclass.
    ///
    /// [`Debug`]: std::fmt::Debug
    pub fn dump_classes(&self) -> impl Debug + '_
    where
        D: Debug,
    {
        EGraphDump(self)
    }
}

impl<L: Language> RawEGraph<L, ()> {
    /// Simplified version of [`raw_add`](RawEGraph::raw_add) for egraphs without eclass data
    pub fn add_uncanonical(&mut self, enode: L) -> Id {
        Self::raw_add(
            self,
            |x| x,
            enode,
            |_, id, _| Some(id),
            |_, _, _| {},
            |_, _, _| (),
        )
    }

    /// Simplified version of [`raw_union`](RawEGraph::raw_union) for egraphs without eclass data
    pub fn union(&mut self, id1: Id, id2: Id) -> bool {
        Self::raw_union(self, id1, id2).is_some()
    }

    /// Simplified version of [`raw_rebuild`](RawEGraph::raw_rebuild) for egraphs without eclass data
    pub fn rebuild(&mut self) {
        Self::raw_rebuild(
            self,
            |x| x,
            |this, id1, id2| {
                this.union(id1, id2);
            },
            |_, _, _| {},
        );
    }
}

struct EGraphUncanonicalDump<'a, L: Language>(&'a EGraphResidual<L>);

impl<'a, L: Language> Debug for EGraphUncanonicalDump<'a, L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (id, node) in self.0.uncanonical_nodes() {
            writeln!(f, "{}: {:?} (root={})", id, node, self.0.find(id))?
        }
        Ok(())
    }
}

struct EGraphDump<'a, L: Language, D>(&'a RawEGraph<L, D>);

impl<'a, L: Language, D: Debug> Debug for EGraphDump<'a, L, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ids: Vec<Id> = self.0.classes().map(|c| c.id).collect();
        ids.sort();
        for id in ids {
            writeln!(f, "{} {:?}", id, self.0.get_class(id).raw_data)?
        }
        Ok(())
    }
}
