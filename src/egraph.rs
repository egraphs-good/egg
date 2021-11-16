use crate::*;
use std::{
    borrow::BorrowMut,
    fmt::{self, Debug, Display},
};

#[cfg(feature = "serde-1")]
use ::serde::{Deserialize, Serialize};

use log::*;

/** A data structure to keep track of equalities between expressions.

Check out the [background tutorial](crate::tutorials::_01_background)
for more information on e-graphs in general.

# E-graphs in `egg`

In `egg`, the main types associated with e-graphs are
[`EGraph`], [`EClass`], [`Language`], and [`Id`].

[`EGraph`] and [`EClass`] are all generic over a
[`Language`], meaning that types actually floating around in the
egraph are all user-defined.
In particular, the e-nodes are elements of your [`Language`].
[`EGraph`]s and [`EClass`]es are additionally parameterized by some
[`Analysis`], abritrary data associated with each e-class.

Many methods of [`EGraph`] deal with [`Id`]s, which represent e-classes.
Because eclasses are frequently merged, many [`Id`]s will refer to the
same e-class.

You can use the `egraph[id]` syntax to get an [`EClass`] from an [`Id`], because
[`EGraph`] implements
[`Index`](struct.EGraph.html#impl-Index<Id>)
and
[`IndexMut`](struct.EGraph.html#impl-IndexMut<Id>).

Enabling the `serde-1` feature on this crate will allow you to
de/serialize [`EGraph`]s using [`serde`](https://serde.rs/).
You must call [`EGraph::rebuild`] after deserializing an e-graph!

[`add`]: EGraph::add()
[`union`]: EGraph::union()
[`rebuild`]: EGraph::rebuild()
[equivalence relation]: https://en.wikipedia.org/wiki/Equivalence_relation
[congruence relation]: https://en.wikipedia.org/wiki/Congruence_relation
[dot]: Dot
[extract]: Extractor
[sound]: https://itinerarium.github.io/phoneme-synthesis/?w=/'igraf/
**/
#[derive(Clone)]
#[cfg_attr(feature = "serde-1", derive(Serialize, Deserialize))]
pub struct EGraph<L: Language, N: Analysis<L>> {
    /// The `Analysis` given when creating this `EGraph`.
    pub analysis: N,
    /// The `Explain` used to explain equivalences in this `EGraph`.
    pub(crate) explain: Option<Explain<L>>,
    unionfind: UnionFind,
    #[cfg_attr(feature = "serde-1", serde(with = "vectorize"))]
    memo: HashMap<L, Id>,
    to_union: Vec<(Id, Id, Option<Symbol>, bool)>,
    pending: Vec<(L, Id)>,
    analysis_pending: IndexSet<(L, Id)>,
    #[cfg_attr(
        feature = "serde-1",
        serde(bound(
            serialize = "N::Data: Serialize",
            deserialize = "N::Data: for<'a> Deserialize<'a>",
        ))
    )]
    classes: HashMap<Id, EClass<L, N::Data>>,
    #[cfg_attr(feature = "serde-1", serde(skip))]
    #[cfg_attr(feature = "serde-1", serde(default = "default_classes_by_op"))]
    pub(crate) classes_by_op: HashMap<std::mem::Discriminant<L>, HashSet<Id>>,
    /// Whether or not reading operation are allowed on this e-graph.
    /// Mutating operations will set this to `false`, and
    /// [`EGraph::rebuild`] will set it to true.
    /// Reading operations require this to be `true`.
    /// Only manually set it if you know what you're doing.
    #[cfg_attr(feature = "serde-1", serde(skip))]
    pub clean: bool,
}

#[cfg(feature = "serde-1")]
fn default_classes_by_op<K>() -> HashMap<K, HashSet<Id>> {
    HashMap::default()
}

impl<L: Language, N: Analysis<L> + Default> Default for EGraph<L, N> {
    fn default() -> Self {
        Self::new(N::default())
    }
}

// manual debug impl to avoid L: Language bound on EGraph defn
impl<L: Language, N: Analysis<L>> Debug for EGraph<L, N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("EGraph")
            .field("memo", &self.memo)
            .field("classes", &self.classes)
            .finish()
    }
}

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    /// Creates a new, empty `EGraph` with the given `Analysis`
    pub fn new(analysis: N) -> Self {
        Self {
            analysis,
            to_union: Default::default(),
            classes: Default::default(),
            unionfind: Default::default(),
            clean: false,
            explain: None,
            pending: Default::default(),
            memo: Default::default(),
            analysis_pending: Default::default(),
            classes_by_op: Default::default(),
        }
    }

    /// Returns an iterator over the eclasses in the egraph.
    pub fn classes(&self) -> impl ExactSizeIterator<Item = &EClass<L, N::Data>> {
        self.classes.values()
    }

    /// Returns an mutating iterator over the eclasses in the egraph.
    pub fn classes_mut(&mut self) -> impl ExactSizeIterator<Item = &mut EClass<L, N::Data>> {
        self.classes.values_mut()
    }

    /// Returns `true` if the egraph is empty
    /// # Example
    /// ```
    /// use egg::{*, SymbolLang as S};
    /// let mut egraph = EGraph::<S, ()>::default();
    /// assert!(egraph.is_empty());
    /// egraph.add(S::leaf("foo"));
    /// assert!(!egraph.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.memo.is_empty()
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

    /// Iterates over the classes, returning the total number of nodes.
    pub fn total_number_of_nodes(&self) -> usize {
        self.classes().map(|c| c.len()).sum()
    }

    /// Returns the number of eclasses in the egraph.
    pub fn number_of_classes(&self) -> usize {
        self.classes.len()
    }

    /// Enable explanations for this `EGraph`.
    /// This allows the egraph to explain why two expressions are
    /// equivalent with the [`explain_equivalence`](EGraph::explain_equivalence) function.
    pub fn with_explanations_enabled(mut self) -> Self {
        if self.explain.is_some() {
            return self;
        }
        if self.total_size() > 0 {
            panic!("Need to set explanations enabled before adding any expressions to the egraph.");
        }
        self.explain = Some(Explain::new());
        self
    }

    /// Disable explanations for this `EGraph`.
    pub fn with_explanations_disabled(mut self) -> Self {
        self.explain = None;
        self
    }

    /// Check if explanations are enabled.
    pub fn are_explanations_enabled(&self) -> bool {
        self.explain.is_some()
    }

    /// When explanations are enabled, this function
    /// produces an [`Explanation`] describing why two expressions are equivalent.
    ///
    /// The [`Explanation`] can be used in it's default tree form or in a less compact
    /// flattened form. Each of these also has a s-expression string representation,
    /// given by [`get_flat_string`](Explanation::get_flat_string) and [`get_string`](Explanation::get_string).
    pub fn explain_equivalence(&mut self, left: &RecExpr<L>, right: &RecExpr<L>) -> Explanation<L> {
        if let Some(explain) = &mut self.explain {
            explain.explain_equivalence(left, right, &self.memo, &mut self.unionfind)
        } else {
            panic!("Use runner.with_explanations_enabled() or egraph.with_explanations_enabled() before running to get explanations.")
        }
    }

    /// When explanations are enabled, this function
    /// produces an [`Explanation`] describing how the given expression came
    /// to be in the egraph.
    ///
    /// The [`Explanation`] begins with some expression that was added directly
    /// into the egraph and ends with the given `expr`.
    /// Note that this function can be called again to explain any intermediate terms
    /// used in the output [`Explanation`].
    pub fn explain_existance(&mut self, expr: &RecExpr<L>) -> Explanation<L> {
        if let Some(explain) = &mut self.explain {
            explain.explain_existance(expr, &self.memo, &mut self.unionfind)
        } else {
            panic!("Use runner.with_explanations_enabled() or egraph.with_explanations_enabled() before running to get explanations.")
        }
    }

    /// Return an [`Explanation`] for why a pattern appears in the egraph.
    pub fn explain_existance_pattern(
        &mut self,
        pattern: &PatternAst<L>,
        subst: &Subst,
    ) -> Explanation<L> {
        if let Some(explain) = &mut self.explain {
            explain.explain_existance_pattern(pattern, subst, &self.memo, &mut self.unionfind)
        } else {
            panic!("Use runner.with_explanations_enabled() or egraph.with_explanations_enabled() before running to get explanations.")
        }
    }

    /// Get an explanation for why an expression matches a pattern.
    pub fn explain_matches(
        &mut self,
        left: &RecExpr<L>,
        right: &PatternAst<L>,
        subst: &Subst,
    ) -> Explanation<L> {
        if let Some(explain) = &mut self.explain {
            explain.explain_matches(left, right, subst, &self.memo, &mut self.unionfind)
        } else {
            panic!("Use runner.with_explanations_enabled() or egraph.with_explanations_enabled() before running to get explanations.");
        }
    }

    /// Canonicalizes an eclass id.
    ///
    /// This corresponds to the `find` operation on the egraph's
    /// underlying unionfind data structure.
    ///
    /// # Example
    /// ```
    /// use egg::{*, SymbolLang as S};
    /// let mut egraph = EGraph::<S, ()>::default();
    /// let x = egraph.add(S::leaf("x"));
    /// let y = egraph.add(S::leaf("y"));
    /// assert_ne!(egraph.find(x), egraph.find(y));
    ///
    /// egraph.union(x, y);
    /// egraph.rebuild();
    /// assert_eq!(egraph.find(x), egraph.find(y));
    /// ```
    pub fn find(&self, id: Id) -> Id {
        self.unionfind.find(id)
    }

    /// This is private, but internals should use this whenever
    /// possible because it does path compression.
    fn find_mut(&mut self, id: Id) -> Id {
        self.unionfind.find_mut(id)
    }

    /// Creates a [`Dot`] to visualize this egraph. See [`Dot`].
    ///
    pub fn dot(&self) -> Dot<L, N> {
        Dot {
            egraph: self,
            config: vec![],
            use_anchors: true,
        }
    }
}

/// Given an `Id` using the `egraph[id]` syntax, retrieve the e-class.
impl<L: Language, N: Analysis<L>> std::ops::Index<Id> for EGraph<L, N> {
    type Output = EClass<L, N::Data>;
    fn index(&self, id: Id) -> &Self::Output {
        let id = self.find(id);
        self.classes
            .get(&id)
            .unwrap_or_else(|| panic!("Invalid id {}", id))
    }
}

/// Given an `Id` using the `&mut egraph[id]` syntax, retrieve a mutable
/// reference to the e-class.
impl<L: Language, N: Analysis<L>> std::ops::IndexMut<Id> for EGraph<L, N> {
    fn index_mut(&mut self, id: Id) -> &mut Self::Output {
        let id = self.find_mut(id);
        self.classes
            .get_mut(&id)
            .unwrap_or_else(|| panic!("Invalid id {}", id))
    }
}

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    /// Adds a [`RecExpr`] to the [`EGraph`].
    ///
    /// # Example
    /// ```
    /// use egg::{*, SymbolLang as S};
    /// let mut egraph = EGraph::<S, ()>::default();
    /// let x = egraph.add(S::leaf("x"));
    /// let y = egraph.add(S::leaf("y"));
    /// let plus = egraph.add(S::new("+", vec![x, y]));
    /// let plus_recexpr = "(+ x y)".parse().unwrap();
    /// assert_eq!(plus, egraph.add_expr(&plus_recexpr));
    /// ```
    ///
    /// [`add_expr`]: EGraph::add_expr()
    pub fn add_expr(&mut self, expr: &RecExpr<L>) -> Id {
        let nodes = expr.as_ref();
        let mut new_ids = Vec::with_capacity(nodes.len());
        let mut new_node_q = Vec::with_capacity(nodes.len());
        for node in nodes {
            let new_node = node.clone().map_children(|i| new_ids[usize::from(i)]);
            let size_before = self.unionfind.size();
            let next_id = self.add(new_node);
            if self.unionfind.size() > size_before {
                new_node_q.push(true);
            } else {
                new_node_q.push(false);
            }
            if let Some(explain) = &mut self.explain {
                node.for_each(|child| {
                    // Set the existance reason for new nodes to their parent node.
                    if new_node_q[usize::from(child)] {
                        explain.set_existance_reason(new_ids[usize::from(child)], next_id);
                    }
                });
            }
            new_ids.push(next_id);
        }
        *new_ids.last().unwrap()
    }

    /// Adds a [`Pattern`] and a substitution to the [`EGraph`].
    pub fn add_instantiation(&mut self, pat: &PatternAst<L>, subst: &Subst) -> Id {
        let nodes = pat.as_ref().as_ref();
        let mut new_ids = Vec::with_capacity(nodes.len());
        let mut new_node_q = Vec::with_capacity(nodes.len());
        for node in nodes {
            match node {
                ENodeOrVar::Var(var) => {
                    let id = subst[*var];
                    new_ids.push(id);
                    new_node_q.push(false);
                }
                ENodeOrVar::ENode(node) => {
                    let new_node = node.clone().map_children(|i| new_ids[usize::from(i)]);
                    let size_before = self.unionfind.size();
                    let next_id = self.add(new_node);
                    if self.unionfind.size() > size_before {
                        new_node_q.push(true);
                    } else {
                        new_node_q.push(false);
                    }
                    if let Some(explain) = &mut self.explain {
                        node.for_each(|child| {
                            if new_node_q[usize::from(child)] {
                                explain.set_existance_reason(new_ids[usize::from(child)], next_id);
                            }
                        });
                    }
                    new_ids.push(next_id);
                }
            }
        }
        *new_ids.last().unwrap()
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
    pub fn lookup<B>(&self, mut enode: B) -> Option<Id>
    where
        B: BorrowMut<L>,
    {
        let enode = enode.borrow_mut();
        enode.update_children(|id| self.find(id));
        let id = self.memo.get(enode);
        id.map(|&id| self.find(id))
    }

    /// Lookup the eclass of the given [`RecExpr`].
    pub fn lookup_expr(&self, expr: &RecExpr<L>) -> Option<Id> {
        let nodes = expr.as_ref();
        let mut new_ids = Vec::with_capacity(nodes.len());
        for node in nodes {
            let node = node.clone().map_children(|i| new_ids[usize::from(i)]);
            let id = self.lookup(node)?;
            new_ids.push(id)
        }
        Some(*new_ids.last().unwrap())
    }

    /// Adds an enode to the [`EGraph`].
    ///
    /// When adding an enode, to the egraph, [`add`] it performs
    /// _hashconsing_ (sometimes called interning in other contexts).
    ///
    /// Hashconsing ensures that only one copy of that enode is in the egraph.
    /// If a copy is in the egraph, then [`add`] simply returns the id of the
    /// eclass in which the enode was found.
    ///
    /// Like [`union`](EGraph::union), this modifies the e-graph,
    /// so you must call [`rebuild`](EGraph::rebuild) any query operations.
    ///
    /// [`add`]: EGraph::add()
    pub fn add(&mut self, mut enode: L) -> Id {
        self.lookup(&mut enode).unwrap_or_else(|| {
            let id = self.unionfind.make_set();
            if let Some(explain) = &mut self.explain {
                explain.add(enode.clone(), id, id);
            }
            log::trace!("  ...adding to {}", id);
            let class = EClass {
                id,
                nodes: vec![enode.clone()],
                data: N::make(self, &enode),
                parents: Default::default(),
            };

            // add this enode to the parent lists of its children
            enode.for_each(|child| {
                let tup = (enode.clone(), id);
                self[child].parents.push(tup);
            });

            // TODO is this needed?
            self.pending.push((enode.clone(), id));

            self.classes.insert(id, class);
            assert!(self.memo.insert(enode, id).is_none());

            N::modify(self, id);

            self.clean = false;
            id
        })
    }

    /// Checks whether two [`RecExpr`]s are equivalent.
    /// Returns a list of id where both expression are represented.
    /// In most cases, there will none or exactly one id.
    ///
    pub fn equivs(&self, expr1: &RecExpr<L>, expr2: &RecExpr<L>) -> Vec<Id> {
        let pat1 = Pattern::from(expr1.as_ref());
        let pat2 = Pattern::from(expr2.as_ref());
        let matches1 = pat1.search(self);
        trace!("Matches1: {:?}", matches1);

        let matches2 = pat2.search(self);
        trace!("Matches2: {:?}", matches2);

        let mut equiv_eclasses = Vec::new();

        for m1 in &matches1 {
            for m2 in &matches2 {
                if self.find(m1.eclass) == self.find(m2.eclass) {
                    equiv_eclasses.push(m1.eclass)
                }
            }
        }

        equiv_eclasses
    }

    /// Given two patterns and a substitution, add the patterns
    /// and mark them for unioning.
    /// The unions are performed when [`rebuild`](EGraph::rebuild) is called.
    /// When explanations are enabled [`with_explanations_enabled`](Runner::with_explanations_enabled), use
    /// this function instead of [`union`](EGraph::union).
    ///
    /// The returned `bool` indicates whether a union is necessary,
    /// and returned Id represents the eclass of the left pattern.
    pub fn union_instantiations(
        &mut self,
        from_pat: &PatternAst<L>,
        to_pat: &PatternAst<L>,
        subst: &Subst,
        rule_name: impl Into<Symbol>,
    ) -> (Id, bool) {
        let id1 = self.add_instantiation(from_pat, subst);
        let size_before = self.unionfind.size();
        let id2 = self.add_instantiation(to_pat, subst);
        let rhs_new = self.unionfind.size() > size_before;
        (
            id1,
            self.union_with_justification(id1, id2, from_pat, to_pat, subst, rule_name, rhs_new),
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn union_with_justification(
        &mut self,
        id1: Id,
        id2: Id,
        from_pat: &PatternAst<L>,
        to_pat: &PatternAst<L>,
        subst: &Subst,
        rule_name: impl Into<Symbol>,
        rhs_new: bool,
    ) -> bool {
        self.clean = false;
        if let Some(explain) = &mut self.explain {
            if self.unionfind.find_mut(id1) == self.unionfind.find_mut(id2) {
                false
            } else {
                let left_added =
                    explain.add_match(from_pat, subst, &self.memo, &mut self.unionfind);
                let size_before_right = self.unionfind.size();
                let right_added = explain.add_match(to_pat, subst, &self.memo, &mut self.unionfind);
                let any_new_rhs = rhs_new || self.unionfind.size() > size_before_right;
                self.to_union
                    .push((left_added, right_added, Some(rule_name.into()), any_new_rhs));
                true
            }
        } else {
            self.union(id1, id2)
        }
    }

    /// Marks two eclasses to be unioned given their ids.
    ///
    /// At the end of each iteration, these classes are unioned during
    /// [`rebuild`](EGraph::rebuild).
    ///
    /// The given ids need not be canonical.
    /// The returned `bool` indicates whether a union is necessary,
    /// so it's `false` if they were already equivalent.
    /// Both results are canonical.
    ///
    /// When explanations are enabled, this function is not available.
    /// Instead, use [`union_instantiations`](EGraph::union_instantiations).
    /// See [`explain_equivalence`](Runner::explain_equivalence) for a more detailed
    /// explanation of the feature.
    ///
    /// You must call [`rebuild`](EGraph::rebuild) to observe any effect.
    ///
    pub fn union(&mut self, id1: Id, id2: Id) -> bool {
        self.clean = false;
        if self.explain.is_some() {
            panic!("Use union_instantiations when explanation mode is enabled.");
        }
        if self.find_mut(id1) == self.find_mut(id2) {
            false
        } else {
            self.to_union.push((id1, id2, None, false));
            true
        }
    }

    fn perform_union(
        &mut self,
        enode_id1: Id,
        enode_id2: Id,
        rule: Option<Justification>,
        any_new_rhs: bool,
    ) -> bool {
        let mut id1 = self.find_mut(enode_id1);
        let mut id2 = self.find_mut(enode_id2);
        if id1 == id2 {
            return false;
        }
        // make sure class2 has fewer parents
        let class1_parents = self.classes[&id1].parents.len();
        let class2_parents = self.classes[&id2].parents.len();
        if class1_parents < class2_parents {
            std::mem::swap(&mut id1, &mut id2);
        }

        N::pre_union(self, id1, id2);

        if let Some(explain) = &mut self.explain {
            explain.union(enode_id1, enode_id2, rule.unwrap(), any_new_rhs);
        } else {
            assert!(rule.is_none());
        }
        // make id1 the new root
        self.unionfind.union(id1, id2);

        assert_ne!(id1, id2);
        let class2 = self.classes.remove(&id2).unwrap();
        let class1 = self.classes.get_mut(&id1).unwrap();
        assert_eq!(id1, class1.id);

        self.pending.extend(class2.parents.iter().cloned());
        let did_merge = self.analysis.merge(&mut class1.data, class2.data);
        if did_merge.0 {
            self.analysis_pending.extend(class1.parents.iter().cloned());
        }
        if did_merge.1 {
            self.analysis_pending.extend(class2.parents.iter().cloned());
        }

        concat_vecs(&mut class1.nodes, class2.nodes);
        concat_vecs(&mut class1.parents, class2.parents);

        N::modify(self, id1);
        true
    }

    /// Returns a more debug-able representation of the egraph.
    ///
    /// [`EGraph`]s implement [`Debug`], but it ain't pretty. It
    /// prints a lot of stuff you probably don't care about.
    /// This method returns a wrapper that implements [`Debug`] in a
    /// slightly nicer way, just dumping enodes in each eclass.
    ///
    /// [`Debug`]: std::fmt::Debug
    pub fn dump(&self) -> impl Debug + '_ {
        EGraphDump(self)
    }
}

impl<L: Language + Display, N: Analysis<L>> EGraph<L, N> {
    /// Panic if the given eclass doesn't contain the given patterns
    ///
    /// Useful for testing.
    pub fn check_goals(&self, id: Id, goals: &[Pattern<L>]) {
        let (cost, best) = Extractor::new(self, AstSize).find_best(id);
        println!("End ({}): {}", cost, best.pretty(80));

        for (i, goal) in goals.iter().enumerate() {
            println!("Trying to prove goal {}: {}", i, goal.pretty(40));
            let matches = goal.search_eclass(&self, id);
            if matches.is_none() {
                let best = Extractor::new(&self, AstSize).find_best(id).1;
                panic!(
                    "Could not prove goal {}:\n\
                     {}\n\
                     Best thing found:\n\
                     {}",
                    i,
                    goal.pretty(40),
                    best.pretty(40),
                );
            }
        }
    }
}

// All the rebuilding stuff
impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    #[inline(never)]
    fn rebuild_classes(&mut self) -> usize {
        let mut classes_by_op = std::mem::take(&mut self.classes_by_op);
        classes_by_op.values_mut().for_each(|ids| ids.clear());

        let mut trimmed = 0;
        let uf = &mut self.unionfind;

        for class in self.classes.values_mut() {
            let old_len = class.len();
            class
                .nodes
                .iter_mut()
                .for_each(|n| n.update_children(|id| uf.find_mut(id)));
            class.nodes.sort_unstable();
            class.nodes.dedup();

            trimmed += old_len - class.nodes.len();

            let mut add = |n: &L| {
                #[allow(clippy::mem_discriminant_non_enum)]
                classes_by_op
                    .entry(std::mem::discriminant(&n))
                    .or_default()
                    .insert(class.id)
            };

            // we can go through the ops in order to dedup them, becaue we
            // just sorted them
            let mut nodes = class.nodes.iter();
            if let Some(mut prev) = nodes.next() {
                add(prev);
                for n in nodes {
                    if !prev.matches(n) {
                        add(n);
                        prev = n;
                    }
                }
            }
        }

        #[cfg(debug_assertions)]
        for ids in classes_by_op.values_mut() {
            let unique: HashSet<Id> = ids.iter().copied().collect();
            assert_eq!(ids.len(), unique.len());
        }

        self.classes_by_op = classes_by_op;
        trimmed
    }

    #[inline(never)]
    fn check_memo(&self) -> bool {
        let mut test_memo = HashMap::default();

        for (&id, class) in self.classes.iter() {
            assert_eq!(class.id, id);
            for node in &class.nodes {
                if let Some(old) = test_memo.insert(node, id) {
                    assert_eq!(
                        self.find(old),
                        self.find(id),
                        "Found unexpected equivalence for {:?}\n{:?}\nvs\n{:?}",
                        node,
                        self[self.find(id)].nodes,
                        self[self.find(old)].nodes,
                    );
                }
            }
        }

        for (n, e) in test_memo {
            assert_eq!(e, self.find(e));
            assert_eq!(
                Some(e),
                self.memo.get(n).map(|id| self.find(*id)),
                "Entry for {:?} at {} in test_memo was incorrect",
                n,
                e
            );
        }

        true
    }

    fn perform_to_union(&mut self) {
        while !self.to_union.is_empty() {
            let mut current = vec![];
            std::mem::swap(&mut self.to_union, &mut current);
            for (id1, id2, rule, any_new_rhs) in current.into_iter() {
                self.perform_union(id1, id2, rule.map(Justification::Rule), any_new_rhs);
            }
        }
    }

    #[inline(never)]
    fn process_unions(&mut self) -> usize {
        let mut n_unions = 0;

        while !self.pending.is_empty()
            || !self.to_union.is_empty()
            || !self.analysis_pending.is_empty()
        {
            while !self.pending.is_empty() || !self.to_union.is_empty() {
                self.perform_to_union();
                assert!(self.to_union.is_empty());

                while let Some((mut node, class)) = self.pending.pop() {
                    node.update_children(|id| self.find_mut(id));
                    if let Some(memo_class) = self.memo.insert(node, class) {
                        let mut reason = None;
                        if self.explain.is_some() {
                            reason = Some(Justification::Congruence);
                        }
                        let did_something = self.perform_union(memo_class, class, reason, false);
                        n_unions += did_something as usize;
                    }
                }
            }
            assert!(self.pending.is_empty());
            assert!(self.to_union.is_empty());

            while let Some((node, class_id)) = self.analysis_pending.pop() {
                let class_id = self.find_mut(class_id);
                let node_data = N::make(self, &node);
                let class = self.classes.get_mut(&class_id).unwrap();

                let did_merge = self.analysis.merge(&mut class.data, node_data);
                if did_merge.0 {
                    self.analysis_pending.extend(class.parents.iter().cloned());
                    N::modify(self, class_id);
                }
            }
        }

        assert!(self.pending.is_empty());
        assert!(self.analysis_pending.is_empty());
        assert!(self.to_union.is_empty());

        n_unions
    }

    /// Restores the egraph invariants of congruence and enode uniqueness.
    ///
    /// As mentioned
    /// [in the tutorial](tutorials/_01_background/index.html#invariants-and-rebuilding),
    /// `egg` takes a lazy approach to maintaining the egraph invariants.
    /// The `rebuild` method allows the user to manually restore those
    /// invariants at a time of their choosing. It's a reasonably
    /// fast, linear-ish traversal through the egraph.
    ///
    /// After modifying an e-graph with [`add`](EGraph::add) or
    /// [`union`](EGraph::union), you must call `rebuild` to restore
    /// invariants before any query operations, otherwise the results
    /// may be stale or incorrect.
    ///
    /// This will set [`EGraph::clean`] to `true`.
    ///
    /// # Example
    /// ```
    /// use egg::{*, SymbolLang as S};
    /// let mut egraph = EGraph::<S, ()>::default();
    /// let x = egraph.add(S::leaf("x"));
    /// let y = egraph.add(S::leaf("y"));
    /// let ax = egraph.add_expr(&"(+ a x)".parse().unwrap());
    /// let ay = egraph.add_expr(&"(+ a y)".parse().unwrap());

    /// // The effects of this union aren't yet visible;
    /// // The union has not taken effect.
    /// egraph.union(x, y);
    /// // Classes: [x] [y] [ax] [ay] [a]
    /// assert_eq!(egraph.number_of_classes(), 5);
    /// assert_ne!(egraph.find(ax), egraph.find(ay));
    ///
    /// // Rebuilding applies the union and restores the invariants, finding
    /// // that ax and ay are equivalent.
    /// egraph.rebuild();
    /// // Classes: [x y] [ax ay] [a]
    /// assert_eq!(egraph.number_of_classes(), 3);
    /// assert_eq!(egraph.find(ax), egraph.find(ay));
    /// ```
    pub fn rebuild(&mut self) -> usize {
        let old_hc_size = self.memo.len();
        let old_n_eclasses = self.number_of_classes();

        let start = Instant::now();

        let n_unions = self.process_unions();
        let trimmed_nodes = self.rebuild_classes();

        let elapsed = start.elapsed();
        info!(
            concat!(
                "REBUILT! in {}.{:03}s\n",
                "  Old: hc size {}, eclasses: {}\n",
                "  New: hc size {}, eclasses: {}\n",
                "  unions: {}, trimmed nodes: {}"
            ),
            elapsed.as_secs(),
            elapsed.subsec_millis(),
            old_hc_size,
            old_n_eclasses,
            self.memo.len(),
            self.number_of_classes(),
            n_unions,
            trimmed_nodes,
        );

        debug_assert!(self.check_memo());
        self.clean = true;
        n_unions
    }

    pub(crate) fn check_each_explain(&self, rules: &[&Rewrite<L, N>]) -> bool {
        if let Some(explain) = &self.explain {
            explain.check_each_explain(rules)
        } else {
            panic!("Can't check explain when explanations are off");
        }
    }
}

struct EGraphDump<'a, L: Language, N: Analysis<L>>(&'a EGraph<L, N>);

impl<'a, L: Language, N: Analysis<L>> Debug for EGraphDump<'a, L, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ids: Vec<Id> = self.0.classes().map(|c| c.id).collect();
        ids.sort();
        for id in ids {
            let mut nodes = self.0[id].nodes.clone();
            nodes.sort();
            writeln!(f, "{} ({:?}): {:?}", id, self.0[id].data, nodes)?
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn simple_add() {
        use SymbolLang as S;

        crate::init_logger();
        let mut egraph = EGraph::<S, ()>::default();

        let x = egraph.add(S::leaf("x"));
        let x2 = egraph.add(S::leaf("x"));
        let _plus = egraph.add(S::new("+", vec![x, x2]));

        egraph.union_instantiations(
            &"x".parse().unwrap(),
            &"y".parse().unwrap(),
            &Default::default(),
            "union x and y".to_string(),
        );
        egraph.rebuild();

        egraph.dot().to_dot("target/foo.dot").unwrap();
    }

    #[cfg(all(feature = "serde-1", feature = "serde_json"))]
    #[test]
    fn test_serde() {
        fn ser(_: &impl Serialize) {}
        fn de<'a>(_: &impl Deserialize<'a>) {}

        let mut egraph = EGraph::<SymbolLang, ()>::default();
        egraph.add_expr(&"(foo bar baz)".parse().unwrap());
        ser(&egraph);
        de(&egraph);

        let json_rep = serde_json::to_string_pretty(&egraph).unwrap();
        println!("{}", json_rep);
    }
}
