use std::collections::HashMap;
use std::{
    borrow::BorrowMut,
    fmt::{self, Debug},
};

use indexmap::IndexMap;
use log::*;

use crate::{
    Analysis, AstSize, Dot, EClass, Extractor, Id, Language, Pattern, RecExpr, Searcher, UnionFind,
};

/** A data structure to keep track of equalities between expressions.

# What's an egraph?

An egraph ([/'igraf/][sound]) is a data structure to maintain equivalence

classes of expressions.
An egraph conceptually is a set of eclasses, each of which
contains equivalent enodes.
An enode is conceptually and operator with children, but instead of
children being other operators or values, the children are eclasses.

In `egg`, these are respresented by the [`EGraph`], [`EClass`], and
[`Language`] (enodes) types.


Here's an egraph created and rendered by [this example](struct.Dot.html).
As described in the documentation for [egraph visualization][dot] and
in the academic literature, we picture eclasses as dotted boxes
surrounding the equivalent enodes:

<img src="https://mwillsey.com/assets/simple-egraph.svg"/>

We say a term _t_ is _represented_ in an eclass _e_ if you can pick a
single enode from each eclass such that _t_ is in _e_.
A term is represented in the egraph if it's represented in any eclass.
In the image above, the terms `2 * a`, `a * 2`, and `a << 1` are all
represented in the same eclass and thus are equivalent.
The terms `1`, `(a * 2) / 2`, and `(a << 1) / 2` are represented in
the egraph, but not in the same eclass as the prior three terms, so
these three are not equivalent to those three.

Egraphs are useful when you have a bunch of very similar expressions,
some of which are equivalent, and you'd like a compactly store them.
This compactness allows rewrite systems based on egraphs to
efficiently "remember" the expression before and after rewriting, so
you can essentially apply all rewrites at once.
See [`Rewrite`] and [`Runner`] for more details about rewrites and
running rewrite systems, respectively.

# Invariants and Rebuilding

An egraph has two core operations that modify the egraph:
[`add`] which adds enodes to the egraph, and
[`union`] which merges two eclasses.
These operations maintains two key (related) invariants:

1. **Uniqueness of enodes**

   There do not exist two distinct enodes with equal operators and equal
   children in the eclass, either in the same eclass or different eclasses.
   This is maintained in part by the hashconsing performed by [`add`],
   and by deduplication performed by [`union`] and [`rebuild`].

2. **Congruence closure**

   An egraph maintains not just an [equivalence relation] over
   expressions, but a [congruence relation].
   So as the user calls [`union`], many eclasses other than the given
   two may need to merge to maintain congruence.

   For example, suppose terms `a + x` and `a + y` are represented in
   eclasses 1 and 2, respectively.
   At some later point, `x` and `y` become
   equivalent (perhaps the user called [`union`] on their containing
   eclasses).
   Eclasses 1 and 2 must merge, because now the two `+`
   operators have equivalent arguments, making them equivalent.

`egg` takes a delayed approach to maintaining these invariants.
Specifically, the effects of calling [`union`] (or applying a rewrite,
which calls [`union`]) may not be reflected immediately.
To restore the egraph invariants and make these effects visible, the
user *must* call the [`rebuild`] method.

`egg`s choice here allows for a higher performance implementation.
Maintaining the congruence relation complicates the core egraph data
structure and requires an expensive traversal through the egraph on
every [`union`].
`egg` chooses to relax these invariants for better performance, only
restoring the invariants on a call to [`rebuild`].
See the [`rebuild`] documentation for more information.
Note also that [`Runner`]s take care of this for you, calling
[`rebuild`] between rewrite iterations.

# egraphs in `egg`

In `egg`, the main types associated with egraphs are
[`EGraph`], [`EClass`], [`Language`], and [`Id`].

[`EGraph`] and [`EClass`] are all generic over a
[`Language`], meaning that types actually floating around in the
egraph are all user-defined.
In particular, the enodes are elements of your [`Language`].
[`EGraph`]s and [`EClass`]es are additionally parameterized by some
[`Analysis`], abritrary data associated with each eclass.

Many methods of [`EGraph`] deal with [`Id`]s, which represent eclasses.
Because eclasses are frequently merged, many [`Id`]s will refer to the
same eclass.

[`EGraph`]: struct.EGraph.html
[`EClass`]: struct.EClass.html
[`Rewrite`]: struct.Rewrite.html
[`Runner`]: struct.Runner.html
[`Language`]: trait.Language.html
[`Analysis`]: trait.Analysis.html
[`Id`]: struct.Id.html
[`add`]: struct.EGraph.html#method.add
[`union`]: struct.EGraph.html#method.union
[`rebuild`]: struct.EGraph.html#method.rebuild
[equivalence relation]: https://en.wikipedia.org/wiki/Equivalence_relation
[congruence relation]: https://en.wikipedia.org/wiki/Congruence_relation
[dot]: struct.Dot.html
[extract]: struct.Extractor.html
[sound]: https://itinerarium.github.io/phoneme-synthesis/?w=/'igraf/
**/
#[derive(Clone)]
pub struct EGraph<L: Language, N: Analysis<L>> {
    /// The `Analysis` given when creating this `EGraph`.
    pub analysis: N,
    memo: HashMap<L, Id>,
    unionfind: UnionFind,
    classes: SparseVec<EClass<L, N::Data>>,
    dirty_unions: Vec<Id>,
    repairs_since_rebuild: usize,
    pub(crate) classes_by_op: IndexMap<std::mem::Discriminant<L>, indexmap::IndexSet<Id>>,
}

type SparseVec<T> = Vec<Option<Box<T>>>;

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
            memo: Default::default(),
            classes: Default::default(),
            unionfind: Default::default(),
            dirty_unions: Default::default(),
            classes_by_op: IndexMap::default(),
            repairs_since_rebuild: 0,
        }
    }

    /// Returns an iterator over the eclasses in the egraph.
    pub fn classes(&self) -> impl Iterator<Item = &EClass<L, N::Data>> {
        self.classes
            .iter()
            .filter_map(Option::as_ref)
            .map(AsRef::as_ref)
    }

    /// Returns an mutating iterator over the eclasses in the egraph.
    pub fn classes_mut(&mut self) -> impl Iterator<Item = &mut EClass<L, N::Data>> {
        self.classes
            .iter_mut()
            .filter_map(Option::as_mut)
            .map(AsMut::as_mut)
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
        self.classes().count()
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
    /// assert_eq!(egraph.find(x), egraph.find(y));
    /// ```
    pub fn find(&self, id: Id) -> Id {
        self.unionfind.find(id)
    }

    /// Creates a [`Dot`] to visualize this egraph. See [`Dot`].
    ///
    /// [`Dot`]: struct.Dot.html
    pub fn dot(&self) -> Dot<L, N> {
        Dot { egraph: self }
    }
}

impl<L: Language, N: Analysis<L>> std::ops::Index<Id> for EGraph<L, N> {
    type Output = EClass<L, N::Data>;
    fn index(&self, id: Id) -> &Self::Output {
        let id = self.find(id);
        self.classes[usize::from(id)]
            .as_ref()
            .unwrap_or_else(|| panic!("Invalid id {}", id))
    }
}

impl<L: Language, N: Analysis<L>> std::ops::IndexMut<Id> for EGraph<L, N> {
    fn index_mut(&mut self, id: Id) -> &mut Self::Output {
        let id = self.find(id);
        self.classes[usize::from(id)]
            .as_mut()
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
    /// [`EGraph`]: struct.EGraph.html
    /// [`RecExpr`]: struct.RecExpr.html
    /// [`add_expr`]: struct.EGraph.html#method.add_expr
    pub fn add_expr(&mut self, expr: &RecExpr<L>) -> Id {
        self.add_expr_rec(expr.as_ref())
    }

    fn add_expr_rec(&mut self, expr: &[L]) -> Id {
        log::trace!("Adding expr {:?}", expr);
        let e = expr.last().unwrap().clone().map_children(|i| {
            let child = &expr[..usize::from(i) + 1];
            self.add_expr_rec(child)
        });
        let id = self.add(e);
        log::trace!("Added!! expr {:?}", expr);
        id
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
    /// let c = egraph.add(SymbolLang::leaf("c"));
    ///
    /// // lookup will find this node if its in the egraph
    /// let mut node_f_ac = SymbolLang::new("f", vec![a, c]);
    /// assert_eq!(egraph.lookup(node_f_ac.clone()), None);
    /// let id = egraph.add(node_f_ac.clone());
    /// assert_eq!(egraph.lookup(node_f_ac.clone()), Some(id));
    ///
    /// // if the query node isn't canonical, and its passed in by &mut instead of owned,
    /// // its children will be canonicalized
    /// egraph.union(b, c);
    /// egraph.rebuild();
    /// assert_eq!(egraph.lookup(&mut node_f_ac), Some(id));
    /// assert_eq!(node_f_ac, SymbolLang::new("f", vec![a, b]));
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

    /// Adds an enode to the [`EGraph`].
    ///
    /// When adding an enode, to the egraph, [`add`] it performs
    /// _hashconsing_ (sometimes called interning in other contexts).
    ///
    /// Hashconsing ensures that only one copy of that enode is in the egraph.
    /// If a copy is in the egraph, then [`add`] simply returns the id of the
    /// eclass in which the enode was found.
    /// Otherwise
    ///
    /// [`EGraph`]: struct.EGraph.html
    /// [`EClass`]: struct.EClass.html
    /// [`add`]: struct.EGraph.html#method.add
    pub fn add(&mut self, mut enode: L) -> Id {
        self.lookup(&mut enode).unwrap_or_else(|| {
            let id = self.unionfind.make_set();
            log::trace!("  ...adding to {}", id);
            let class = Box::new(EClass {
                id,
                nodes: vec![enode.clone()],
                data: N::make(self, &enode),
                parents: Default::default(),
            });

            // add this enode to the parent lists of its children
            enode.for_each(|child| {
                let tup = (enode.clone(), id);
                self[child].parents.push(tup);
            });

            assert_eq!(self.classes.len(), usize::from(id));
            self.classes.push(Some(class));
            assert!(self.memo.insert(enode, id).is_none());

            N::modify(self, id);
            id
        })
    }

    /// Checks whether two [`RecExpr`]s are equivalent.
    /// Returns a list of id where both expression are represented.
    /// In most cases, there will none or exactly one id.
    ///
    /// [`RecExpr`]: struct.RecExpr.html
    pub fn equivs(&self, expr1: &RecExpr<L>, expr2: &RecExpr<L>) -> Vec<Id> {
        let matches1 = Pattern::from(expr1.as_ref()).search(self);
        trace!("Matches1: {:?}", matches1);

        let matches2 = Pattern::from(expr2.as_ref()).search(self);
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
                    "Could not prove goal {}:\n{}\nBest thing found:\n{}",
                    i,
                    goal.pretty(40),
                    best.pretty(40),
                );
            }
        }
    }

    #[inline]
    fn union_impl(&mut self, id1: Id, id2: Id) -> (Id, bool) {
        fn concat<T>(to: &mut Vec<T>, mut from: Vec<T>) {
            if to.len() < from.len() {
                std::mem::swap(to, &mut from)
            }
            to.extend(from);
        }

        let (to, from) = self.unionfind.union(id1, id2);
        debug_assert_eq!(to, self.find(id1));
        debug_assert_eq!(to, self.find(id2));
        if to != from {
            self.dirty_unions.push(to);

            // update the classes data structure
            let from_class = self.classes[usize::from(from)].take().unwrap();
            let to_class = self.classes[usize::from(to)].as_mut().unwrap();

            self.analysis.merge(&mut to_class.data, from_class.data);
            concat(&mut to_class.nodes, from_class.nodes);
            concat(&mut to_class.parents, from_class.parents);

            N::modify(self, to);
        }
        (to, to != from)
    }

    /// Unions two eclasses given their ids.
    ///
    /// The given ids need not be canonical.
    /// The returned `bool` indicates whether a union was done,
    /// so it's `false` if they were already equivalent.
    /// Both results are canonical.
    pub fn union(&mut self, id1: Id, id2: Id) -> (Id, bool) {
        let union = self.union_impl(id1, id2);
        if union.1 && cfg!(feature = "upward-merging") {
            self.process_unions();
        }
        union
    }

    /// Returns a more debug-able representation of the egraph.
    ///
    /// [`EGraph`]s implement [`Debug`], but it ain't pretty. It
    /// prints a lot of stuff you probably don't care about.
    /// This method returns a wrapper that implements [`Debug`] in a
    /// slightly nicer way, just dumping enodes in each eclass.
    ///
    /// [`Debug`]: https://doc.rust-lang.org/stable/std/fmt/trait.Debug.html
    /// [`EGraph`]: struct.EGraph.html
    pub fn dump<'a>(&'a self) -> impl Debug + 'a {
        EGraphDump(self)
    }
}

// All the rebuilding stuff
impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    #[inline(never)]
    fn rebuild_classes(&mut self) -> usize {
        let mut classes_by_op = std::mem::take(&mut self.classes_by_op);
        classes_by_op.values_mut().for_each(|ids| ids.clear());

        let mut trimmed = 0;

        let uf = &self.unionfind;
        for class in self.classes.iter_mut().filter_map(Option::as_mut) {
            let old_len = class.len();
            class
                .nodes
                .iter_mut()
                .for_each(|n| n.update_children(|id| uf.find(id)));
            class.nodes.sort_unstable();
            class.nodes.dedup();

            trimmed += old_len - class.nodes.len();

            // TODO this is the slow version, could take advantage of sortedness
            // maybe
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
            let unique: indexmap::IndexSet<Id> = ids.iter().copied().collect();
            assert_eq!(ids.len(), unique.len());
        }

        self.classes_by_op = classes_by_op;
        trimmed
    }

    #[inline(never)]
    fn check_memo(&self) -> bool {
        let mut test_memo = IndexMap::new();

        for (id, class) in self.classes.iter().enumerate() {
            let id = Id::from(id);
            let class = match class.as_ref() {
                Some(class) => class,
                None => continue,
            };
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

    #[inline(never)]
    fn process_unions(&mut self) {
        let mut to_union = vec![];

        while !self.dirty_unions.is_empty() {
            // take the worklist, we'll get the stuff that's added the next time around
            // deduplicate the dirty list to avoid extra work
            let mut todo = std::mem::take(&mut self.dirty_unions);
            todo.iter_mut().for_each(|id| *id = self.find(*id));
            if cfg!(not(feature = "upward-merging")) {
                todo.sort_unstable();
                todo.dedup();
            }
            assert!(!todo.is_empty());

            for id in todo {
                self.repairs_since_rebuild += 1;
                let mut parents = std::mem::take(&mut self[id].parents);

                for (n, _e) in &parents {
                    self.memo.remove(n);
                }

                parents.iter_mut().for_each(|(n, id)| {
                    n.update_children(|child| self.find(child));
                    *id = self.find(*id);
                });
                parents.sort_unstable();
                parents.dedup_by(|(n1, e1), (n2, e2)| {
                    n1 == n2 && {
                        to_union.push((*e1, *e2));
                        true
                    }
                });

                for (n, e) in &parents {
                    if let Some(old) = self.memo.insert(n.clone(), *e) {
                        to_union.push((old, *e));
                    }
                }

                self.propagate_metadata(&parents);

                self[id].parents = parents;
                N::modify(self, id);
            }

            for (id1, id2) in to_union.drain(..) {
                let (to, did_something) = self.union_impl(id1, id2);
                if did_something {
                    self.dirty_unions.push(to);
                }
            }
        }

        assert!(self.dirty_unions.is_empty());
        assert!(to_union.is_empty());
    }

    /// Restores the egraph invariants of congruence and enode uniqueness.
    ///
    /// As mentioned [above](struct.EGraph.html#invariants-and-rebuilding),
    /// `egg` takes a lazy approach to maintaining the egraph invariants.
    /// The `rebuild` method allows the user to manually restore those
    /// invariants at a time of their choosing. It's a reasonably
    /// fast, linear-ish traversal through the egraph.
    ///
    /// # Example
    /// ```
    /// use egg::{*, SymbolLang as S};
    /// let mut egraph = EGraph::<S, ()>::default();
    /// let x = egraph.add(S::leaf("x"));
    /// let y = egraph.add(S::leaf("y"));
    /// let ax = egraph.add_expr(&"(+ a x)".parse().unwrap());
    /// let ay = egraph.add_expr(&"(+ a y)".parse().unwrap());
    ///
    /// // The effects of this union aren't yet visible; ax and ay
    /// // should be equivalent by congruence since x = y.
    /// egraph.union(x, y);
    /// // Classes: [x y] [ax] [ay] [a]
    /// # #[cfg(not(feature = "upward-merging"))]
    /// assert_eq!(egraph.number_of_classes(), 4);
    /// # #[cfg(not(feature = "upward-merging"))]
    /// assert_ne!(egraph.find(ax), egraph.find(ay));
    ///
    /// // Rebuilding restores the invariants, finding the "missing" equivalence
    /// egraph.rebuild();
    /// // Classes: [x y] [ax ay] [a]
    /// assert_eq!(egraph.number_of_classes(), 3);
    /// assert_eq!(egraph.find(ax), egraph.find(ay));
    /// ```
    pub fn rebuild(&mut self) -> usize {
        let old_hc_size = self.memo.len();
        let old_n_eclasses = self.number_of_classes();

        let start = instant::Instant::now();

        self.process_unions();
        let n_unions = std::mem::take(&mut self.repairs_since_rebuild);
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
        n_unions
    }

    #[inline(never)]
    fn propagate_metadata(&mut self, parents: &[(L, Id)]) {
        for (n, e) in parents {
            let e = self.find(*e);
            let node_data = N::make(self, n);
            let class = self.classes[usize::from(e)].as_mut().unwrap();
            if self.analysis.merge(&mut class.data, node_data) {
                // self.dirty_unions.push(e); // NOTE: i dont think this is necessary
                let e_parents = std::mem::take(&mut class.parents);
                self.propagate_metadata(&e_parents);
                self[e].parents = e_parents;
                N::modify(self, e)
            }
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
            writeln!(f, "{}: {:?}", id, nodes)?
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use crate::*;

    #[test]
    fn simple_add() {
        use SymbolLang as S;

        crate::init_logger();
        let mut egraph = EGraph::<S, ()>::default();

        let x = egraph.add(S::leaf("x"));
        let x2 = egraph.add(S::leaf("x"));
        let _plus = egraph.add(S::new("+", vec![x, x2]));

        let y = egraph.add(S::leaf("y"));

        egraph.union(x, y);
        egraph.rebuild();

        egraph.dot().to_dot("target/foo.dot").unwrap();

        assert_eq!(2 + 2, 4);
    }
}
