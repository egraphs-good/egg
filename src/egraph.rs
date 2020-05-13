use std::fmt::{self, Debug};

use indexmap::IndexMap;
use log::*;

use crate::{unionfind::UnionFind, Dot, EClass, ENode, Id, Language, Metadata, RecExpr};

/** A data structure to keep track of equalities between expressions.

# What's an egraph?

An egraph ([/'igraf/][sound]) is a data structure to maintain equivalence

classes of expressions.
An egraph conceptually is a set of eclasses, each of which
contains equivalent enodes.
An enode is conceptually and operator with children, but instead of
children being other operators or values, the children are eclasses.

In `egg`, these are respresented by the [`EGraph`], [`EClass`], and
[`ENode`] types.


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
[`EGraph`], [`EClass`], [`ENode`], and [`Id`].

[`EGraph`], [`EClass`], and [`ENode`] are all generic over a
[`Language`], meaning that types actually floating around in the
egraph are all user-defined.
In particular, [`ENode`]s contain operators from your [`Language`].
[`EGraph`]s and [`EClass`]es are additionally parameterized by some
[`Metadata`], abritrary data associated with each eclass.

Many methods of [`EGraph`] deal with [`Id`]s, which represent eclasses.
Because eclasses are frequently merged, many [`Id`]s will refer to the
same eclass.

[`EGraph`]: struct.EGraph.html
[`EClass`]: struct.EClass.html
[`ENode`]: struct.ENode.html
[`Rewrite`]: struct.Rewrite.html
[`Runner`]: struct.Runner.html
[`Language`]: trait.Language.html
[`Metadata`]: trait.Metadata.html
[`Id`]: type.Id.html
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
pub struct EGraph<L, M> {
    memo: IndexMap<ENode<L>, Id>,
    classes: UnionFind<Id, EClass<L, M>>,
    dirty_unions: Vec<Id>,
    pub(crate) classes_by_op: IndexMap<(L, usize), Vec<Id>>,
}

// manual debug impl to avoid L: Language bound on EGraph defn
impl<L: Language, M: Debug> Debug for EGraph<L, M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("EGraph")
            .field("memo", &self.memo)
            .field("classes", &self.classes)
            .finish()
    }
}

impl<L, M> Default for EGraph<L, M> {
    /// Returns an empty egraph.
    fn default() -> EGraph<L, M> {
        EGraph {
            memo: IndexMap::default(),
            classes: UnionFind::default(),
            dirty_unions: Default::default(),
            classes_by_op: IndexMap::default(),
        }
    }
}

impl<L, M> EGraph<L, M> {
    /// Returns an iterator over the eclasses in the egraph.
    pub fn classes(&self) -> impl Iterator<Item = &EClass<L, M>> {
        self.classes.values()
    }

    /// Returns an mutating iterator over the eclasses in the egraph.
    pub fn classes_mut(&mut self) -> impl Iterator<Item = &mut EClass<L, M>> {
        self.classes.values_mut()
    }

    /// Returns `true` if the egraph is empty
    /// # Example
    /// ```
    /// # use egg::*;
    /// let mut egraph = EGraph::<String, ()>::default();
    /// assert!(egraph.is_empty());
    /// egraph.add(enode!("foo"));
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
    /// # use egg::*;
    /// let mut egraph = EGraph::<String, ()>::default();
    /// let x = egraph.add(enode!("x"));
    /// let y = egraph.add(enode!("y"));
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
        self.classes.number_of_classes()
    }

    /// Canonicalizes an eclass id.
    ///
    /// This corresponds to the `find` operation on the egraph's
    /// underlying unionfind data structure.
    ///
    /// # Example
    /// ```
    /// # use egg::*;
    /// let mut egraph = EGraph::<String, ()>::default();
    /// let x = egraph.add(enode!("x"));
    /// let y = egraph.add(enode!("y"));
    /// assert_ne!(egraph.find(x), egraph.find(y));
    ///
    /// egraph.union(x, y);
    /// assert_eq!(egraph.find(x), egraph.find(y));
    /// ```
    pub fn find(&self, id: Id) -> Id {
        self.classes.find(id)
    }

    fn canonicalize(&self, enode: &mut ENode<L>) {
        enode.children.iter_mut().for_each(|c| *c = self.find(*c))
    }

    /// Creates a [`Dot`] to visualize this egraph. See [`Dot`].
    ///
    /// [`Dot`]: struct.Dot.html
    pub fn dot(&self) -> Dot<L, M> {
        Dot::new(self)
    }
}

impl<L, M> std::ops::Index<Id> for EGraph<L, M> {
    type Output = EClass<L, M>;
    fn index(&self, id: Id) -> &Self::Output {
        self.classes.get(id)
    }
}

impl<L, M> std::ops::IndexMut<Id> for EGraph<L, M> {
    fn index_mut(&mut self, id: Id) -> &mut Self::Output {
        self.classes.get_mut(id)
    }
}

impl<L: Language, M: Metadata<L>> EGraph<L, M> {
    /// Create an egraph from a [`RecExpr`].
    /// Equivalent to calling [`add_expr`] on an empty [`EGraph`].
    ///
    /// [`EGraph`]: struct.EGraph.html
    /// [`RecExpr`]: struct.RecExpr.html
    /// [`add_expr`]: struct.EGraph.html#method.add_expr
    pub fn from_expr(expr: &RecExpr<L>) -> (Self, Id) {
        let mut egraph = EGraph::default();
        let root = egraph.add_expr(expr);
        (egraph, root)
    }

    /// Adds a [`RecExpr`] to the [`EGraph`].
    ///
    /// # Example
    /// ```
    /// # use egg::*;
    /// let mut egraph = EGraph::<String, ()>::default();
    /// let x = egraph.add(enode!("x"));
    /// let y = egraph.add(enode!("y"));
    /// let plus = egraph.add(enode!("+", x, y));
    /// let plus_recexpr = "(+ x y)".parse().unwrap();
    /// assert_eq!(plus, egraph.add_expr(&plus_recexpr));
    /// ```
    ///
    /// [`EGraph`]: struct.EGraph.html
    /// [`RecExpr`]: struct.RecExpr.html
    /// [`add_expr`]: struct.EGraph.html#method.add_expr
    pub fn add_expr(&mut self, expr: &RecExpr<L>) -> Id {
        let e = expr.as_ref().map_children(|child| self.add_expr(&child));
        self.add(e)
    }

    /// Adds an [`ENode`] to the [`EGraph`].
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
    /// [`ENode`]: struct.ENode.html
    /// [`add`]: struct.EGraph.html#method.add
    pub fn add(&mut self, mut enode: ENode<L>) -> Id {
        self.canonicalize(&mut enode);

        let id = self.classes.total_size() as Id;

        match self.memo.get(&enode) {
            Some(id) => self.find(*id),
            None => {
                trace!("Adding {:?}", enode);
                let class = EClass {
                    id,
                    nodes: vec![enode.clone()],
                    metadata: M::make(self, &enode),
                    parents: Default::default(),
                };

                // add this enode to the parent lists of its children
                for &child in &enode.children {
                    let tup = (enode.clone(), id);
                    self[child].parents.push(tup);
                }

                let next_id = self.classes.make_set(class);
                debug_assert_eq!(next_id, id);
                let old = self.memo.insert(enode, next_id);
                assert_eq!(old, None);

                M::modify(self, id);
                next_id
            }
        }
    }

    /// Checks whether two [`RecExpr`]s are equivalent.
    /// Returns a list of id where both expression are represented.
    /// In most cases, there will none or exactly one id.
    ///
    /// [`RecExpr`]: struct.RecExpr.html
    pub fn equivs(&self, expr1: &RecExpr<L>, expr2: &RecExpr<L>) -> Vec<Id> {
        use crate::{Pattern, Searcher};
        let matches1 = Pattern::from(expr1.clone()).search(self);
        trace!("Matches1: {:?}", matches1);

        let matches2 = Pattern::from(expr2.clone()).search(self);
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

    #[inline]
    fn union_impl(&mut self, id1: Id, id2: Id) -> (Id, bool) {
        let (to, did_something) = self.classes.union(id1, id2).unwrap();
        if did_something {
            self.dirty_unions.push(to);
            M::modify(self, to);
            #[cfg(feature = "upward-merging")]
            self.process_unions();
        }
        (to, did_something)
    }

    /// Unions two eclasses given their ids.
    ///
    /// The given ids need not be canonical.
    /// If the two eclasses were actually the same, this does nothing.
    /// This returns the canonical id of the merged eclass.
    pub fn union(&mut self, id1: Id, id2: Id) -> Id {
        self.union_impl(id1, id2).0
    }

    /// Unions two eclasses given their ids.
    ///
    /// Same as [`union`](struct.EGraph.html#method.union), but it
    /// returns None if the two given ids refer to the same eclass.
    pub fn union_if_different(&mut self, id1: Id, id2: Id) -> Option<Id> {
        let (to, did_something) = self.union_impl(id1, id2);
        if did_something {
            Some(to)
        } else {
            None
        }
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
impl<L: Language, M: Metadata<L>> EGraph<L, M> {
    #[inline(never)]
    fn rebuild_classes(&mut self) -> usize {
        let (find, mut_values) = self.classes.split();

        let mut classes_by_op = std::mem::take(&mut self.classes_by_op);
        classes_by_op.clear();

        let mut trimmed = 0;

        // let mut memo = IndexMap::new(); // std::mem::take(&mut self.memo);
        // self.memo.clear();

        for class in mut_values {
            let old_len = class.len();
            class
                .nodes
                .iter_mut()
                .for_each(|n| n.children.iter_mut().for_each(|id| *id = find(*id)));
            class.nodes.sort_unstable();
            class.nodes.dedup();

            trimmed += old_len - class.nodes.len();

            // for n in &class.nodes {
            //     self.memo.insert(n.clone(), class.id);
            // }

            let mut add = |op: &L, len: usize| {
                classes_by_op
                    .entry((op.clone(), len))
                    .or_default()
                    .push(class.id)
            };

            // we can go through the ops in order to dedup them, becaue we
            // just sorted them
            let mut ops_and_lens = class.nodes.iter().map(|n| (&n.op, n.children.len()));
            // let mut prev = ops_and_lens.next().unwrap_or_else(|| panic!("Empty eclass! {:?}", class));
            if let Some(mut prev) = ops_and_lens.next() {
                add(&prev.0, prev.1);
                for tup in ops_and_lens {
                    if tup != prev {
                        add(&tup.0, tup.1);
                        prev = tup;
                    }
                }
            }
        }

        // self.memo = memo;
        self.classes_by_op = classes_by_op;
        trimmed
    }

    #[inline(never)]
    fn check_memo(&self) -> bool {
        let mut new_memo = IndexMap::new();

        for class in self.classes() {
            for node in &class.nodes {
                if let Some(old) = new_memo.insert(node, class.id) {
                    assert_eq!(
                        self.find(old),
                        self.find(class.id),
                        "Found unexpected equivalence for {:?}",
                        node
                    );
                }
            }
        }

        for (n, e) in new_memo {
            assert_eq!(Some(e), self.memo.get(n).map(|id| self.find(*id)));
        }

        true
    }

    #[inline(never)]
    fn process_unions(&mut self) -> usize {
        let mut n_unions = 0;
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
                n_unions += 1;
                let mut parents = std::mem::take(&mut self[id].parents);

                for (n, _e) in &parents {
                    self.memo.remove(n);
                }

                parents.iter_mut().for_each(|(n, id)| {
                    self.canonicalize(n);
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
                M::modify(self, id);
            }

            for (id1, id2) in to_union.drain(..) {
                let (to, did_something) = self.classes.union(id1, id2).unwrap();
                if did_something {
                    self.dirty_unions.push(to);
                }
            }
        }

        assert!(self.dirty_unions.is_empty());
        assert!(to_union.is_empty());
        n_unions
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
    /// # use egg::*;
    /// let mut egraph = EGraph::<String, ()>::default();
    /// let x = egraph.add(enode!("x"));
    /// let y = egraph.add(enode!("y"));
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
        let old_n_eclasses = self.classes.number_of_classes();

        let start = instant::Instant::now();

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
            self.classes.number_of_classes(),
            n_unions,
            trimmed_nodes,
        );

        debug_assert!(self.check_memo());
        n_unions
    }

    #[inline(never)]
    fn propagate_metadata(&mut self, parents: &[(ENode<L>, Id)]) {
        for (n, e) in parents {
            let node_meta = M::make(self, n);
            let class = &mut self[*e];
            let new_meta = class.metadata.merge(&node_meta);
            if class.metadata != new_meta {
                class.metadata = new_meta;
                // self.dirty_unions.push(*e);
                let e_parents = std::mem::take(&mut self[*e].parents);
                self.propagate_metadata(&e_parents);
                self[*e].parents = e_parents;
                M::modify(self, *e);
            }
        }
    }
}

struct EGraphDump<'a, L, M>(&'a EGraph<L, M>);

impl<'a, L, M> Debug for EGraphDump<'a, L, M>
where
    L: Language,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for class in self.0.classes() {
            writeln!(f, "{}: {:?}", class.id, class.nodes)?
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use crate::{enode as e, *};

    #[test]
    fn simple_add() {
        crate::init_logger();
        let mut egraph = EGraph::<String, ()>::default();

        let x = egraph.add(e!("x"));
        let x2 = egraph.add(e!("x"));
        let _plus = egraph.add(e!("+", x, x2));

        let y = egraph.add(e!("y"));

        egraph.union(x, y);
        egraph.rebuild();

        egraph.dot().to_dot("target/foo.dot").unwrap();

        assert_eq!(2 + 2, 4);
    }
}
