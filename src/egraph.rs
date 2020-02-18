use std::fmt::{self, Debug};

use indexmap::{IndexMap, IndexSet};
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
[`Runner`]: trait.Runner.html
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
    unions_since_rebuild: usize,
}

// manual debug impl to avoid L: Language bound on EGraph defn
impl<L: Language, M: Debug> Debug for EGraph<L, M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("EGraph")
            .field("memo", &self.memo)
            .field("classes", &self.classes)
            .field("unions_since_rebuild", &self.unions_since_rebuild)
            .finish()
    }
}

impl<L, M> Default for EGraph<L, M> {
    /// Returns an empty egraph.
    fn default() -> EGraph<L, M> {
        EGraph {
            memo: IndexMap::default(),
            classes: UnionFind::default(),
            unions_since_rebuild: 0,
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
    ///
    /// assert_eq!(egraph.total_size(), 2);
    /// assert_eq!(egraph.number_of_classes(), 1);
    /// ```
    pub fn total_size(&self) -> usize {
        let union_find_size = self.classes.total_size();
        debug_assert_eq!(union_find_size, self.memo.len());
        union_find_size
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

    /// Creates a [`Dot`] to visualize this egraph. See [`Dot`].
    ///
    /// [`Dot`]: struct.Dot.html
    pub fn dot(&self) -> Dot<L, M> {
        Dot::new(self)
    }
}

impl<L: Language, M> std::ops::Index<Id> for EGraph<L, M> {
    type Output = EClass<L, M>;
    fn index(&self, id: Id) -> &Self::Output {
        self.classes.get(id)
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
    pub fn add(&mut self, enode: ENode<L>) -> Id {
        trace!("Adding       {:?}", enode);

        // make sure that the enodes children are already in the set
        if cfg!(debug_assertions) {
            for &id in &enode.children {
                if id >= self.classes.total_size() as u32 {
                    panic!(
                        "Expr: {:?}\n  Found id {} but classes.len() = {}",
                        enode,
                        id,
                        self.classes.total_size()
                    );
                }
            }
        }

        match self.memo.get(&enode) {
            Some(&id) => {
                trace!("Found     {}: {:?}", id, enode);
                self.classes.find(id)
            }
            None => self.add_unchecked(enode),
        }
    }

    fn add_unchecked(&mut self, enode: ENode<L>) -> Id {
        // HACK knowing the next key like this is pretty bad
        let mut class = EClass {
            id: self.classes.total_size() as Id,
            nodes: vec![enode.clone()],
            metadata: M::make(enode.map_children(|id| &self[id].metadata)),
            #[cfg(feature = "parent-pointers")]
            parents: IndexSet::new(),
        };
        M::modify(&mut class);
        let next_id = self.classes.make_set(class);
        trace!("Added  {:4}: {:?}", next_id, enode);

        let (idx, old) = self.memo.insert_full(enode, next_id);
        let _ = idx;
        #[cfg(feature = "parent-pointers")]
        for &child in &self.memo.get_index(idx).unwrap().0.children {
            self.classes.get_mut(child).parents.insert(idx);
        }

        assert_eq!(old, None);
        next_id
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
                if m1.eclass == m2.eclass {
                    equiv_eclasses.push(m1.eclass)
                }
            }
        }

        equiv_eclasses
    }

    #[cfg(not(feature = "parent-pointers"))]
    fn rebuild_once(&mut self) -> usize {
        let mut new_memo = IndexMap::new();
        let mut to_union = Vec::new();

        for (leader, class) in self.classes.iter() {
            for node in &class.nodes {
                let n = node.update_ids(&self.classes);
                if let Some(old_leader) = new_memo.insert(n, leader) {
                    if old_leader != leader {
                        to_union.push((leader, old_leader));
                    }
                }
            }
        }

        let n_unions = to_union.len();
        for (id1, id2) in to_union {
            self.union(id1, id2);
        }

        n_unions
    }

    fn rebuild_classes(&mut self) -> usize {
        let mut trimmed = 0;

        let (find, mut_values) = self.classes.split();
        for class in mut_values {
            let old_len = class.len();

            let unique: IndexSet<_> = class
                .nodes
                .iter()
                .map(|node| node.map_children(&find))
                .collect();

            trimmed += old_len - unique.len();

            class.nodes.clear();
            class.nodes.extend(unique);
        }

        trimmed
    }

    /// Does very little since you're in parent-pointers mode.
    #[cfg(feature = "parent-pointers")]
    pub fn rebuild(&mut self) {
        info!("Skipping rebuild because we have parent pointers");
        self.rebuild_classes();
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
    /// assert_eq!(egraph.number_of_classes(), 4);
    /// assert_ne!(egraph.find(ax), egraph.find(ay));
    ///
    /// // Rebuilding restores the invariants, finding the "missing" equivalence
    /// egraph.rebuild();
    /// // Classes: [x y] [ax ay] [a]
    /// assert_eq!(egraph.number_of_classes(), 3);
    /// assert_eq!(egraph.find(ax), egraph.find(ay));
    /// ```
    #[cfg(not(feature = "parent-pointers"))]
    pub fn rebuild(&mut self) {
        if self.unions_since_rebuild == 0 {
            info!("Skipping rebuild!");
            return;
        }

        self.unions_since_rebuild = 0;

        let old_hc_size = self.memo.len();
        let old_n_eclasses = self.classes.number_of_classes();
        let mut n_rebuilds = 0;
        let mut n_unions = 0;

        let start = instant::Instant::now();

        loop {
            let u = self.rebuild_once();
            n_unions += u;
            n_rebuilds += 1;
            if u == 0 {
                break;
            }
        }

        let trimmed_nodes = self.rebuild_classes();

        let elapsed = start.elapsed();
        info!(
            concat!(
                "REBUILT! {} times in {}.{:03}s\n",
                "  Old: hc size {}, eclasses: {}\n",
                "  New: hc size {}, eclasses: {}\n",
                "  unions: {}, trimmed nodes: {}"
            ),
            n_rebuilds,
            elapsed.as_secs(),
            elapsed.subsec_millis(),
            old_hc_size,
            old_n_eclasses,
            self.memo.len(),
            self.classes.number_of_classes(),
            n_unions,
            trimmed_nodes,
        );
    }

    /// Unions two eclasses given their ids.
    ///
    /// The given ids need not be canonical.
    /// If the two eclasses were actually the same, this does nothing.
    /// This returns the canonical id of the merged eclass.
    pub fn union(&mut self, id1: Id, id2: Id) -> Id {
        self.union_depth(0, id1, id2)
    }

    /// Unions two eclasses given their ids.
    ///
    /// Same as [`union`](struct.EGraph.html#method.union), but it
    /// returns None if the two given ids refer to the same eclass.
    pub fn union_if_different(&mut self, id1: Id, id2: Id) -> Option<Id> {
        let id1 = self.find(id1);
        let id2 = self.find(id2);
        if id1 == id2 {
            None
        } else {
            Some(self.union(id1, id2))
        }
    }

    fn union_depth(&mut self, depth: usize, id1: Id, id2: Id) -> Id {
        trace!("Unioning (d={}) {} and {}", depth, id1, id2);
        let (to, did_something) = self.classes.union(id1, id2).unwrap();
        if !did_something {
            return to;
        }
        self.unions_since_rebuild += 1;

        #[cfg(feature = "parent-pointers")]
        self.upward(to);

        // #[cfg(feature = "parent-pointers")] {
        //     self.classes.get_mut(to).nodes = self[to]
        //         .nodes
        //         .iter()
        //         .map(|n| n.update_ids(&self.classes))
        //         .collect::<IndexSet<_>>()
        //         .into_iter()
        //         .collect();
        // }

        if log_enabled!(Level::Trace) {
            let from = if to == id1 { id2 } else { id1 };
            trace!("Unioned {} -> {}", from, to);
            trace!("Classes: {:?}", self.classes);
            for (leader, class) in self.classes.iter() {
                trace!("  {:?}: {:?}", leader, class);
            }
        }
        to
    }

    #[cfg(feature = "parent-pointers")]
    fn upward(&mut self, id: Id) {
        use itertools::Itertools;

        let mut t = 0;
        let mut ids = vec![id];
        let mut done = IndexSet::new();

        while let Some(id) = ids.pop() {
            t += 1;
            let id = self.classes.find(id);
            if !done.insert(id) {
                continue;
            }

            if t > 1000 && t % 1000 == 0 {
                warn!("Long time: {}, to do: {}", t, ids.len());
            }

            let map = self[id]
                .parents
                .iter()
                .map(|p| {
                    let (expr, id) = self.memo.get_index(*p).unwrap();
                    let expr = expr.update_ids(&self.classes);
                    (expr, *id)
                })
                .into_group_map();

            for (_expr, same_ids) in map {
                if same_ids.len() > 1 {
                    let id0 = same_ids[0];
                    let mut did_union = false;
                    for id in same_ids[1..].iter() {
                        did_union |= self.classes.union(id0, *id).unwrap().1;
                    }
                    if did_union {
                        ids.push(id0);
                    }
                }
            }
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
