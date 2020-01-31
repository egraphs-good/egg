use std::fmt::{self, Debug};

use indexmap::{IndexMap, IndexSet};
use log::*;

use crate::{unionfind::UnionFind, Dot, EClass, ENode, Id, Language, Metadata, RecExpr};

/// Data structure to keep track of equalities between expressions
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
    fn default() -> EGraph<L, M> {
        EGraph {
            memo: IndexMap::default(),
            classes: UnionFind::default(),
            unions_since_rebuild: 0,
        }
    }
}

/// Struct that tells you whether or not an [`add`] modified the EGraph
///
/// ```
/// # use egg::*;
/// let mut egraph = EGraph::<String, ()>::default();
/// let x1 = egraph.add(enode!("x"));
/// let x2 = egraph.add(enode!("x"));
///
/// assert_eq!(x1.id, x2.id);
/// assert!(!x1.was_there);
/// assert!(x2.was_there);
/// ```
///
/// [`add`]: struct.EGraph.html#method.add
#[derive(Debug)]
pub struct AddResult {
    pub was_there: bool,
    pub id: Id,
}

impl<L, M> EGraph<L, M> {
    pub fn dot(&self) -> Dot<L, M> {
        Dot::new(self)
    }

    pub fn classes(&self) -> impl Iterator<Item = &EClass<L, M>> {
        self.classes.values()
    }

    pub fn classes_mut(&mut self) -> impl Iterator<Item = &mut EClass<L, M>> {
        self.classes.values_mut()
    }

    pub fn is_empty(&self) -> bool {
        self.memo.is_empty()
    }

    /// Returns the number of nodes in the `EGraph`.
    ///
    /// Actually returns the size of the hash cons index.
    /// ```
    /// # use egg::*;
    /// let mut egraph = EGraph::<String, ()>::default();
    /// let x = egraph.add(enode!("x"));
    /// let y = egraph.add(enode!("y"));
    /// // only one eclass
    /// egraph.union(x.id, y.id);
    ///
    /// assert_eq!(egraph.total_size(), 2);
    /// ```
    pub fn total_size(&self) -> usize {
        self.classes.total_size()
    }

    pub fn number_of_classes(&self) -> usize {
        self.classes.number_of_classes()
    }

    pub fn find(&self, id: Id) -> Id {
        self.classes.find(id)
    }
}

impl<L: Language, M> std::ops::Index<Id> for EGraph<L, M> {
    type Output = EClass<L, M>;
    fn index(&self, id: Id) -> &Self::Output {
        self.classes.get(id)
    }
}

impl<L: Language, M: Metadata<L>> EGraph<L, M> {
    pub fn from_expr(expr: &RecExpr<L>) -> (Self, Id) {
        let mut egraph = EGraph::default();
        let root = egraph.add_expr(expr);
        (egraph, root)
    }

    pub fn add_expr(&mut self, expr: &RecExpr<L>) -> Id {
        let e = expr.as_ref().map_children(|child| self.add_expr(&child));
        self.add(e).id
    }

    pub fn add(&mut self, enode: ENode<L>) -> AddResult {
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
                AddResult {
                    was_there: true,
                    id: self.classes.find(id),
                }
            }
            None => self.add_unchecked(enode),
        }
    }

    fn add_unchecked(&mut self, enode: ENode<L>) -> AddResult {
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
        AddResult {
            was_there: false,
            id: next_id,
        }
    }

    pub fn equivs(&self, expr1: &RecExpr<L>, expr2: &RecExpr<L>) -> Vec<Id> {
        use crate::pattern::Pattern;
        // debug!("Searching for expr1: {}", expr1.to_sexp());
        let matches1 = Pattern::from_expr(expr1).search(self);
        info!("Matches1: {:?}", matches1);

        // debug!("Searching for expr2: {}", expr2.to_sexp());
        let matches2 = Pattern::from_expr(expr2).search(self);
        info!("Matches2: {:?}", matches2);

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

    #[cfg(feature = "parent-pointers")]
    pub fn rebuild(&mut self) {
        info!("Skipping rebuild because we have parent pointers");
        self.rebuild_classes();
    }

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

    #[inline(always)]
    pub fn union(&mut self, id1: Id, id2: Id) -> Id {
        self.union_depth(0, id1, id2)
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

        let x = egraph.add(e!("x")).id;
        let x2 = egraph.add(e!("x")).id;
        let _plus = egraph.add(e!("+", x, x2)).id;

        let y = egraph.add(e!("y")).id;

        egraph.union(x, y);
        egraph.rebuild();

        egraph.dot().to_dot("target/foo.dot").unwrap();

        assert_eq!(2 + 2, 4);
    }
}
