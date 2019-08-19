use log::*;
use std::fmt::Debug;
use std::iter::ExactSizeIterator;

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;

use crate::{
    expr::{Expr, Id, Language, RecExpr},
    unionfind::{UnionFind, Value},
};

use indexmap::{IndexMap, IndexSet};

/// Data structure to keep track of equalities between expressions
#[derive(Debug)]
pub struct EGraph<L: Language, M> {
    memo: IndexMap<Expr<L, Id>, Id>,
    classes: UnionFind<Id, EClass<L, M>>,
    unions_since_rebuild: usize,
}

impl<L: Language, M> Default for EGraph<L, M> {
    fn default() -> EGraph<L, M> {
        EGraph {
            memo: IndexMap::default(),
            classes: UnionFind::default(),
            unions_since_rebuild: 0,
        }
    }
}

pub trait Metadata<L: Language>: Sized + Debug {
    type Error: Debug;
    fn merge(&self, other: &Self) -> Self;
    fn make(expr: Expr<L, &Self>) -> Self;
    fn modify(_eclass: &mut EClass<L, Self>) {}
}

impl<L: Language> Metadata<L> for () {
    type Error = std::convert::Infallible;
    fn merge(&self, _other: &()) {}
    fn make(_expr: Expr<L, &()>) {}
}

/// Struct that tells you whether or not an [`add`] modified the EGraph
///
/// ```
/// # use egg::egraph::EGraph;
/// # use egg::expr::tests::*;
/// let mut egraph = EGraph::<TestLang, ()>::default();
/// let x1 = egraph.add(var("x"));
/// let x2 = egraph.add(var("x"));
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

#[derive(Debug, Clone)]
pub struct EClass<L: Language, M> {
    pub id: Id,
    pub nodes: Vec<Expr<L, Id>>,
    pub metadata: M,
}

impl<L: Language, M> EClass<L, M> {
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = &Expr<L, Id>> {
        self.nodes.iter()
    }
}

impl<L: Language, M: Metadata<L>> Value for EClass<L, M> {
    type Error = std::convert::Infallible;
    fn merge<K>(
        _unionfind: &mut UnionFind<K, Self>,
        to: Self,
        from: Self,
    ) -> Result<Self, Self::Error> {
        let mut less = to.nodes;
        let mut more = from.nodes;

        // make sure less is actually smaller
        if more.len() < less.len() {
            std::mem::swap(&mut less, &mut more);
        }

        more.extend(less);
        let mut eclass = EClass {
            id: to.id,
            nodes: more,
            metadata: to.metadata.merge(&from.metadata),
        };
        M::modify(&mut eclass);
        Ok(eclass)
    }
}

impl<L: Language, M> EGraph<L, M> {
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
    /// # use egg::egraph::EGraph;
    /// # use egg::expr::tests::*;
    /// let mut egraph = EGraph::<TestLang, ()>::default();
    /// let x = egraph.add(var("x"));
    /// let y = egraph.add(var("y"));
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

    pub fn add(&mut self, enode: Expr<L, Id>) -> AddResult {
        trace!("Adding       {:?}", enode);

        // make sure that the enodes children are already in the set
        if cfg!(debug_assertions) {
            for &id in enode.children() {
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

        // hash cons
        match self.memo.get(&enode) {
            None => {
                // HACK knowing the next key like this is pretty bad
                let mut class = EClass {
                    id: self.classes.total_size() as Id,
                    nodes: vec![enode.clone()],
                    metadata: M::make(enode.map_children(|id| &self[id].metadata)),
                };
                M::modify(&mut class);
                let next_id = self.classes.make_set(class);
                trace!("Added  {:4}: {:?}", next_id, enode);
                let old = self.memo.insert(enode, next_id);
                assert_eq!(old, None);
                AddResult {
                    was_there: false,
                    id: next_id,
                }
            }
            Some(id) => {
                trace!("Added *{:4}: {:?}", id, enode);
                AddResult {
                    was_there: true,
                    id: *id,
                }
            }
        }
    }

    pub fn equivs(&self, expr1: &RecExpr<L>, expr2: &RecExpr<L>) -> Vec<Id> {
        use crate::pattern::Pattern;
        let matches1 = Pattern::from_expr(expr1).search(self);
        info!("Matches1: {:?}", matches1);

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

    fn rebuild_once(&mut self) -> usize {
        let mut new_memo = IndexMap::new();
        let mut to_union = Vec::new();
        let mut new_metas = IndexMap::new();

        for (leader, class) in self.classes.iter() {
            let mut class_metas = Vec::new();
            for node in &class.nodes {
                let n = node.update_ids(&self.classes);
                class_metas.push(M::make(n.map_children(|id| &self[id].metadata)));

                if let Some(old_leader) = new_memo.insert(n, leader) {
                    if old_leader != leader {
                        to_union.push((leader, old_leader));
                    }
                }
            }
            new_metas.insert(leader, class_metas);
        }

        for (leader, metas) in new_metas.drain(..) {
            let class = self.classes.get_mut(leader);
            for m in metas {
                class.metadata = class.metadata.merge(&m)
            }
        }

        let n_unions = to_union.len();
        for (id1, id2) in to_union {
            self.union(id1, id2);
        }

        self.memo = new_memo;
        n_unions
    }

    fn rebuild_classes(&mut self) -> usize {
        let mut trimmed = 0;
        let mut new_classes = Vec::new();
        for class in self.classes.values() {
            let mut new_nodes = IndexSet::new();
            for node in class.nodes.iter() {
                new_nodes.insert(node.update_ids(&self.classes));
            }
            trimmed += class.len() - new_nodes.len();
            let nodes: Vec<_> = new_nodes.into_iter().collect();
            new_classes.push((class.id, nodes));
        }

        for (id, nodes) in new_classes {
            let class = self.classes.get_mut(id);
            class.nodes = nodes
        }

        trimmed
    }

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

        #[cfg(not(target_arch = "wasm32"))]
        let start = Instant::now();

        loop {
            let u = self.rebuild_once();
            n_unions += u;
            n_rebuilds += 1;
            if u == 0 {
                break;
            }
        }

        let trimmed_nodes = self.rebuild_classes();

        #[cfg(not(target_arch = "wasm32"))]
        let elapsed = start.elapsed();

        #[cfg(target_arch = "wasm32")]
        info!(
            concat!(
                "REBUILT! {} times",
                "  Old: hc size {}, eclasses: {}\n",
                "  New: hc size {}, eclasses: {}\n",
                "  unions: {}, trimmed nodes: {}"
            ),
            n_rebuilds,
            old_hc_size,
            old_n_eclasses,
            self.memo.len(),
            self.classes.number_of_classes(),
            n_unions,
            trimmed_nodes,
        );
        #[cfg(not(target_arch = "wasm32"))]
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

    pub fn union(&mut self, id1: Id, id2: Id) -> Id {
        trace!("Unioning {} and {}", id1, id2);

        let to = self.classes.union(id1, id2).unwrap();
        self.unions_since_rebuild += 1;

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

    pub fn dump_dot(&self, filename: &str)
    where
        L::Constant: std::fmt::Display,
        L::Variable: std::fmt::Display,
        L::Operator: std::fmt::Display,
    {
        use std::fs::File;
        use std::io::prelude::*;

        let filename = format!("dots/{}", filename);
        std::fs::create_dir_all("dots").unwrap();

        let dot = crate::dot::Dot::new(self);
        let mut file = File::create(&filename).unwrap();
        write!(file, "{}", dot).unwrap();
        trace!("Writing {}...\n{}", filename, dot);
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::expr::tests::{op, var, TestLang};

    #[test]
    fn simple_add() {
        crate::init_logger();
        let mut egraph = EGraph::<TestLang, ()>::default();

        let x = egraph.add(var("x")).id;
        let x2 = egraph.add(var("x")).id;
        let _plus = egraph.add(op("+", vec![x, x2])).id;

        let y = egraph.add(var("y")).id;

        egraph.union(x, y);
        egraph.rebuild();

        egraph.dump_dot("foo.dot");

        assert_eq!(2 + 2, 4);
    }
}
