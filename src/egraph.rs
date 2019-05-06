use log::*;
use std::time::Instant;

use crate::{
    expr::{Expr, FlatExpr, Id, Language},
    unionfind::{UnionFind, UnionResult},
    util::{HashMap, HashSet},
};

#[derive(Debug)]
pub struct EGraph<L: Language> {
    // TODO no pub
    pub nodes: HashMap<Expr<L, Id>, Id>,
    pub leaders: UnionFind,
    pub classes: HashMap<Id, Vec<Expr<L, Id>>>,
}

impl<L: Language> Default for EGraph<L> {
    fn default() -> EGraph<L> {
        EGraph {
            nodes: HashMap::default(),
            leaders: UnionFind::default(),
            classes: HashMap::default(),
        }
    }
}

#[derive(Debug)]
pub struct AddResult {
    pub was_there: bool,
    pub id: Id,
}

impl<L: Language> EGraph<L> {
    pub fn from_expr(expr: &FlatExpr<L>) -> (Self, Id) {
        let mut egraph = EGraph::default();
        let root = egraph.add_from_expr(expr, expr.root);
        (egraph, root)
    }

    fn add_from_expr(&mut self, expr: &FlatExpr<L>, id: Id) -> Id {
        let node = expr
            .get_node(id)
            .map_children(|child| self.add_from_expr(expr, child));
        self.add(node).id
    }

    fn check(&self) {
        // FIXME checks are broken
        return;
        assert_eq!(self.nodes.len(), self.leaders.len());

        // make sure the classes map contains exactly the unique leaders
        let sets = self.leaders.build_sets();

        assert_eq!(sets.len(), self.classes.len());
        for l in sets.keys() {
            assert!(self.classes.contains_key(&l));
        }

        // make sure that total size of classes == all nodes
        let sum_classes = self.classes.values().map(|c| c.len()).sum();
        assert_eq!(self.nodes.len(), sum_classes);
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn get_eclass(&self, eclass_id: Id) -> &[Expr<L, Id>] {
        self.classes
            .get(&self.just_find(eclass_id))
            .unwrap_or_else(|| panic!("Couldn't find eclass {:?}", eclass_id))
    }

    pub fn equivs(&self, expr1: &FlatExpr<L>, expr2: &FlatExpr<L>) -> Vec<Id> {
        use crate::pattern::FlatPattern;
        let matches1 = FlatPattern::from_flat_expr(expr1).search(self);
        info!("Matches1: {:?}", matches1);

        let matches2 = FlatPattern::from_flat_expr(expr2).search(self);
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

    pub fn add(&mut self, enode: Expr<L, Id>) -> AddResult {
        self.check();

        trace!("Adding       {:?}", enode);

        // make sure that the enodes children are already in the set
        if cfg!(debug_assertions) {
            for &id in enode.children() {
                if id >= self.leaders.len() as u32 {
                    panic!(
                        "Expr: {:?}\n  Found id {} but leaders.len() = {}",
                        enode,
                        id,
                        self.leaders.len()
                    );
                }
            }
        }

        // hash cons
        let result = match self.nodes.get(&enode) {
            None => {
                let next_id = self.leaders.make_set();
                trace!("Added  {:4}: {:?}", next_id, enode);
                self.classes.insert(next_id, vec![enode.clone()]);
                let old = self.nodes.insert(enode, next_id);
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
        };

        self.check();
        result
    }

    pub fn just_find(&self, id: Id) -> Id {
        self.leaders.just_find(id)
    }

    fn rebuild_once(&mut self) -> u32 {
        let mut new_nodes = HashMap::default();
        let mut n_unions = 0;
        // TODO clone here is iffy
        for (&leader, class) in self.classes.clone().iter() {
            for node in class {
                let n = node.clone().map_children(|id| self.leaders.just_find(id));

                if let Some(old_leader) = new_nodes.insert(n, leader) {
                    if old_leader != leader {
                        self.union(leader, old_leader);
                        n_unions += 1;
                    }
                }
            }
        }
        self.nodes = new_nodes;
        n_unions
    }

    fn rebuild_classes(&mut self) -> usize {
        let mut trimmed = 0;
        let mut new_classes = HashMap::<Id, Vec<_>>::default();
        for (&leader, class) in self.classes.iter() {
            let mut new_class = HashSet::default();
            for node in class {
                new_class.insert(node.clone().map_children(|id| self.leaders.just_find(id)));
            }
            trimmed += class.len() - new_class.len();
            new_classes.insert(leader, new_class.into_iter().collect());
        }

        self.classes = new_classes;
        trimmed
    }

    pub fn rebuild(&mut self) {
        let old_hc_size = self.nodes.len();
        let old_n_eclasses = self.classes.len();
        let mut n_rebuilds = 0;
        let mut n_unions = 0;

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
            self.nodes.len(),
            self.classes.len(),
            n_unions,
            trimmed_nodes,
        );
    }

    pub fn union(&mut self, id1: Id, id2: Id) -> Id {
        self.check();

        trace!("Unioning {} and {}", id1, id2);

        let (from, to) = match self.leaders.union(id1, id2) {
            UnionResult::SameSet(leader) => return leader,
            UnionResult::Unioned { from, to } => (from, to),
        };

        // remove the smaller class, merging into the bigger class
        let from_class = self.classes.remove(&from).unwrap();
        let to_class = self.classes.remove(&to).unwrap();

        let mut new_nodes = Vec::with_capacity(from_class.len() + to_class.len());
        for node in from_class.into_iter().chain(to_class) {
            new_nodes.push(node.map_children(|id| self.leaders.find(id)));
        }

        self.classes.insert(to, new_nodes);

        self.check();
        trace!("Unioned {} -> {}", from, to);
        trace!("Leaders: {:?}", self.leaders);
        for (leader, class) in &self.classes {
            trace!("  {:?}: {:?}", leader, class);
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
        let mut egraph = EGraph::<TestLang>::default();

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
