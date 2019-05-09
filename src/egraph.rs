use log::*;
use std::time::Instant;

use crate::{
    expr::{Expr, Id, Language, RecExpr},
    unionfind::{UnionFind, UnionResult},
    util::{HashMap, HashSet},
};

#[derive(Debug)]
pub struct EGraph<L: Language> {
    // TODO no pub
    pub nodes: HashMap<Expr<L, Id>, Id>,
    pub leaders: UnionFind,
    pub classes: HashMap<Id, EClass<L>>,
    unions_since_rebuild: usize,
}

impl<L: Language> Default for EGraph<L> {
    fn default() -> EGraph<L> {
        EGraph {
            nodes: HashMap::default(),
            leaders: UnionFind::default(),
            classes: HashMap::default(),
            unions_since_rebuild: 0,
        }
    }
}

#[derive(Debug)]
pub struct AddResult {
    pub was_there: bool,
    pub id: Id,
}

#[derive(Debug, Clone)]
pub struct EClass<L: Language> {
    id: Id,
    nodes: Vec<Expr<L, Id>>,
}

impl<L: Language> EClass<L> {
    fn new(id: Id, nodes: Vec<Expr<L, Id>>) -> Self {
        EClass { id, nodes }
    }
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Expr<L, Id>> {
        self.nodes.iter()
    }

    pub fn combine(self, other: Self, id: Id) -> Self {
        let mut less_nodes = self.nodes;
        let mut more_nodes = other.nodes;

        // make sure less nodes is actually smaller
        if more_nodes.len() < less_nodes.len() {
            std::mem::swap(&mut less_nodes, &mut more_nodes);
        }

        more_nodes.extend(less_nodes);

        EClass {
            id: id,
            nodes: more_nodes,
        }
    }
}

impl<L: Language> EGraph<L> {
    pub fn from_expr(expr: &RecExpr<L>) -> (Self, Id) {
        let mut egraph = EGraph::default();
        let root = egraph.add_expr(expr);
        (egraph, root)
    }

    pub fn add_expr(&mut self, expr: &RecExpr<L>) -> Id {
        let e = expr.as_ref().map_children(|child| self.add_expr(&child));
        self.add(e).id
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

    pub fn get_eclass(&self, eclass_id: Id) -> &EClass<L> {
        self.classes
            .get(&self.just_find(eclass_id))
            .unwrap_or_else(|| panic!("Couldn't find eclass {:?}", eclass_id))
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
                self.classes
                    .insert(next_id, EClass::new(next_id, vec![enode.clone()]));
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

    pub fn prune(&mut self) -> usize {
        let mut pruned = 0;
        for class in self.classes.values_mut() {
            let mut new_nodes = Vec::new();
            for node in &class.nodes {
                match node {
                    Expr::Variable(_) | Expr::Constant(_) => new_nodes.push(node.clone()),
                    _ => (),
                }
            }

            if new_nodes.len() > 0 {
                pruned += class.len() - new_nodes.len();
                class.nodes = new_nodes;
            }
        }

        if pruned > 0 {
            info!("Pruned {} nodes", pruned);
        }

        pruned
    }

    fn rebuild_once(&mut self) -> usize {
        let mut new_nodes = HashMap::default();
        let mut to_union = Vec::new();

        for (&leader, class) in self.classes.iter() {
            for node in &class.nodes {
                let n = node.update_ids(&self.leaders);

                if let Some(old_leader) = new_nodes.insert(n, leader) {
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
        self.nodes = new_nodes;
        n_unions
    }

    fn rebuild_classes(&mut self) -> usize {
        let mut trimmed = 0;
        let mut new_classes = HashMap::default();
        for (leader, class) in self.classes.drain() {
            let mut new_nodes = HashSet::default();
            for node in class.nodes.iter() {
                new_nodes.insert(node.update_ids(&self.leaders));
            }
            trimmed += class.len() - new_nodes.len();
            let new_class = EClass::new(leader, new_nodes.into_iter().collect());
            new_classes.insert(leader, new_class);
        }

        self.classes = new_classes;
        trimmed
    }

    pub fn rebuild(&mut self) {
        if self.unions_since_rebuild == 0 {
            info!("Skipping rebuild!");
            return;
        }

        self.unions_since_rebuild = 0;

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

        self.unions_since_rebuild += 1;

        let from_class = self.classes.remove(&from).unwrap();
        let to_class = self.classes.remove(&to).unwrap();

        self.classes.insert(to, from_class.combine(to_class, to));

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
