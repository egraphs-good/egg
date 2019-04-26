mod unionfind;

pub mod dot;
pub mod parse;

use std::collections::HashMap;

use log::*;

use unionfind::{UnionFind, UnionResult};

/// EClass Id
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EClassId(u32);
pub type Id = EClassId;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct OpId(u32);

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Expr<Id> {
    Var(String),
    Const(i32),
    Op2(OpId, Id, Id),
}

static OP_STRINGS: &[&str] = &["+", "*"];

type ENode = Expr<EClassId>;

type VarMap = HashMap<String, Id>;

impl ENode {
    fn write_label(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Expr::Var(s) => write!(f, "'{}'", s),
            Expr::Const(i) => write!(f, "{}", i),
            Expr::Op2(op_id, _, _) => write!(f, "{}", OP_STRINGS[op_id.0 as usize]),
        }
    }

    fn update_ids(&self, uf: &mut UnionFind) -> ENode {
        match *self {
            Expr::Var(_) => self.clone(),
            Expr::Const(_) => self.clone(),
            Expr::Op2(op, l, r) => Expr::Op2(op, find(uf, l), find(uf, r)),
        }
    }

    fn fill_children(&self, vec: &mut Vec<EClassId>) {
        assert_eq!(vec.len(), 0);
        match self {
            Expr::Var(_) => (),
            Expr::Const(_) => (),
            Expr::Op2(_op, l, r) => {
                vec.push(*l);
                vec.push(*r);
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct EGraph {
    nodes: HashMap<ENode, EClassId>,
    leaders: UnionFind,
    classes: HashMap<EClassId, Vec<ENode>>,
}

// helper function that doens't require mut on the whole egraph
pub fn find(uf: &mut UnionFind, id: EClassId) -> EClassId {
    EClassId(uf.find(id.0))
}

impl EGraph {
    fn check(&self) {
        assert_eq!(self.nodes.len(), self.leaders.len());

        // make sure the classes map contains exactly the unique leaders
        let sets = self.leaders.build_sets();

        assert_eq!(sets.len(), self.classes.len());
        for l in sets.keys() {
            let id = EClassId(*l);
            assert!(self.classes.contains_key(&id));
        }

        // make sure that total size of classes == all nodes
        let sum_classes = self.classes.values().map(|c| c.len()).sum();
        assert_eq!(self.nodes.len(), sum_classes);
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn add(&mut self, enode: ENode) -> Id {
        self.check();

        trace!("Adding       {:?}", enode);

        // make sure that the enodes children are already in the set
        if cfg!(debug_assertions) {
            let mut ids = Vec::new();
            enode.fill_children(&mut ids);
            for id in ids {
                assert!(id.0 < self.len() as u32);
            }
        }

        // hash cons
        let id = match self.nodes.get(&enode) {
            None => {
                let next_id = EClassId(self.leaders.make_set());
                trace!("Added  {:4}: {:?}", next_id.0, enode);
                self.classes.insert(next_id, vec![enode.clone()]);
                self.nodes.insert(enode, next_id);
                next_id
            }
            Some(id) => {
                trace!("Added *{:4}: {:?}", id.0, enode);
                *id
            }
        };

        self.check();
        id
    }

    pub fn just_find(&self, id: EClassId) -> EClassId {
        EClassId(self.leaders.just_find(id.0))
    }

    pub fn pattern_match_eclass(
        &mut self,
        pattern: &Pattern,
        eclass: EClassId,
    ) -> Vec<VarMap> {
        let start = &pattern.nodes[pattern.lhs.0 as usize];
        let initial_mapping = HashMap::new();
        let mappings =
            self.match_node_against_eclass(initial_mapping, pattern, eclass, start.clone());

        for m in &mappings {
            self.add_pattern(eclass, m, &pattern);
        }

        mappings
    }

    fn get_eclass(&self, eclass_id: Id) -> &[ENode] {
        self.classes
            .get(&eclass_id)
            .unwrap_or_else(|| panic!("Couldn't find eclass {:?}", eclass_id))
    }

    fn match_node_against_eclass(
        &self,
        mut var_mapping: VarMap,
        pattern: &Pattern,
        eclass: Id,
        pattern_node: ENode,
    ) -> Vec<VarMap> {
        if let Expr::Var(s) = pattern_node {
            match var_mapping.get(&s) {
                None => {
                    var_mapping.insert(s, eclass);
                }
                Some(&prev_mapped_eclass) => {
                    if eclass != prev_mapped_eclass {
                        return vec![];
                    }
                }
            }

            return vec![var_mapping];
        }

        let mut new_mappings = Vec::new();

        for class_node in self.get_eclass(eclass) {
            use Expr::*;
            match (&pattern_node, class_node) {
                (Var(_), _) => panic!("pattern isn't a var at this point"),
                (Op2(po, pl, pr), Op2(no, nl, nr)) if po == no => {
                    let left_mappings = self.match_node_against_eclass(
                        var_mapping.clone(),
                        pattern,
                        *nl,
                        pattern.nodes[pl.0 as usize].clone(),
                    );

                    for vm in left_mappings {
                        new_mappings.extend(self.match_node_against_eclass(
                            vm,
                            pattern,
                            *nr,
                            pattern.nodes[pr.0 as usize].clone(),
                        ))
                    }
                }
                _ => (),
            }
        }

        new_mappings
    }

    pub fn rebuild(&mut self) {
        // TODO don't copy so much
        let mut new_classes = HashMap::new();

        for (leader, class) in self.classes.iter() {
            let mut new_nodes = Vec::with_capacity(class.len());
            for node in class {
                new_nodes.push(node.update_ids(&mut self.leaders));
            }

            new_classes.insert(*leader, new_nodes);
        }
        self.classes = new_classes;

        self.nodes.clear();
        for (leader, class) in &self.classes {
            for node in class {
                self.nodes.insert(node.clone(), *leader);
            }
        }
    }

    pub fn union(&mut self, id1: Id, id2: Id) -> Id {
        self.check();

        trace!("Unioning {} and {}", id1.0, id2.0);

        let (from, to) = match self.leaders.union(id1.0, id2.0) {
            UnionResult::SameSet(leader) => return EClassId(leader),
            UnionResult::Unioned { from, to } => (EClassId(from), EClassId(to)),
        };

        // remove the smaller class, merging into the bigger class
        let from_class = self.classes.remove(&from).unwrap();
        let to_class = self.classes.remove(&to).unwrap();

        let mut new_nodes = Vec::with_capacity(from_class.len() + to_class.len());
        for node in from_class.into_iter().chain(to_class) {
            new_nodes.push(node.update_ids(&mut self.leaders));
        }

        self.classes.insert(to, new_nodes);

        self.check();
        trace!("Unioned {} -> {}", from.0, to.0);
        trace!("Leaders: {:?}", self.leaders);
        for (leader, class) in &self.classes {
            trace!("  {:?}: {:?}", leader, class);
        }
        to
    }

    fn add_pattern(
        &mut self,
        root_enode: EClassId,
        map: &HashMap<String, Id>,
        pattern: &Pattern,
    ) -> EClassId {
        let start = pattern.nodes[pattern.rhs.0 as usize].clone();
        let pattern_root = self.add_pattern_node(map, pattern, start);
        self.union(root_enode, pattern_root)
    }

    fn add_pattern_node(
        &mut self,
        map: &HashMap<String, Id>,
        pattern: &Pattern,
        node: ENode,
    ) -> EClassId {
        match node {
            Expr::Const(_) => self.add(node),
            Expr::Var(s) => map[&s],
            Expr::Op2(op, l, r) => {
                let ll = self.add_pattern_node(map, pattern, pattern.nodes[l.0 as usize].clone());
                let rr = self.add_pattern_node(map, pattern, pattern.nodes[r.0 as usize].clone());
                self.add(Expr::Op2(op, ll, rr))
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Pattern {
    nodes: Vec<ENode>,
    lhs: Id,
    rhs: Id,
}

#[cfg(test)]
fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
}

#[cfg(test)]
mod tests {

    use super::*;

    use maplit::hashmap;

    fn var(s: &str) -> ENode {
        Expr::Var(s.into())
    }

    fn mk_plus(l: EClassId, r: EClassId) -> ENode {
        Expr::Op2(OpId(0), l, r)
    }

    fn dot(egraph: &EGraph, name: &str) {
        use std::fs::File;
        use std::io::prelude::*;

        let dot = dot::Dot::new(&egraph);
        let mut file = File::create(format!("{}.dot", name)).unwrap();
        write!(file, "{}", dot).unwrap();
        info!("Writing {}.dot ...\n{}", name, dot);
    }

    #[test]
    fn simple_add() {
        crate::init_logger();
        let mut egraph = EGraph::default();

        let x = egraph.add(var("x"));
        let x2 = egraph.add(var("x"));
        let _plus = egraph.add(mk_plus(x, x2));

        let y = egraph.add(var("y"));

        egraph.union(x, y);
        egraph.rebuild();

        dot(&egraph, "foo");

        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn simple_match() {
        crate::init_logger();
        let mut egraph = EGraph::default();

        let x = egraph.add(var("x"));
        let y = egraph.add(var("y"));
        let plus = egraph.add(mk_plus(x, y));

        let z = egraph.add(var("z"));
        let w = egraph.add(var("w"));
        let plus2 = egraph.add(mk_plus(z, w));

        egraph.union(plus, plus2);
        egraph.rebuild();

        let commute_plus = Pattern {
            nodes: vec![
                var("a"),
                var("b"),
                mk_plus(EClassId(0), EClassId(1)),
                mk_plus(EClassId(1), EClassId(0)),
            ],
            lhs: EClassId(2),
            rhs: EClassId(3),
        };

        let mappings = egraph.pattern_match_eclass(&commute_plus, egraph.just_find(plus));
        egraph.rebuild();

        let expected_mappings = vec![
            hashmap! {"a".into() => x, "b".into() => y},
            hashmap! {"a".into() => z, "b".into() => w},
        ];

        // for now, I have to check mappings both ways
        if mappings != expected_mappings {
            let e0 = expected_mappings[0].clone();
            let e1 = expected_mappings[1].clone();
            assert_eq!(mappings, vec![e1, e0])
        }

        info!("Here are the mappings!");
        for m in &mappings {
            info!("mappings: {:?}", m);
        }

        dot(&egraph, "simple-match");
    }
}
