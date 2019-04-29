use log::*;
use std::collections::HashMap;

use crate::{
    egraph::{AddResult, EGraph, Eid},
    expr::{Expr, VarId},
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Pid(pub u32);
pub type PNode = Expr<Pid>;

#[derive(Debug, PartialEq)]
pub struct Pattern {
    // TODO make these private
    pub nodes: Vec<PNode>,
    pub lhs: Pid,
    pub rhs: Pid,
}

impl Pattern {
    pub fn make_search_context<'p, 'e>(
        &'p self,
        egraph: &'e EGraph,
    ) -> PatternSearchContext<'p, 'e> {
        PatternSearchContext {
            pattern: &self,
            egraph,
        }
    }

    pub fn match_against_egraph(&self, egraph: &EGraph) -> Vec<PatternMatches> {
        let ctx = self.make_search_context(egraph);
        let matches: Vec<_> = egraph
            .classes
            .keys()
            .filter_map(|eclass| ctx.search_eclass(*eclass))
            .collect();
        info!("Found {} matches", matches.len());
        matches
    }

    fn get_node(&self, id: Pid) -> PNode {
        self.nodes[id.0 as usize].clone()
    }
}

pub type VarMap = HashMap<VarId, Eid>;

pub struct PatternSearchContext<'p, 'e> {
    pattern: &'p Pattern,
    egraph: &'e EGraph,
}

impl<'p, 'e> PatternSearchContext<'p, 'e> {
    pub fn search_eclass(&self, eclass: Eid) -> Option<PatternMatches<'p>> {
        let initial_mapping = HashMap::new();
        let mappings = self.search_pat(initial_mapping, eclass, self.pattern.lhs);
        if mappings.len() > 0 {
            Some(PatternMatches {
                pattern: self.pattern,
                eclass: eclass,
                mappings: mappings,
            })
        } else {
            None
        }
    }

    fn search_pat(&self, mut var_mapping: VarMap, eid: Eid, pid: Pid) -> Vec<VarMap> {
        let pattern_node = self.pattern.get_node(pid);

        if let Expr::Var(s) = pattern_node {
            match var_mapping.get(&s) {
                None => {
                    var_mapping.insert(s, eid);
                }
                Some(&prev_mapped_eclass) => {
                    if eid != prev_mapped_eclass {
                        return vec![];
                    }
                }
            }

            return vec![var_mapping];
        }

        let mut new_mappings = Vec::new();

        for class_node in self.egraph.get_eclass(eid) {
            use Expr::*;
            match (&pattern_node, class_node) {
                (Var(_), _) => panic!("pattern isn't a var at this point"),
                (Op(po, pargs), Op(eo, eargs)) if po == eo => {
                    assert_eq!(pargs.len(), eargs.len());

                    let mut mappings1 = vec![];
                    let mut mappings2 = vec![var_mapping.clone()];

                    for (pa, ea) in pargs.iter().zip(eargs) {
                        std::mem::swap(&mut mappings1, &mut mappings2);
                        for m in mappings1.drain(..) {
                            mappings2.extend(self.search_pat(m, *ea, *pa));
                        }
                    }

                    new_mappings.extend(mappings2);
                }
                _ => (),
            }
        }

        new_mappings
    }
}

pub struct PatternMatches<'p> {
    pub pattern: &'p Pattern,
    pub eclass: Eid,
    pub mappings: Vec<VarMap>,
}

impl<'p> PatternMatches<'p> {
    pub fn apply(&self, egraph: &mut EGraph) -> Vec<Eid> {
        self.mappings
            .iter()
            .filter_map(|mapping| {
                let pattern_root = self.apply_rec(egraph, mapping, self.pattern.rhs);
                if !pattern_root.was_there {
                    Some(egraph.union(self.eclass, pattern_root.id))
                } else {
                    None
                }
            })
            .collect()
    }

    fn apply_rec(&self, egraph: &mut EGraph, mapping: &VarMap, pid: Pid) -> AddResult {
        let pattern_node = self.pattern.get_node(pid);
        match pattern_node {
            Expr::Const(_) => egraph.add(pattern_node.convert_atom()),
            Expr::Var(s) => AddResult {
                was_there: true,
                id: mapping[&s],
            },
            Expr::Op(op, args) => {
                let args2 = args
                    .iter()
                    .map(|a| self.apply_rec(egraph, mapping, *a).id)
                    .collect();
                egraph.add(Expr::Op(op, args2))
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::{
        expr::{op, var, VarId},
        pattern::Pid,
    };

    use maplit::hashmap;

    #[test]
    fn simple_match() {
        crate::init_logger();
        let mut egraph = EGraph::default();

        let x = egraph.add(var(0)).id;
        let y = egraph.add(var(1)).id;
        let plus = egraph.add(op(0, vec![x, y])).id;

        let z = egraph.add(var(2)).id;
        let w = egraph.add(var(3)).id;
        let plus2 = egraph.add(op(0, vec![z, w])).id;

        egraph.union(plus, plus2);
        egraph.rebuild();

        let commute_plus = crate::pattern::Pattern {
            nodes: vec![
                var(0),
                var(1),
                op(0, vec![Pid(0), Pid(1)]),
                op(0, vec![Pid(1), Pid(0)]),
            ],
            lhs: Pid(2),
            rhs: Pid(3),
        };

        // explictly borrow to make sure that it doesn't mutate
        let match_ctx = commute_plus.make_search_context(&egraph);
        let matches = match_ctx.search_eclass((&egraph).just_find(plus)).unwrap();
        assert_eq!(matches.mappings.len(), 2);

        let applications = matches.apply(&mut egraph);
        egraph.rebuild();
        assert_eq!(applications.len(), 2);

        let expected_mappings = vec![
            hashmap! {VarId(0) => x, VarId(1) => y},
            hashmap! {VarId(0) => z, VarId(1) => w},
        ];

        // for now, I have to check mappings both ways
        if matches.mappings != expected_mappings {
            let e0 = expected_mappings[0].clone();
            let e1 = expected_mappings[1].clone();
            assert_eq!(matches.mappings, vec![e1, e0])
        }

        info!("Here are the mappings!");
        for m in &matches.mappings {
            info!("mappings: {:?}", m);
        }

        egraph.dot("simple-match.dot");
    }
}
