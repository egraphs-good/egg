use std::collections::HashMap;

use crate::{AddResult, EGraph, ENode, Expr, Id};

#[derive(Debug, PartialEq)]
pub struct Pattern {
    // TODO make these private
    pub nodes: Vec<ENode>,
    pub lhs: Id,
    pub rhs: Id,
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
        egraph
            .classes
            .keys()
            .filter_map(|eclass| ctx.search_eclass(*eclass))
            .collect()
    }

    fn get_node(&self, id: Id) -> ENode {
        self.nodes[id.0 as usize].clone()
    }
}

pub type VarMap = HashMap<String, Id>;

pub struct PatternSearchContext<'p, 'e> {
    pattern: &'p Pattern,
    egraph: &'e EGraph,
}

impl<'p, 'e> PatternSearchContext<'p, 'e> {
    pub fn search_eclass(&self, eclass: Id) -> Option<PatternMatches<'p>> {
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

    fn search_pat(&self, mut var_mapping: VarMap, eid: Id, pid: Id) -> Vec<VarMap> {
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
                (Op2(po, pl, pr), Op2(eo, el, er)) if po == eo => {
                    let left_mappings = self.search_pat(var_mapping.clone(), *el, *pl);

                    for vm in left_mappings {
                        new_mappings.extend(self.search_pat(vm, *er, *pr))
                    }
                }
                _ => (),
            }
        }

        new_mappings
    }
}

pub struct PatternMatches<'p> {
    pub pattern: &'p Pattern,
    pub eclass: Id,
    pub mappings: Vec<VarMap>,
}

impl<'p> PatternMatches<'p> {
    pub fn apply(&self, egraph: &mut EGraph) -> Vec<Id> {
        self.mappings
            .iter()
            .filter_map(|mapping| {
                let pattern_root = self.apply_rec(egraph, mapping, self.pattern.lhs);
                if pattern_root.was_there {
                    Some(egraph.union(self.eclass, pattern_root.id))
                } else {
                    None
                }
            })
            .collect()
    }

    fn apply_rec(&self, egraph: &mut EGraph, mapping: &VarMap, pid: Id) -> AddResult {
        let pattern_node = self.pattern.get_node(pid);
        match pattern_node {
            Expr::Const(_) => egraph.add(pattern_node),
            Expr::Var(s) => AddResult {
                was_there: true,
                id: mapping[&s],
            },
            Expr::Op2(op, l, r) => {
                let ll = self.apply_rec(egraph, mapping, l);
                let rr = self.apply_rec(egraph, mapping, r);
                egraph.add(Expr::Op2(op, ll.id, rr.id))
            }
        }
    }
}
