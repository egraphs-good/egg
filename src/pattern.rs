use std::collections::HashMap;

use crate::{EGraph, ENode, Expr, Id};

#[derive(Debug, PartialEq)]
pub struct Pattern {
    // TODO make these private
    pub nodes: Vec<ENode>,
    pub lhs: Id,
    pub rhs: Id,
}

impl Pattern {
    pub fn make_match_context<'p, 'e>(&'p self, egraph: &'e EGraph) -> PatternMatchContext<'p, 'e> {
        PatternMatchContext {
            pattern: &self,
            egraph,
        }
    }

    fn get_node(&self, id: Id) -> ENode {
        self.nodes[id.0 as usize].clone()
    }
}

pub type VarMap = HashMap<String, Id>;

pub struct PatternMatchContext<'p, 'e> {
    pattern: &'p Pattern,
    egraph: &'e EGraph,
}

impl<'a, 'b> PatternMatchContext<'a, 'b> {
    pub fn pattern_match_eclass(&self, eclass: Id) -> Vec<VarMap> {
        let initial_mapping = HashMap::new();
        self.match_node_against_eclass(initial_mapping, eclass, self.pattern.lhs)
    }

    fn match_node_against_eclass(&self, mut var_mapping: VarMap, eid: Id, pid: Id) -> Vec<VarMap> {
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
                    let left_mappings =
                        self.match_node_against_eclass(var_mapping.clone(), *el, *pl);

                    for vm in left_mappings {
                        new_mappings.extend(self.match_node_against_eclass(vm, *er, *pr))
                    }
                }
                _ => (),
            }
        }

        new_mappings
    }
}
