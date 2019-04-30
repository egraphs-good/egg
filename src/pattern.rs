use log::*;
use std::collections::HashMap;

use crate::{
    egraph::{AddResult, EGraph},
    expr::{Expr, Id, Node},
};

#[derive(Debug, PartialEq)]
pub struct Pattern<N> {
    pub lhs: Expr<N>,
    pub rhs: Expr<N>,
}

impl<N: Node> Pattern<N> {
    pub fn make_search_context<'p, 'e>(
        &'p self,
        egraph: &'e EGraph<N>,
    ) -> PatternSearchContext<'p, 'e, N> {
        PatternSearchContext {
            pattern: &self,
            egraph,
        }
    }

    pub fn match_against_egraph(&self, egraph: &EGraph<N>) -> Vec<PatternMatches<N>> {
        let ctx = self.make_search_context(egraph);
        let matches: Vec<_> = egraph
            .classes
            .keys()
            .filter_map(|eclass| ctx.search_eclass(*eclass))
            .collect();
        info!("Found {} matches", matches.len());
        matches
    }
}

pub type VarMap<N> = HashMap<<N as Node>::Variable, Id>;

pub struct PatternSearchContext<'p, 'e, N: Node> {
    pattern: &'p Pattern<N>,
    egraph: &'e EGraph<N>,
}

impl<'p, 'e, N: Node> PatternSearchContext<'p, 'e, N> {
    pub fn search_eclass(&self, eclass: Id) -> Option<PatternMatches<'p, N>> {
        let initial_mapping = HashMap::new();
        let mappings = self.search_pat(initial_mapping, eclass, self.pattern.lhs.root);
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

    fn search_pat(&self, mut var_mapping: VarMap<N>, eid: Id, pid: Id) -> Vec<VarMap<N>> {
        let pn = self.pattern.lhs.get_node(pid);

        if let Some(v) = pn.get_variable() {
            match var_mapping.get(&v) {
                None => {
                    var_mapping.insert(v.clone(), eid);
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

        for en in self.egraph.get_eclass(eid) {
            debug_assert_eq!(pn.get_variable(), None);

            if let (Some(pc), Some(ec)) = (pn.get_constant(), en.get_constant()) {
                if pc == ec {
                    new_mappings.push(var_mapping.clone())
                }
            }
            if let (Some(po), Some(eo)) = (pn.get_operator(), en.get_operator()) {
                if po != eo {
                    continue;
                }

                assert_eq!(pn.children().len(), en.children().len());

                let mut mappings1 = vec![];
                let mut mappings2 = vec![var_mapping.clone()];

                for (pa, ea) in pn.children().iter().zip(en.children()) {
                    std::mem::swap(&mut mappings1, &mut mappings2);
                    for m in mappings1.drain(..) {
                        mappings2.extend(self.search_pat(m, *ea, *pa));
                    }
                }

                new_mappings.extend(mappings2);
            }
        }

        new_mappings
    }
}

pub struct PatternMatches<'p, N: Node> {
    pub pattern: &'p Pattern<N>,
    pub eclass: Id,
    pub mappings: Vec<VarMap<N>>,
}

impl<'p, N: Node> PatternMatches<'p, N> {
    pub fn apply(&self, egraph: &mut EGraph<N>) -> Vec<Id> {
        self.mappings
            .iter()
            .filter_map(|mapping| {
                let pattern_root = self.apply_rec(egraph, mapping, self.pattern.rhs.root);
                if !pattern_root.was_there {
                    Some(egraph.union(self.eclass, pattern_root.id))
                } else {
                    None
                }
            })
            .collect()
    }

    fn apply_rec(&self, egraph: &mut EGraph<N>, mapping: &VarMap<N>, pid: Id) -> AddResult {
        let pattern_node = self.pattern.rhs.get_node(pid);

        if let Some(_) = pattern_node.get_constant() {
            egraph.add(pattern_node.clone())
        } else if let Some(v) = pattern_node.get_variable() {
            AddResult {
                was_there: true,
                id: mapping[v],
            }
        } else if let Some(_) = pattern_node.get_operator() {
            let n = pattern_node
                .clone()
                .map_children(|arg| self.apply_rec(egraph, mapping, arg).id);
            egraph.add(n)
        } else {
            unreachable!()
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::expr::{
        tests::{op, var},
        Expr,
    };

    use maplit::hashmap;

    #[test]
    fn simple_match() {
        crate::init_logger();
        let mut egraph = EGraph::default();

        let x = egraph.add(var("x")).id;
        let y = egraph.add(var("y")).id;
        let plus = egraph.add(op("+", vec![x, y])).id;

        let z = egraph.add(var("z")).id;
        let w = egraph.add(var("w")).id;
        let plus2 = egraph.add(op("+", vec![z, w])).id;

        egraph.union(plus, plus2);
        egraph.rebuild();

        let commute_plus = crate::pattern::Pattern {
            lhs: Expr {
                root: 0,
                nodes: vec![op("+", vec![1, 2]), var("a"), var("b")],
            },
            rhs: Expr {
                root: 0,
                nodes: vec![op("+", vec![1, 2]), var("b"), var("a")],
            },
        };

        // explictly borrow to make sure that it doesn't mutate
        let match_ctx = commute_plus.make_search_context(&egraph);
        let matches = match_ctx.search_eclass((&egraph).just_find(plus)).unwrap();
        assert_eq!(matches.mappings.len(), 2);

        let applications = matches.apply(&mut egraph);
        egraph.rebuild();
        assert_eq!(applications.len(), 2);

        let expected_mappings = vec![
            hashmap! {"a".into() => x, "b".into() => y},
            hashmap! {"a".into() => z, "b".into() => w},
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
