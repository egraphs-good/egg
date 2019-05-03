use log::*;

use crate::{
    egraph::{AddResult, EGraph},
    expr::{Expr, Flat, FlatExpr, Id, Language},
    util::HashMap,
};

#[derive(Debug, PartialEq, Clone)]
pub enum Pattern<L: Language> {
    Expr(Expr<L, Id>),
    Wildcard(L::Wildcard),
}

pub type FlatPattern<L> = Flat<Pattern<L>>;

impl<L: Language> FlatPattern<L> {
    pub fn from_flat_expr(e: &FlatExpr<L>) -> Self {
        FlatPattern {
            root: e.root,
            nodes: e.nodes.iter().cloned().map(Pattern::Expr).collect(),
        }
    }

    pub fn search(&self, egraph: &EGraph<L>) -> Vec<PatternMatches<L>> {
        self.make_search_context(egraph).search()
    }

    pub fn search_eclass(&self, egraph: &EGraph<L>, eclass: Id) -> Option<PatternMatches<L>> {
        self.make_search_context(egraph).search_eclass(eclass)
    }

    pub fn make_search_context<'p, 'e>(
        &'p self,
        egraph: &'e EGraph<L>,
    ) -> PatternSearchContext<'p, 'e, L> {
        PatternSearchContext {
            pattern: self,
            egraph: egraph,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Rewrite<L: Language> {
    pub lhs: FlatPattern<L>,
    pub rhs: FlatPattern<L>,
}

impl<L: Language> Rewrite<L> {
    pub fn flip(&self) -> Self {
        Rewrite {
            lhs: self.rhs.clone(),
            rhs: self.lhs.clone(),
        }
    }

    pub fn run(&self, egraph: &mut EGraph<L>) {
        let ctx = self.lhs.make_search_context(&egraph);
        let matches = ctx.search();

        for m in matches {
            m.apply(&self.rhs, egraph);
        }

        egraph.rebuild();
    }
}

pub type WildMap<L> = HashMap<<L as Language>::Wildcard, Id>;

// TODO can probably get rid of this type
pub struct PatternSearchContext<'p, 'e, L: Language> {
    pattern: &'p FlatPattern<L>,
    egraph: &'e EGraph<L>,
}

impl<'p, 'e, L: Language> PatternSearchContext<'p, 'e, L> {
    pub fn search(&self) -> Vec<PatternMatches<L>> {
        self.egraph
            .classes
            .keys()
            .filter_map(|&eclass_id| self.search_eclass(eclass_id))
            .collect()
    }

    pub fn search_eclass(&self, eclass: Id) -> Option<PatternMatches<L>> {
        let initial_mapping = HashMap::default();
        let mappings = self.search_pat(initial_mapping, eclass, self.pattern.root);
        if mappings.len() > 0 {
            Some(PatternMatches {
                eclass: eclass,
                mappings: mappings,
            })
        } else {
            None
        }
    }

    fn search_pat(&self, mut var_mapping: WildMap<L>, eid: Id, pid: Id) -> Vec<WildMap<L>> {
        let pn = self.pattern.get_node(pid);

        let pn = match pn {
            Pattern::Wildcard(w) => {
                match var_mapping.get(&w) {
                    None => {
                        var_mapping.insert(w.clone(), eid);
                    }
                    Some(&prev_mapped_eclass) => {
                        if eid != prev_mapped_eclass {
                            return vec![];
                        }
                    }
                }

                return vec![var_mapping];
            }
            Pattern::Expr(e) => e,
        };

        let mut new_mappings = Vec::new();

        for en in self.egraph.get_eclass(eid) {
            use Expr::*;
            match (pn, en) {
                (Variable(pv), Variable(ev)) => {
                    if pv == ev {
                        new_mappings.push(var_mapping.clone())
                    }
                }
                (Constant(pc), Constant(ec)) => {
                    if pc == ec {
                        new_mappings.push(var_mapping.clone())
                    }
                }
                (Operator(po, pargs), Operator(eo, eargs)) => {
                    if po != eo {
                        continue;
                    }
                    assert_eq!(pn.children().len(), en.children().len());

                    let mut mappings1 = vec![];
                    let mut mappings2 = vec![var_mapping.clone()];

                    for (pa, ea) in pargs.into_iter().zip(eargs) {
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

pub struct PatternMatches<L: Language> {
    pub eclass: Id,
    pub mappings: Vec<WildMap<L>>,
}

impl<L: Language> PatternMatches<L> {
    pub fn apply(&self, pattern: &FlatPattern<L>, egraph: &mut EGraph<L>) -> Vec<Id> {
        assert_ne!(self.mappings.len(), 0);
        self.mappings
            .iter()
            .filter_map(|mapping| {
                let pattern_root = self.apply_rec(pattern, egraph, mapping, pattern.root);
                if !pattern_root.was_there {
                    Some(egraph.union(self.eclass, pattern_root.id))
                } else {
                    None
                }
            })
            .collect()
    }

    fn apply_rec(
        &self,
        pattern: &FlatPattern<L>,
        egraph: &mut EGraph<L>,
        mapping: &WildMap<L>,
        pid: Id,
    ) -> AddResult {
        let pattern_node = pattern.get_node(pid);

        trace!("apply_rec {:?}", pattern_node);

        match pattern_node {
            Pattern::Wildcard(w) => AddResult {
                was_there: true,
                id: mapping[&w],
            },
            Pattern::Expr(e) => match e {
                Expr::Constant(_) => egraph.add(e.clone()),
                Expr::Variable(_) => egraph.add(e.clone()),
                Expr::Operator(_, _) => {
                    let n = e
                        .clone()
                        .map_children(|arg| self.apply_rec(pattern, egraph, mapping, arg).id);
                    egraph.add(n)
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::{
        expr::{
            tests::{op, var},
            QuestionMarkName,
        },
        util::hashmap,
    };

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

        let a: QuestionMarkName = "?a".parse().unwrap();
        let b: QuestionMarkName = "?b".parse().unwrap();

        let commute_plus = crate::pattern::Rewrite {
            lhs: FlatPattern {
                root: 0,
                nodes: vec![
                    Pattern::Expr(op("+", vec![1, 2])),
                    Pattern::Wildcard(a.clone()),
                    Pattern::Wildcard(b.clone()),
                ],
            },
            rhs: FlatPattern {
                root: 0,
                nodes: vec![
                    Pattern::Expr(op("+", vec![1, 2])),
                    Pattern::Wildcard(b.clone()),
                    Pattern::Wildcard(a.clone()),
                ],
            },
        };

        let eclass = egraph.just_find(plus);
        let matches = commute_plus.lhs.search_eclass(&egraph, eclass).unwrap();
        assert_eq!(matches.mappings.len(), 2);

        let applications = matches.apply(&commute_plus.rhs, &mut egraph);
        egraph.rebuild();
        assert_eq!(applications.len(), 2);

        let expected_mappings = vec![hashmap(&[(&a, x), (&b, y)]), hashmap(&[(&a, z), (&b, w)])];

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

        use crate::extract::Extractor;

        let ext = Extractor::new(&egraph);

        let best = ext.find_best(2);
        eprintln!("Best: {:#?}", best);
    }
}
