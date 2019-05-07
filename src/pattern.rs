use log::*;
use std::time::Instant;

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
    pub name: String,
    pub lhs: FlatPattern<L>,
    pub rhs: FlatPattern<L>,
}

impl<L: Language> Rewrite<L> {
    pub fn flip(&self) -> Self {
        Rewrite {
            name: format!("{}-flipped", self.name),
            lhs: self.rhs.clone(),
            rhs: self.lhs.clone(),
        }
    }

    pub fn run(&self, egraph: &mut EGraph<L>) {
        debug!("Running rewrite '{}'", self.name);
        let ctx = self.lhs.make_search_context(&egraph);
        let matches = ctx.search_with_name(&self.name);
        debug!(
            "Ran the rewrite '{}', found {} matches",
            self.name,
            matches.len()
        );

        let start = Instant::now();
        for m in matches {
            m.apply(&self.rhs, egraph);
        }
        let elapsed = start.elapsed();
        debug!(
            "Applied rewrite {} in {}.{:03}",
            self.name,
            elapsed.as_secs(),
            elapsed.subsec_millis()
        );
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

    pub fn search_with_name(&self, name: &str) -> Vec<PatternMatches<L>> {
        let mut skips = 0;
        let matches = self.egraph
            .classes
            .keys()
            .filter_map(|eclass_id| {
                let eclass = &self.egraph.classes[&eclass_id];
                if eclass.is_done(name) {
                    skips += 1;
                    None
                } else {
                    eclass.mark_as_done(name);
                    self.search_eclass(*eclass_id)
                }
            })
            .collect();
        if skips > 0 {
            warn!("Skipped searching {} eclasses", skips);
        }
        matches
    }

    pub fn search_eclass(&self, eclass: Id) -> Option<PatternMatches<L>> {
        let initial_mapping = HashMap::default();
        let mappings = self.search_pat(0, initial_mapping, eclass, self.pattern.root);
        if mappings.len() > 0 {
            Some(PatternMatches {
                eclass: eclass,
                mappings: mappings,
            })
        } else {
            None
        }
    }

    fn search_pat(
        &self,
        depth: usize,
        mut var_mapping: WildMap<L>,
        eid: Id,
        pid: Id,
    ) -> Vec<WildMap<L>> {
        let indent = "    ".repeat(depth);
        let pn = self.pattern.get_node(pid);

        trace!("{}search_pat {:2?} -> {}", indent, pn, eid);
        trace!("{} class: {:?}", indent, self.egraph.get_eclass(eid));

        let pn = match pn {
            Pattern::Wildcard(w) => {
                match var_mapping.get(&w) {
                    None => {
                        var_mapping.insert(w.clone(), eid);
                    }
                    Some(&prev_mapped_eclass) => {
                        if eid != prev_mapped_eclass {
                            trace!("{} Failed to bind wildcard {:?}", indent, w);
                            return vec![];
                        }
                    }
                }

                trace!("{} Bound wildcard {:?} to {}", indent, w, eid);
                return vec![var_mapping];
            }
            Pattern::Expr(e) => e,
        };

        let mut new_mappings = Vec::new();

        for en in self.egraph.get_eclass(eid).iter() {
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
                    if pn.children().len() != en.children().len() {
                        panic!(
                            concat!(
                                "Different length children in pattern and expr\n",
                                "  exp: {:?}\n",
                                "  pat: {:?}"
                            ),
                            en,
                            pn
                        );
                    }

                    let mut mappings1 = vec![];
                    let mut mappings2 = vec![var_mapping.clone()];

                    for (pa, ea) in pargs.into_iter().zip(eargs) {
                        std::mem::swap(&mut mappings1, &mut mappings2);
                        for m in mappings1.drain(..) {
                            mappings2.extend(self.search_pat(depth + 1, m, *ea, *pa));
                        }
                    }
                    new_mappings.extend(mappings2);
                }
                _ => (),
            }
        }

        trace!("{} Found {} mappings", indent, new_mappings.len());
        new_mappings
    }
}

#[derive(Debug)]
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
                let before_size = egraph.len();
                let pattern_root = self.apply_rec(0, pattern, egraph, mapping, pattern.root);
                let leader = egraph.union(self.eclass, pattern_root.id);
                if !pattern_root.was_there {
                    Some(leader)
                } else {
                    // if the pattern root `was_there`, then nothing
                    // was actually done in this application (it was
                    // already in the egraph), so we can check to make
                    // sure the egraph isn't any bigger
                    assert_eq!(before_size, egraph.len());
                    None
                }
            })
            .collect()
    }

    fn apply_rec(
        &self,
        depth: usize,
        pattern: &FlatPattern<L>,
        egraph: &mut EGraph<L>,
        mapping: &WildMap<L>,
        pid: Id,
    ) -> AddResult {
        let pattern_node = pattern.get_node(pid);

        trace!("{}apply_rec {:2?}", "    ".repeat(depth), pattern_node);

        let result = match pattern_node {
            Pattern::Wildcard(w) => AddResult {
                was_there: true,
                id: mapping[&w],
            },
            Pattern::Expr(e) => match e {
                Expr::Constant(_) => egraph.add(e.clone()),
                Expr::Variable(_) => egraph.add(e.clone()),
                Expr::Operator(_, _) => {
                    // use the `was_there` field to keep track if we
                    // ever added anything to the egraph during this
                    // application
                    let mut everything_was_there = true;
                    let n = e.clone().map_children(|arg| {
                        let add = self.apply_rec(depth + 1, pattern, egraph, mapping, arg);
                        everything_was_there &= add.was_there;
                        add.id
                    });
                    trace!("{}adding: {:?}", "    ".repeat(depth), n);
                    let mut op_add = egraph.add(n);
                    op_add.was_there &= everything_was_there;
                    op_add
                }
            },
        };

        trace!("{}result: {:?}", "    ".repeat(depth), result);
        result
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
            name: "commute_plus".into(),
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

        egraph.dump_dot("simple-match.dot");

        use crate::extract::Extractor;

        let ext = Extractor::new(&egraph);

        let best = ext.find_best(2);
        eprintln!("Best: {:#?}", best);
    }
}
