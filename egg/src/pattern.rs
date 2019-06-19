use log::*;
use std::time::Instant;

use itertools::Itertools;
use smallvec::{smallvec, SmallVec};
use symbolic_expressions::Sexp;

use crate::{
    egraph::{AddResult, EGraph, Metadata},
    expr::{Expr, Id, Language, RecExpr},
};

#[derive(Debug, PartialEq, Clone)]
pub enum Pattern<L: Language> {
    Expr(Expr<L, Pattern<L>>),
    Wildcard(L::Wildcard),
}

impl<L: Language> Pattern<L> {
    pub fn from_expr(e: &RecExpr<L>) -> Self {
        Pattern::Expr(e.as_ref().map_children(|child| Pattern::from_expr(&child)))
    }
}

impl<L: Language> Pattern<L>
where
    L::Wildcard: std::fmt::Display,
{
    pub fn to_sexp(&self) -> Sexp {
        match self {
            Pattern::Wildcard(w) => Sexp::String(w.to_string()),
            Pattern::Expr(e) => match e {
                Expr::Constant(c) => Sexp::String(c.to_string()),
                Expr::Variable(v) => Sexp::String(v.to_string()),
                Expr::Operator(op, args) => {
                    let mut vec: Vec<_> = args.iter().map(Self::to_sexp).collect();
                    vec.insert(0, Sexp::String(op.to_string()));
                    Sexp::List(vec)
                }
            },
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Rewrite<L: Language> {
    pub name: String,
    pub lhs: Pattern<L>,
    pub rhs: Pattern<L>,
}

impl<L: Language> Rewrite<L> {
    pub fn flip(&self) -> Self {
        Rewrite {
            name: format!("{}-flipped", self.name),
            lhs: self.rhs.clone(),
            rhs: self.lhs.clone(),
        }
    }

    pub fn run<M: Metadata<L>>(&self, egraph: &mut EGraph<L, M>) {
        debug!("Running rewrite '{}'", self.name);
        let matches = self.lhs.search(&egraph);
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

#[derive(Debug, Clone, PartialEq)]
pub struct WildMap<L: Language> {
    vec: SmallVec<[(L::Wildcard, Id); 2]>,
}

impl<L: Language> Default for WildMap<L> {
    fn default() -> Self {
        Self {
            vec: Default::default(),
        }
    }
}

impl<L: Language> WildMap<L> {
    fn insert(&mut self, w: L::Wildcard, id: Id) -> Option<Id> {
        if let Some(old) = self.get(&w) {
            return Some(old);
        }
        self.vec.push((w, id));
        None
    }

    fn get(&self, w: &L::Wildcard) -> Option<Id> {
        for (w2, id2) in &self.vec {
            if w == w2 {
                return Some(*id2);
            }
        }
        None
    }
}

impl<L: Language> Pattern<L> {
    pub fn search<M>(&self, egraph: &EGraph<L, M>) -> Vec<PatternMatches<L>> {
        egraph
            .classes()
            .filter_map(|class| self.search_eclass(egraph, class.id))
            .collect()
    }

    pub fn search_eclass<M>(&self, egraph: &EGraph<L, M>, eclass: Id) -> Option<PatternMatches<L>> {
        let mappings = self.search_pat(0, egraph, eclass);
        if !mappings.is_empty() {
            Some(PatternMatches {
                eclass,
                mappings: mappings.into_vec(),
            })
        } else {
            None
        }
    }

    fn search_pat<M>(
        &self,
        depth: usize,
        egraph: &EGraph<L, M>,
        eclass: Id,
    ) -> SmallVec<[WildMap<L>; 1]> {
        let pat_expr = match self {
            Pattern::Wildcard(w) => {
                let mut var_mapping = WildMap::default();
                let was_there = var_mapping.insert(w.clone(), eclass);
                assert_eq!(was_there, None);

                return smallvec![var_mapping];
            }
            Pattern::Expr(e) => e,
        };

        let mut new_mappings = SmallVec::new();

        use Expr::*;
        match pat_expr {
            Variable(pv) => {
                for e in egraph[eclass].iter() {
                    if let Variable(ev) = e {
                        if ev == pv {
                            new_mappings.push(WildMap::default());
                            break;
                        }
                    }
                }
            }
            Constant(pc) => {
                for e in egraph[eclass].iter() {
                    if let Constant(ec) = e {
                        if ec == pc {
                            new_mappings.push(WildMap::default());
                            break;
                        }
                    }
                }
            }
            Operator(po, pargs) => {
                for e in egraph[eclass].iter() {
                    if let Operator(eo, eargs) = e {
                        if po != eo {
                            continue;
                        }
                        if pat_expr.children().len() != e.children().len() {
                            warn!(
                                concat!(
                                    "Different length children in pattern and expr\n",
                                    "  exp: {:?}\n",
                                    "  pat: {:?}"
                                ),
                                pat_expr, e
                            );
                            continue;
                        }

                        let arg_mappings: Vec<_> = pargs
                            .iter()
                            .zip(eargs)
                            .map(|(pa, ea)| pa.search_pat(depth + 1, egraph, *ea))
                            .collect();

                        'outer: for ms in arg_mappings.iter().multi_cartesian_product() {
                            let mut combined = ms[0].clone();
                            for m in &ms[1..] {
                                for (w, id) in &m.vec {
                                    if let Some(old_id) = combined.insert(w.clone(), *id) {
                                        if old_id != *id {
                                            continue 'outer;
                                        }
                                    }
                                }
                            }
                            new_mappings.push(combined)
                        }
                    }
                }
            }
        }

        new_mappings
    }
}

#[derive(Debug)]
pub struct PatternMatches<L: Language> {
    pub eclass: Id,
    pub mappings: Vec<WildMap<L>>,
}

impl<L: Language> PatternMatches<L> {
    pub fn apply<M: Metadata<L>>(
        &self,
        pattern: &Pattern<L>,
        egraph: &mut EGraph<L, M>,
    ) -> Vec<Id> {
        self.apply_with_limit(pattern, egraph, std::usize::MAX)
    }

    pub fn apply_with_limit<M: Metadata<L>>(
        &self,
        pattern: &Pattern<L>,
        egraph: &mut EGraph<L, M>,
        size_limit: usize,
    ) -> Vec<Id> {
        assert_ne!(self.mappings.len(), 0);
        let mut applications = Vec::new();
        for mapping in &self.mappings {
            let before_size = egraph.total_size();
            if before_size > size_limit {
                break;
            }
            let pattern_root = self.apply_rec(0, pattern, egraph, mapping);
            let leader = egraph.union(self.eclass, pattern_root.id);
            if !pattern_root.was_there {
                applications.push(leader);
            } else {
                // if the pattern root `was_there`, then nothing
                // was actually done in this application (it was
                // already in the egraph), so we can check to make
                // sure the egraph isn't any bigger
                let after_size = egraph.total_size();
                assert_eq!(before_size, after_size);
            }
        }
        applications
    }

    fn apply_rec<M: Metadata<L>>(
        &self,
        depth: usize,
        pattern: &Pattern<L>,
        egraph: &mut EGraph<L, M>,
        mapping: &WildMap<L>,
    ) -> AddResult {
        trace!("{}apply_rec {:2?}", "    ".repeat(depth), pattern);

        let result = match pattern {
            Pattern::Wildcard(w) => AddResult {
                was_there: true,
                id: mapping.get(&w).unwrap(),
            },
            Pattern::Expr(e) => match e {
                Expr::Constant(c) => egraph.add(Expr::Constant(c.clone())),
                Expr::Variable(v) => egraph.add(Expr::Variable(v.clone())),
                Expr::Operator(_, _) => {
                    // use the `was_there` field to keep track if we
                    // ever added anything to the egraph during this
                    // application
                    let mut everything_was_there = true;
                    let n = e.clone().map_children(|arg| {
                        let add = self.apply_rec(depth + 1, &arg, egraph, mapping);
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

    use crate::expr::{
        tests::{op, var, TestLang},
        QuestionMarkName,
    };

    #[test]
    fn simple_match() {
        crate::init_logger();
        let mut egraph = EGraph::<TestLang, ()>::default();

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
            lhs: Pattern::Expr(op(
                "+",
                vec![Pattern::Wildcard(a.clone()), Pattern::Wildcard(b.clone())],
            )),
            rhs: Pattern::Expr(op(
                "+",
                vec![Pattern::Wildcard(b.clone()), Pattern::Wildcard(a.clone())],
            )),
        };

        let eclass = egraph.find(plus);
        let matches = commute_plus.lhs.search_eclass(&egraph, eclass).unwrap();
        assert_eq!(matches.mappings.len(), 2);

        let applications = matches.apply(&commute_plus.rhs, &mut egraph);
        egraph.rebuild();
        assert_eq!(applications.len(), 2);

        let wm = |pairs: &[_]| WildMap { vec: pairs.into() };

        let expected_mappings = vec![
            wm(&[(a.clone(), x), (b.clone(), y)]),
            wm(&[(a.clone(), z), (b.clone(), w)]),
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

        egraph.dump_dot("simple-match.dot");

        use crate::extract::Extractor;

        let ext = Extractor::new(&egraph);

        let best = ext.find_best(2);
        eprintln!("Best: {:#?}", best.expr);
    }
}
