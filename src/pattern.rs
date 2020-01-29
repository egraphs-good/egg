use std::fmt;

use itertools::Itertools;
use log::*;
use smallvec::{smallvec, SmallVec};
use symbolic_expressions::Sexp;

use crate::{
    egraph::{AddResult, EGraph, Metadata},
    expr::{Expr, Id, Language, QuestionMarkName, RecExpr},
    rewrite::Applier,
};

#[derive(Debug, PartialEq, Clone)]
pub enum Pattern<L> {
    Expr(Box<Expr<L, Pattern<L>>>),
    Wildcard(QuestionMarkName, WildcardKind),
}

#[derive(Debug, PartialEq, Clone, Copy, Hash)]
pub enum WildcardKind {
    Single,
    ZeroOrMore,
}

impl<L: Language> Pattern<L> {
    pub fn from_expr(e: &RecExpr<L>) -> Self {
        Pattern::Expr(
            e.as_ref()
                .map_children(|child| Pattern::from_expr(&child))
                .into(),
        )
    }

    pub fn is_multi_wildcard(&self) -> bool {
        match self {
            Pattern::Wildcard(_, WildcardKind::ZeroOrMore) => true,
            _ => false,
        }
    }

    pub fn subst_and_find<M>(&self, egraph: &mut EGraph<L, M>, mapping: &WildMap) -> Id
    where
        M: Metadata<L>,
    {
        match self {
            Pattern::Wildcard(w, kind) => {
                assert_eq!(*kind, WildcardKind::Single);
                mapping.get(w, *kind).unwrap()[0]
            }
            Pattern::Expr(expr) => {
                let expr = expr.map_children(|pat| pat.subst_and_find(egraph, mapping));
                let result = egraph.add(expr);
                result.id
            }
        }
    }

    // pub(crate) fn insert_wildcards(&self, set: &mut IndexSet<QuestionMarkName>) {
    //     match self {
    //         Pattern::Wildcard(w, _) => {
    //             set.insert(w.clone());
    //         }
    //         Pattern::Expr(expr) => {
    //             expr.map_children(|pat| pat.insert_wildcards(set));
    //         }
    //     }
    // }

    // pub(crate) fn is_bound(&self, set: &IndexSet<QuestionMarkName>) -> bool {
    //     match self {
    //         Pattern::Wildcard(w, _) => set.contains(w),
    //         Pattern::Expr(e) => e.children.iter().all(|p| p.is_bound(set)),
    //     }
    // }
}

impl<L: Language + fmt::Display> Pattern<L> {
    pub fn to_sexp(&self) -> Sexp {
        match self {
            Pattern::Wildcard(w, _) => Sexp::String(w.to_string()),
            Pattern::Expr(e) => match e.children.len() {
                0 => Sexp::String(e.op.to_string()),
                _ => {
                    let mut vec: Vec<_> = e.children.iter().map(Self::to_sexp).collect();
                    vec.insert(0, Sexp::String(e.op.to_string()));
                    Sexp::List(vec)
                }
            },
        }
    }
}

impl<L: Language, M: Metadata<L>> Applier<L, M> for Pattern<L> {
    fn apply(&self, egraph: &mut EGraph<L, M>, mapping: &WildMap) -> Vec<AddResult> {
        trace!("apply_rec {:2?} {:?}", self, mapping);

        let result = match &self {
            Pattern::Wildcard(w, kind) => mapping
                .get(&w, *kind)
                .unwrap()
                .iter()
                .map(|&id| AddResult {
                    was_there: true,
                    id,
                })
                .collect(),
            Pattern::Expr(e) => {
                // use the `was_there` field to keep track if we
                // ever added anything to the egraph during this
                // application
                let mut everything_was_there = true;
                let children = e
                    .children
                    .iter()
                    .flat_map(|child| child.apply(egraph, mapping))
                    .map(|result| {
                        everything_was_there &= result.was_there;
                        result.id
                    })
                    .collect();
                let n = Expr::new(e.op.clone(), children);
                trace!("adding: {:?}", n);
                let mut op_add = egraph.add(n);
                op_add.was_there &= everything_was_there;
                vec![op_add]
            }
        };

        trace!("result: {:?}", result);
        result
    }
}

#[derive(Debug)]
pub struct EClassMatches {
    pub eclass: Id,
    pub mappings: Vec<WildMap>,
}

#[derive(Debug, Clone, PartialEq, Hash)]
pub struct WildMap {
    vec: SmallVec<[(QuestionMarkName, WildcardKind, Vec<Id>); 2]>,
}

impl Default for WildMap {
    fn default() -> Self {
        Self {
            vec: Default::default(),
        }
    }
}

impl WildMap {
    fn insert(&mut self, w: QuestionMarkName, kind: WildcardKind, ids: Vec<Id>) -> Option<&[Id]> {
        // HACK double get is annoying here but you need it for lifetime reasons
        if self.get(&w, kind).is_some() {
            self.get(&w, kind)
        } else {
            self.vec.push((w, kind, ids));
            None
        }
    }
    fn get(&self, w: &QuestionMarkName, kind: WildcardKind) -> Option<&[Id]> {
        for (w2, kind2, ids2) in &self.vec {
            if w == w2 {
                assert_eq!(kind, *kind2);
                return Some(&ids2);
            }
        }
        None
    }
}

impl<'a> std::ops::Index<&'a QuestionMarkName> for WildMap {
    type Output = [Id];
    fn index(&self, q: &QuestionMarkName) -> &Self::Output {
        for (w2, _kind, ids2) in &self.vec {
            if q == w2 {
                return &ids2;
            }
        }
        panic!("Didn't find wildcard {}", q)
    }
}

impl<L: Language> Pattern<L> {
    pub fn search<M>(&self, egraph: &EGraph<L, M>) -> Vec<EClassMatches> {
        egraph
            .classes()
            .filter_map(|e| self.search_eclass(egraph, e.id))
            .collect()
    }

    pub fn search_eclass<M>(&self, egraph: &EGraph<L, M>, eclass: Id) -> Option<EClassMatches> {
        let mappings = self.search_pat(0, egraph, eclass);
        if mappings.is_empty() {
            None
        } else {
            Some(EClassMatches {
                eclass,
                mappings: mappings.into_vec(),
            })
        }
    }

    fn search_pat<M>(
        &self,
        depth: usize,
        egraph: &EGraph<L, M>,
        eclass: Id,
    ) -> SmallVec<[WildMap; 1]> {
        let pat_expr = match self {
            Pattern::Wildcard(w, kind) => {
                assert_eq!(*kind, WildcardKind::Single);
                let mut var_mapping = WildMap::default();
                let was_there = var_mapping.insert(w.clone(), *kind, vec![eclass]);
                assert_eq!(was_there, None);

                return smallvec![var_mapping];
            }
            Pattern::Expr(e) => e,
        };

        let mut new_mappings = SmallVec::new();

        if pat_expr.children.is_empty() {
            for e in egraph[eclass].iter() {
                if e.children.is_empty() && pat_expr.op == e.op {
                    new_mappings.push(WildMap::default());
                    break;
                }
            }
        } else {
            for e in egraph[eclass].iter().filter(|e| e.op == pat_expr.op) {
                let n_multi = pat_expr
                    .children
                    .iter()
                    .filter(|p| p.is_multi_wildcard())
                    .count();
                let (range, multi_mapping) = if n_multi > 0 {
                    assert_eq!(n_multi, 1, "Patterns can only have one multi match");
                    let (position, q) = pat_expr
                        .children
                        .iter()
                        .enumerate()
                        .filter_map(|(i, p)| match p {
                            Pattern::Wildcard(q, WildcardKind::ZeroOrMore) => Some((i, q)),
                            Pattern::Wildcard(_, WildcardKind::Single) => None,
                            Pattern::Expr(_) => None,
                        })
                        .next()
                        .unwrap();
                    assert_eq!(
                        position,
                        pat_expr.children.len() - 1,
                        "Multi matches must be in the tail position for now"
                    );

                    // if the pattern is more than one longer, then we
                    // can't match the multi matcher
                    let len = pat_expr.children.len();
                    if len - 1 > e.children.len() {
                        continue;
                    }
                    let ids = e.children[len - 1..].to_vec();
                    (
                        (0..len - 1),
                        Some((q.clone(), WildcardKind::ZeroOrMore, ids)),
                    )
                } else {
                    let len = pat_expr.children.len();
                    if len != e.children.len() {
                        continue;
                    }
                    ((0..len), None)
                };

                let mut arg_mappings: Vec<_> = pat_expr.children[range]
                    .iter()
                    .zip(&e.children)
                    .map(|(pa, ea)| pa.search_pat(depth + 1, egraph, *ea))
                    .collect();

                if let Some((q, kind, ids)) = multi_mapping {
                    let mut m = WildMap::default();
                    m.vec.push((q, kind, ids));
                    arg_mappings.push(smallvec![m]);
                }

                'outer: for ms in arg_mappings.iter().multi_cartesian_product() {
                    let mut combined = ms[0].clone();
                    for m in &ms[1..] {
                        for (w, kind, ids) in &m.vec {
                            if let Some(old_ids) = combined.insert(w.clone(), *kind, ids.clone()) {
                                if old_ids != ids.as_slice() {
                                    continue 'outer;
                                }
                            }
                        }
                    }
                    new_mappings.push(combined)
                }
            }
        }

        trace!("new_mapping for {:?}: {:?}", pat_expr, new_mappings);
        new_mappings
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{
        expr::{
            tests::{op, var, TestLang},
            QuestionMarkName,
        },
        rewrite::rw,
    };

    fn wc<L: Language>(name: &QuestionMarkName) -> Pattern<L> {
        Pattern::Wildcard(name.clone(), WildcardKind::Single)
    }

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

        let commute_plus = rw("commute_plus")
            .with_pattern(Pattern::Expr(op("+", vec![wc(&a), wc(&b)])))
            .with_applier(Pattern::Expr(op("+", vec![wc(&b), wc(&a)])))
            .mk();

        let matches = commute_plus.search(&egraph);
        let n_matches: usize = matches.iter().map(|m| m.mappings.len()).sum();
        assert_eq!(n_matches, 2, "matches is wrong: {:#?}", matches);

        let applications = commute_plus.apply(&mut egraph, &matches);
        egraph.rebuild();
        assert_eq!(applications.len(), 2);

        let wm = |pairs: &[_]| WildMap { vec: pairs.into() };

        use WildcardKind::Single;
        let expected_mappings = vec![
            wm(&[(a.clone(), Single, vec![x]), (b.clone(), Single, vec![y])]),
            wm(&[(a.clone(), Single, vec![z]), (b.clone(), Single, vec![w])]),
        ];
        std::mem::drop((a, b));

        let actual_mappings: Vec<WildMap> =
            matches.iter().flat_map(|m| m.mappings.clone()).collect();

        // for now, I have to check mappings both ways
        if actual_mappings != expected_mappings {
            let e0 = expected_mappings[0].clone();
            let e1 = expected_mappings[1].clone();
            assert_eq!(actual_mappings, vec![e1, e0])
        }

        info!("Here are the mappings!");
        for m in &actual_mappings {
            info!("mappings: {:?}", m);
        }

        egraph.dump_dot("simple-match.dot");

        use crate::extract::{AstSize, Extractor};

        let mut ext = Extractor::new(&egraph, AstSize);
        let (_, best) = ext.find_best(2);
        eprintln!("Best: {:#?}", best);
    }
}
