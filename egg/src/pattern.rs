use std::fmt::Display;

use indexmap::IndexSet;
use instant::Instant;
use itertools::Itertools;
use log::*;
use smallvec::{smallvec, SmallVec};
use symbolic_expressions::Sexp;

use crate::{
    egraph::{AddResult, EGraph, Metadata},
    expr::{Expr, Id, Language, QuestionMarkName, RecExpr},
};

#[derive(Debug, PartialEq, Clone)]
pub enum Pattern<L: Language> {
    Expr(Box<Expr<L, Pattern<L>>>),
    Wildcard(QuestionMarkName, WildcardKind),
}

#[derive(Debug, PartialEq, Clone, Copy)]
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

    fn insert_wildcards(&self, set: &mut IndexSet<QuestionMarkName>) {
        match self {
            Pattern::Wildcard(w, kind) => {
                assert_eq!(*kind, WildcardKind::Single);
                set.insert(w.clone());
            }
            Pattern::Expr(expr) => {
                expr.map_children(|pat| pat.insert_wildcards(set));
            }
        }
    }

    fn is_bound(&self, set: &IndexSet<QuestionMarkName>) -> bool {
        match self {
            Pattern::Wildcard(w, kind) => {
                assert_eq!(*kind, WildcardKind::Single);
                set.contains(w)
            }
            Pattern::Expr(e) => e.children.iter().all(|p| p.is_bound(set)),
        }
    }
}

impl<L: Language + Display> Pattern<L> {
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

#[derive(Debug, PartialEq, Clone)]
pub struct Condition<L: Language> {
    pub lhs: Pattern<L>,
    pub rhs: Pattern<L>,
}

impl<L: Language> Condition<L> {
    fn check<M>(&self, egraph: &mut EGraph<L, M>, mapping: &WildMap) -> bool
    where
        M: Metadata<L>,
    {
        let lhs_id = self.lhs.subst_and_find(egraph, mapping);
        let rhs_id = self.rhs.subst_and_find(egraph, mapping);
        lhs_id == rhs_id
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Rewrite<L: Language> {
    pub name: String,
    pub lhs: Pattern<L>,
    pub rhs: Pattern<L>,
    pub conditions: Vec<Condition<L>>,
}

impl<L: Language> Rewrite<L> {
    pub fn is_bound(&self) -> bool {
        let mut bound = IndexSet::new();
        self.lhs.insert_wildcards(&mut bound);
        self.rhs.is_bound(&bound)
            && self
                .conditions
                .iter()
                .all(|cond| cond.lhs.is_bound(&bound) && cond.rhs.is_bound(&bound))
    }

    pub fn flip(&self) -> Self {
        // flip doesn't make sense for conditional rewrites
        assert_eq!(self.conditions, vec![]);
        Rewrite {
            name: format!("{}-flipped", self.name),
            lhs: self.rhs.clone(),
            rhs: self.lhs.clone(),
            conditions: self.conditions.clone(),
        }
    }

    pub fn run<M: Metadata<L>>(&self, egraph: &mut EGraph<L, M>) -> Vec<Id> {
        let start = Instant::now();

        let matches = self.search(egraph);
        debug!("Found rewrite {} {} times", self.name, matches.len());

        let ids = matches.apply_with_limit(egraph, std::usize::MAX);
        let elapsed = start.elapsed();
        debug!(
            "Applied rewrite {} {} times in {}.{:03}",
            self.name,
            ids.len(),
            elapsed.as_secs(),
            elapsed.subsec_millis()
        );

        ids
    }

    pub fn search<M>(&self, egraph: &EGraph<L, M>) -> RewriteMatches<L> {
        RewriteMatches {
            rewrite: self,
            matches: self.lhs.search(egraph),
        }
    }
}

#[derive(Debug)]
pub struct RewriteMatches<'a, L: Language> {
    pub rewrite: &'a Rewrite<L>,
    matches: Vec<PatternMatches>,
}

impl<'a, L: Language> RewriteMatches<'a, L> {
    pub fn is_empty(&self) -> bool {
        self.matches.iter().all(|m| m.mappings.is_empty())
    }

    pub fn len(&self) -> usize {
        self.matches.iter().map(|m| m.mappings.len()).sum()
    }

    pub fn apply_with_limit<M: Metadata<L>>(
        &self,
        egraph: &mut EGraph<L, M>,
        size_limit: usize,
    ) -> Vec<Id> {
        self.matches
            .iter()
            .flat_map(|m| {
                m.apply_conditionally_with_limit(
                    &self.rewrite.rhs,
                    egraph,
                    &self.rewrite.conditions,
                    size_limit,
                )
            })
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq)]
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

impl<L: Language> Pattern<L> {
    pub fn search<M>(&self, egraph: &EGraph<L, M>) -> Vec<PatternMatches> {
        egraph
            .classes()
            .filter_map(|class| self.search_eclass(egraph, class.id))
            .collect()
    }

    pub fn search_eclass<M>(&self, egraph: &EGraph<L, M>, eclass: Id) -> Option<PatternMatches> {
        let mappings = self.search_pat(0, egraph, eclass);
        if !mappings.is_empty() {
            let res = PatternMatches {
                eclass,
                mappings: mappings.into_vec(),
            };
            trace!("Found matches for {:?}: {:?}", self, res);
            Some(res)
        } else {
            None
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
                    println!("Found a multi {:?}", q);
                    println!("{:?}", pat_expr);
                    println!("{:?}", e);

                    // if the pattern is more than one longer, then we
                    // can't match the multi matcher
                    let len = pat_expr.children.len();
                    if len - 1 > e.children.len() {
                        continue;
                    }
                    let ids = e.children[len - 1..].to_vec();
                    println!("Binding to ids {:?}", ids);
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
                    // assert!(combined.get(q).is_none());
                    // combined.vec.push((q.clone(), *kind, ids.clone()));
                    // println!("{:?}", combined);
                    let mut m = WildMap::default();
                    m.vec.push((q, kind, ids));
                    arg_mappings.push(smallvec![m]);
                    println!("PUSHED to {:?}", arg_mappings);
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

#[derive(Debug)]
pub struct PatternMatches {
    pub eclass: Id,
    pub mappings: Vec<WildMap>,
}

impl PatternMatches {
    #[deprecated(
        since = "0.0.3",
        note = "This unconditionally applies match. Use the `Rewrite` api instead."
    )]
    pub fn apply<L: Language, M: Metadata<L>>(
        &self,
        pattern: &Pattern<L>,
        egraph: &mut EGraph<L, M>,
    ) -> Vec<Id> {
        let conditions = vec![];
        self.apply_conditionally_with_limit(pattern, egraph, &conditions, std::usize::MAX)
    }

    #[deprecated(
        since = "0.0.3",
        note = "This unconditionally applies match. Use the `Rewrite` api instead."
    )]
    pub fn apply_with_limit<L: Language, M: Metadata<L>>(
        &self,
        pattern: &Pattern<L>,
        egraph: &mut EGraph<L, M>,
        size_limit: usize,
    ) -> Vec<Id> {
        let conditions = vec![];
        self.apply_conditionally_with_limit(pattern, egraph, &conditions, size_limit)
    }

    fn apply_conditionally_with_limit<L: Language, M: Metadata<L>>(
        &self,
        pattern: &Pattern<L>,
        egraph: &mut EGraph<L, M>,
        conditions: &[Condition<L>],
        size_limit: usize,
    ) -> Vec<Id> {
        assert_ne!(self.mappings.len(), 0);
        let mut applications = Vec::new();
        for mapping in &self.mappings {
            let before_size = egraph.total_size();
            if before_size > size_limit {
                break;
            }

            if conditions.iter().all(|c| c.check(egraph, mapping)) {
                let result = self.apply_rec(0, pattern, egraph, mapping);
                assert_eq!(
                    result.len(),
                    1,
                    "There shouldn't be multi matches at the top level"
                );
                let pattern_root = &result[0];
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
        }
        applications
    }

    fn apply_rec<L: Language, M: Metadata<L>>(
        &self,
        depth: usize,
        pattern: &Pattern<L>,
        egraph: &mut EGraph<L, M>,
        mapping: &WildMap,
    ) -> Vec<AddResult> {
        trace!(
            "{}apply_rec {:2?} {:?}",
            "    ".repeat(depth),
            pattern,
            mapping
        );

        let result = match pattern {
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
                    .flat_map(|child| self.apply_rec(depth + 1, child, egraph, mapping))
                    .map(|result| {
                        everything_was_there &= result.was_there;
                        result.id
                    })
                    .collect();
                let n = Expr::new(e.op.clone(), children);
                // let n = e.clone().map_children(|arg| {
                //     let add = self.apply_rec(depth + 1, &arg, egraph, mapping);
                //     everything_was_there &= add.was_there;
                //     add.id
                // });
                trace!("{}adding: {:?}", "    ".repeat(depth), n);
                let mut op_add = egraph.add(n);
                op_add.was_there &= everything_was_there;
                vec![op_add]
            }
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

        let commute_plus = crate::pattern::Rewrite {
            name: "commute_plus".into(),
            lhs: Pattern::Expr(op("+", vec![wc(&a), wc(&b)])),
            rhs: Pattern::Expr(op("+", vec![wc(&b), wc(&a)])),
            conditions: vec![],
        };

        // let eclass = egraph.find(plus);
        let matches = commute_plus.search(&egraph);
        assert_eq!(matches.len(), 2);

        let applications = matches.apply_with_limit(&mut egraph, 1000);
        egraph.rebuild();
        assert_eq!(applications.len(), 2);

        let wm = |pairs: &[_]| WildMap { vec: pairs.into() };

        use WildcardKind::Single;
        let expected_mappings = vec![
            wm(&[(a.clone(), Single, vec![x]), (b.clone(), Single, vec![y])]),
            wm(&[(a.clone(), Single, vec![z]), (b.clone(), Single, vec![w])]),
        ];

        let actual_mappings: Vec<WildMap> = matches
            .matches
            .iter()
            .flat_map(|m| m.mappings.clone())
            .collect();

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

        use crate::extract::Extractor;

        let ext = Extractor::new(&egraph);

        let best = ext.find_best(2);
        eprintln!("Best: {:#?}", best.expr);
    }

    #[test]
    fn conditional_rewrite() {
        crate::init_logger();
        let mut egraph = EGraph::<TestLang, ()>::default();

        let x = egraph.add(var("x")).id;
        let y = egraph.add(var("2")).id;
        let mul = egraph.add(op("*", vec![x, y])).id;

        let true_pat = Pattern::Expr(op("TRUE", vec![]));
        let true_id = egraph.add(op("TRUE", vec![])).id;

        let a: QuestionMarkName = "?a".parse().unwrap();
        let b: QuestionMarkName = "?b".parse().unwrap();

        let mul_to_shift = crate::pattern::Rewrite {
            name: "mul_to_shift".into(),
            lhs: Pattern::Expr(op("*", vec![wc(&a), wc(&b)])),
            rhs: Pattern::Expr(op(
                ">>",
                vec![wc(&a), Pattern::Expr(op("log2", vec![wc(&b)]))],
            )),
            conditions: vec![Condition {
                lhs: Pattern::Expr(op("is-power2", vec![wc(&b)])),
                rhs: true_pat,
            }],
        };

        info!("rewrite shouldn't do anything yet");
        egraph.rebuild();
        let apps = mul_to_shift.run(&mut egraph);
        assert_eq!(apps, vec![]);

        info!("Add the needed equality");
        let two_ispow2 = egraph.add(op("is-power2", vec![y])).id;
        egraph.union(two_ispow2, true_id);

        info!("Should fire now");
        egraph.rebuild();
        let apps = mul_to_shift.run(&mut egraph);
        assert_eq!(apps, vec![mul]);
    }
}
