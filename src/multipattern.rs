use std::str::FromStr;
use thiserror::Error;

use crate::*;

pub struct MultiPattern<L> {
    asts: Vec<(Var, PatternAst<L>)>,
    program: machine::Program<L>,
}

impl<L: Language> MultiPattern<L> {
    pub fn new(asts: Vec<(Var, PatternAst<L>)>) -> Self {
        let program = machine::Program::compile_from_multi_pat(&asts);
        Self { asts, program }
    }
}

#[derive(Debug, Error)]
pub enum MultiPatternParseError<E> {
    #[error(transparent)]
    PatternParseError(E),
    PatternAssignmentError(String),
    VariableError(<Var as FromStr>::Err),
}

impl<L: Language + FromOp> FromStr for MultiPattern<L> {
    type Err = MultiPatternParseError<<PatternAst<L> as FromStr>::Err>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use MultiPatternParseError::*;
        let mut asts = vec![];
        for split in s.trim().split(',') {
            let split = split.trim();
            if split.is_empty() {
                continue;
            }
            let mut parts = split.split('=');
            let vs: &str = parts
                .next()
                .ok_or_else(|| PatternAssignmentError(split.into()))?;
            let v: Var = vs.trim().parse().map_err(VariableError)?;
            let ps = parts
                .map(|p| p.trim().parse())
                .collect::<Result<Vec<PatternAst<L>>, _>>()
                .map_err(PatternParseError)?;
            if ps.is_empty() {
                return Err(PatternAssignmentError(split.into()));
            }
            asts.extend(ps.into_iter().map(|p| (v, p)))
        }
        Ok(MultiPattern::new(asts))
    }
}

impl<L: Language, A: Analysis<L>> Searcher<L, A> for MultiPattern<L> {
    fn search_eclass(&self, egraph: &EGraph<L, A>, eclass: Id) -> Option<SearchMatches<L>> {
        let substs = self.program.run(egraph, eclass);
        if substs.is_empty() {
            None
        } else {
            Some(SearchMatches {
                eclass,
                substs,
                ast: None,
            })
        }
    }

    fn vars(&self) -> Vec<Var> {
        let mut vars = vec![];
        for (v, pat) in &self.asts {
            vars.push(*v);
            for n in pat.as_ref() {
                if let ENodeOrVar::Var(v) = n {
                    vars.push(*v)
                }
            }
        }
        vars.sort();
        vars.dedup();
        vars
    }
}

impl<L: Language, A: Analysis<L>> Applier<L, A> for MultiPattern<L> {
    fn apply_one(
        &self,
        _egraph: &mut EGraph<L, A>,
        _eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<L>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        panic!("Multipatterns do not support apply_one")
    }

    fn apply_matches(
        &self,
        egraph: &mut EGraph<L, A>,
        matches: &[SearchMatches<L>],
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // TODO explanations?
        // the ids returned are kinda garbage
        let mut added = vec![];
        for mat in matches {
            for subst in &mat.substs {
                let mut id_buf = vec![];
                for (i, (v, p)) in self.asts.iter().enumerate() {
                    id_buf.resize(p.as_ref().len(), 0.into());
                    let id1 = crate::pattern::apply_pat(&mut id_buf, p.as_ref(), egraph, subst);
                    let id2 = subst[*v];
                    egraph.union(id1, id2);
                    if i == 0 {
                        added.push(id1)
                    }
                }
            }
        }
        added
    }

    fn vars(&self) -> Vec<Var> {
        let mut vars = vec![];
        // TODO are unbound binding vars allowed?
        for (_v, pat) in &self.asts {
            for n in pat.as_ref() {
                if let ENodeOrVar::Var(v) = n {
                    vars.push(*v)
                }
            }
        }
        vars.sort();
        vars.dedup();
        vars
    }
}

#[cfg(test)]
mod tests {
    use crate::{SymbolLang as S, *};

    type EGraph = crate::EGraph<S, ()>;

    #[test]
    fn multi_patterns() {
        crate::init_logger();
        let mut egraph = EGraph::default();
        let _ = egraph.add_expr(&"(f a a)".parse().unwrap());
        let ab = egraph.add_expr(&"(f a b)".parse().unwrap());
        let ac = egraph.add_expr(&"(f a c)".parse().unwrap());
        egraph.union(ab, ac);
        egraph.rebuild();

        let n_matches = |multipattern: &str| -> usize {
            let mp: MultiPattern<S> = multipattern.parse().unwrap();
            mp.n_matches(&egraph)
        };

        assert_eq!(n_matches("?x = (f a a),   ?y = (f ?c b)"), 1);
        assert_eq!(n_matches("?x = (f a a),   ?y = (f a b)"), 1);
        assert_eq!(n_matches("?x = (f a a),   ?y = (f a a)"), 1);
        assert_eq!(n_matches("?x = (f ?a ?b), ?y = (f ?c ?d)"), 9);
        assert_eq!(n_matches("?x = (f ?a a),  ?y = (f ?a b)"), 1);

        assert_eq!(n_matches("?x = (f a a), ?x = (f a c)"), 0);
        assert_eq!(n_matches("?x = (f a b), ?x = (f a c)"), 1);
    }
}
