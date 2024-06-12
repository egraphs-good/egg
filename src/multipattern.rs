use std::str::FromStr;
use thiserror::Error;

use crate::*;

/// A set of open expressions bound to variables.
///
/// Multipatterns bind many expressions to variables,
/// allowing for simultaneous searching or application of many terms
/// constrained to the same substitution.
///
/// Multipatterns are good for writing graph rewrites or datalog-style rules.
///
/// You can create multipatterns via the [`MultiPattern::new`] function or the
/// [`multi_rewrite!`] macro.
///
/// [`MultiPattern`] implements both [`Searcher`] and [`Applier`].
/// When searching a multipattern, the result ensures that
/// patterns bound to the same variable are equivalent.
/// When applying a multipattern, patterns bound a variable occuring in the
/// searcher are unioned with that e-class.
///
/// Multipatterns currently do not support the explanations feature.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct MultiPattern<L> {
    asts: Vec<(Var, PatternAst<L>)>,
    program: machine::Program<L>,
}

impl<L: Language> MultiPattern<L> {
    /// Creates a new multipattern, binding the given patterns to the corresponding variables.
    ///
    /// ```
    /// use egg::*;
    ///
    /// let mut egraph = EGraph::<SymbolLang, ()>::default();
    /// egraph.add_expr(&"(f a a)".parse().unwrap());
    /// egraph.add_expr(&"(f a b)".parse().unwrap());
    /// egraph.add_expr(&"(g a a)".parse().unwrap());
    /// egraph.add_expr(&"(g a b)".parse().unwrap());
    /// egraph.rebuild();
    ///
    /// let f_pat: PatternAst<SymbolLang> = "(f ?x ?y)".parse().unwrap();
    /// let g_pat: PatternAst<SymbolLang> = "(g ?x ?y)".parse().unwrap();
    /// let v1: Var = "?v1".parse().unwrap();
    /// let v2: Var = "?v2".parse().unwrap();
    ///
    /// let multipattern = MultiPattern::new(vec![(v1, f_pat), (v2, g_pat)]);
    /// // you can also parse multipatterns
    /// assert_eq!(multipattern, "?v1 = (f ?x ?y), ?v2 = (g ?x ?y)".parse().unwrap());
    ///
    /// assert_eq!(multipattern.n_matches(&egraph), 2);
    /// ```
    pub fn new(asts: Vec<(Var, PatternAst<L>)>) -> Self {
        let program = machine::Program::compile_from_multi_pat(&asts);
        Self { asts, program }
    }
}

#[derive(Debug, Error)]
/// An error raised when parsing a [`MultiPattern`]
pub enum MultiPatternParseError<E> {
    /// One of the patterns in the multipattern failed to parse.
    #[error(transparent)]
    PatternParseError(E),
    /// One of the clauses in the multipattern wasn't of the form `?var (= pattern)+`.
    #[error("Bad clause in the multipattern: {0}")]
    PatternAssignmentError(String),
    /// One of the variables failed to parse.
    #[error(transparent)]
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
    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<L, A>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<L>> {
        match self.asts.as_slice() {
            [] => panic!("empty multipattern"),
            [(_var, pat), ..] => {
                if let [ENodeOrVar::Var(_)] = pat.as_ref() {
                    panic!(
                        "Bare cannot be first pattern variable in multipattern: {:?}",
                        self.asts
                    )
                }
            }
        }
        let substs = self.program.run_with_limit(egraph, eclass, limit);
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
                let mut subst = subst.clone();
                let mut id_buf = vec![];
                for (i, (v, p)) in self.asts.iter().enumerate() {
                    id_buf.resize(p.as_ref().len(), 0.into());
                    let id1 = crate::pattern::apply_pat(&mut id_buf, p.as_ref(), egraph, &subst);
                    if let Some(id2) = subst.insert(*v, id1) {
                        egraph.union(id1, id2);
                    }
                    if i == 0 {
                        added.push(id1)
                    }
                }
            }
        }
        added
    }

    fn vars(&self) -> Vec<Var> {
        let mut bound_vars = HashSet::default();
        let mut vars = vec![];
        for (bv, pat) in &self.asts {
            for n in pat.as_ref() {
                if let ENodeOrVar::Var(v) = n {
                    // using vars that are already bound doesn't count
                    if !bound_vars.contains(v) {
                        vars.push(*v)
                    }
                }
            }
            bound_vars.insert(bv);
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

    impl EGraph {
        fn add_string(&mut self, s: &str) -> Id {
            self.add_expr(&s.parse().unwrap())
        }
    }

    #[test]
    #[should_panic = "unbound var ?z"]
    fn bad_unbound_var() {
        let _: Rewrite<S, ()> = multi_rewrite!("foo"; "?x = (foo ?y)" => "?x = ?z");
    }

    #[test]
    fn ok_unbound_var() {
        let _: Rewrite<S, ()> = multi_rewrite!("foo"; "?x = (foo ?y)" => "?z = (baz ?y), ?x = ?z");
    }

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

    #[test]
    fn unbound_rhs() {
        let mut egraph = EGraph::default();
        let _x = egraph.add_expr(&"(x)".parse().unwrap());
        let rules = vec![
            // Rule creates y and z if they don't exist.
            multi_rewrite!("rule1"; "?x = (x)" => "?y = (y), ?y = (z)"),
            // Can't fire without above rule. `y` and `z` don't already exist in egraph
            multi_rewrite!("rule2"; "?x = (x), ?y = (y), ?z = (z)" => "?y = (y), ?y = (z)"),
        ];
        let mut runner = Runner::default().with_egraph(egraph).run(&rules);
        let y = runner.egraph.add_expr(&"(y)".parse().unwrap());
        let z = runner.egraph.add_expr(&"(z)".parse().unwrap());
        assert_eq!(runner.egraph.find(y), runner.egraph.find(z));
    }

    #[test]
    fn ctx_transfer() {
        let mut egraph = EGraph::default();
        egraph.add_string("(lte ctx1 ctx2)");
        egraph.add_string("(lte ctx2 ctx2)");
        egraph.add_string("(lte ctx1 ctx1)");
        let x2 = egraph.add_string("(tag x ctx2)");
        let y2 = egraph.add_string("(tag y ctx2)");
        let z2 = egraph.add_string("(tag z ctx2)");

        let x1 = egraph.add_string("(tag x ctx1)");
        let y1 = egraph.add_string("(tag y ctx1)");
        let z1 = egraph.add_string("(tag z ctx2)");
        egraph.union(x1, y1);
        egraph.union(y2, z2);
        let rules = vec![multi_rewrite!("context-transfer"; 
                     "?x = (tag ?a ?ctx1) = (tag ?b ?ctx1), 
                      ?t = (lte ?ctx1 ?ctx2), 
                      ?a1 = (tag ?a ?ctx2), 
                      ?b1 = (tag ?b ?ctx2)" 
                      =>
                      "?a1 = ?b1")];
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        assert_eq!(runner.egraph.find(x1), runner.egraph.find(y1));
        assert_eq!(runner.egraph.find(y2), runner.egraph.find(z2));

        assert_eq!(runner.egraph.find(x2), runner.egraph.find(y2));
        assert_eq!(runner.egraph.find(x2), runner.egraph.find(z2));

        assert_ne!(runner.egraph.find(y1), runner.egraph.find(z1));
        assert_ne!(runner.egraph.find(x1), runner.egraph.find(z1));
    }

    #[test]
    fn bare_var() {
        let mut g = EGraph::default();

        g.add_expr(&"(f a)".parse().unwrap());
        g.rebuild();

        let p: MultiPattern<S> = "?a = (f ?x), ?y = ?y".parse().unwrap();
        let rw = multi_rewrite!("r"; { p } => "?a = (g ?x ?y)");
        rw.run(&mut g);
    }
}
