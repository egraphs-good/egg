use std::convert::TryFrom;

use log::*;

use crate::{
    machine, Applier, EGraph, ENode, Id, Language, Metadata, RecExpr, Searcher, Subst, Var,
};

/// A pattern that can function as either a [`Searcher`] or [`Applier`].
///
/// A [`Pattern`] is essentially a for-all quantified expression with
/// [`Var`]s as the variables (in the logical sense).
///
/// When creating a [`Rewrite`], the most common thing to use as either
/// the left hand side (the [`Searcher`]) or the right hand side
/// (the [`Applier`]) is a [`Pattern`].
///
/// As a [`Searcher`], a [`Pattern`] does the intuitive
/// thing.
/// Here is a somewhat verbose formal-ish statement:
/// Searching for a pattern in an egraph yields substitutions
/// ([`Subst`]s) _s_ such that, for any _s'_—where instead of
/// mapping a variables to an eclass as _s_ does, _s'_ maps
/// a variable to an arbitrary expression represented by that
/// eclass—_p[s']_ (the pattern under substitution _s'_) is also
/// represented by the egraph.
///
/// As an [`Applier`], a [`Pattern`] performs the given substitution
/// and adds the result to the [`EGraph`].
///
/// Importantly, [`Pattern`] implements [`FromStr`] if the
/// [`Language`] does.
/// This is probably how you'll create most [`Pattern`]s.
///
/// ```
/// use egg::*;
/// define_language! {
///     enum Math {
///         Num(i32),
///         Add = "+",
///     }
/// }
///
/// let mut egraph = EGraph::<Math, ()>::default();
/// let a11 = egraph.add_expr(&"(+ 1 1)".parse().unwrap());
/// let a22 = egraph.add_expr(&"(+ 2 2)".parse().unwrap());
///
/// // use Var syntax (leading question mark) to get a
/// // variable in the Pattern
/// let same_add: Pattern<Math> = "(+ ?a ?a)".parse().unwrap();
///
/// // This is the search method from the Searcher trait
/// let matches = same_add.search(&egraph);
/// let matched_eclasses: Vec<Id> = matches.iter().map(|m| m.eclass).collect();
/// assert_eq!(matched_eclasses, vec![a11, a22]);
/// ```
///
/// [`Pattern`]: struct.Pattern.html
/// [`Rewrite`]: struct.Rewrite.html
/// [`EGraph`]: struct.EGraph.html
/// [`Subst`]: struct.Subst.html
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
/// [`Var`]: struct.Var.html
/// [`Searcher`]: trait.Searcher.html
/// [`Applier`]: trait.Applier.html
/// [`Language`]: trait.Language.html
#[derive(Debug, PartialEq, Clone)]
pub struct Pattern<L> {
    ast: PatternAst<L>,
    program: machine::Program<L>,
}

#[derive(Debug, PartialEq, Clone)]
pub(crate) enum PatternAst<L> {
    #[doc(hidden)]
    ENode(Box<ENode<L, PatternAst<L>>>),
    #[doc(hidden)]
    Var(Var),
}

impl<L: Language> PatternAst<L> {
    pub(crate) fn compile(self) -> Pattern<L> {
        let program = machine::Program::compile_from_pat(&self);
        Pattern { ast: self, program }
    }
}

impl<L: Language> From<RecExpr<L>> for PatternAst<L> {
    fn from(e: RecExpr<L>) -> Self {
        PatternAst::ENode(e.as_ref().map_children(PatternAst::from).into())
    }
}

impl<L: Language> From<RecExpr<L>> for Pattern<L> {
    fn from(e: RecExpr<L>) -> Self {
        let ast = PatternAst::from(e);
        ast.compile()
    }
}

impl<L: Language> TryFrom<PatternAst<L>> for RecExpr<L> {
    type Error = String;
    fn try_from(ast: PatternAst<L>) -> Result<RecExpr<L>, String> {
        match ast {
            PatternAst::ENode(e) => {
                let rec_enode = e.map_children_result(RecExpr::try_from);
                Ok(rec_enode?.into())
            }
            PatternAst::Var(v) => {
                let msg = format!("Found variable {:?} instead of expr term", v);
                Err(msg)
            }
        }
    }
}

impl<L: Language> TryFrom<Pattern<L>> for RecExpr<L> {
    type Error = String;
    fn try_from(pat: Pattern<L>) -> Result<RecExpr<L>, String> {
        RecExpr::try_from(pat.ast)
    }
}

/// The result of searching a [`Searcher`] over one eclass.
///
/// Note that one [`SearchMatches`] can contain many found
/// substititions. So taking the length of a list of [`SearchMatches`]
/// tells you how many eclasses something was matched in, _not_ how
/// many matches were found total.
///
/// [`SearchMatches`]: struct.SearchMatches.html
/// [`Searcher`]: trait.Searcher.html
#[derive(Debug)]
pub struct SearchMatches {
    /// The eclass id that these matches were found in.
    pub eclass: Id,
    /// The matches themselves.
    pub substs: Vec<Subst>,
}

impl<L, M> Searcher<L, M> for Pattern<L>
where
    L: Language,
    M: Metadata<L>,
{
    fn search(&self, egraph: &EGraph<L, M>) -> Vec<SearchMatches> {
	match &self.ast {
	    PatternAst::ENode(e) => {
		if let Some(ids) = egraph.sigtoclasses.get(&(e.op.clone(), e.children.len())) {
		    ids.iter().filter_map(|id| self.search_eclass(egraph, *id))
			.collect()
		} else {
		    vec![]
		}
	    },
	    PatternAst::Var(v) => {
		egraph
		    .classes()
		    .filter_map(|e| self.search_eclass(egraph, e.id))
		    .collect()
	    }
	}
    }

    fn search_eclass(&self, egraph: &EGraph<L, M>, eclass: Id) -> Option<SearchMatches> {
        let substs = self.program.run(egraph, eclass);
        if substs.is_empty() {
            None
        } else {
            Some(SearchMatches { eclass, substs })
        }
    }
}

impl<L: Language, M: Metadata<L>> Applier<L, M> for Pattern<L> {
    fn apply_one(&self, egraph: &mut EGraph<L, M>, _: Id, subst: &Subst) -> Vec<Id> {
        apply_pat(&self.ast, egraph, subst)
    }
}

fn apply_pat<L: Language, M: Metadata<L>>(
    pat: &PatternAst<L>,
    egraph: &mut EGraph<L, M>,
    subst: &Subst,
) -> Vec<Id> {
    trace!("apply_rec {:2?} {:?}", pat, subst);

    let result = match &pat {
        PatternAst::Var(w) => vec![subst[&w]],
        PatternAst::ENode(e) => {
            let children = e
                .children
                .iter()
                .flat_map(|child| apply_pat(child, egraph, subst));
            let n = ENode::new(e.op.clone(), children);
            trace!("adding: {:?}", n);
            vec![egraph.add(n)]
        }
    };

    trace!("result: {:?}", result);
    result
}

#[cfg(test)]
mod tests {

    use crate::{enode as e, *};

    #[test]
    fn simple_match() {
        crate::init_logger();
        let mut egraph = EGraph::<String, ()>::default();

        let x = egraph.add(e!("x"));
        let y = egraph.add(e!("y"));
        let plus = egraph.add(e!("+", x, y));

        let z = egraph.add(e!("z"));
        let w = egraph.add(e!("w"));
        let plus2 = egraph.add(e!("+", z, w));

        egraph.union(plus, plus2);
        egraph.rebuild();

        let commute_plus = rewrite!(
            "commute_plus";
            "(+ ?a ?b)" => "(+ ?b ?a)"
        );

        let matches = commute_plus.search(&egraph);
        let n_matches: usize = matches.iter().map(|m| m.substs.len()).sum();
        assert_eq!(n_matches, 2, "matches is wrong: {:#?}", matches);

        let applications = commute_plus.apply(&mut egraph, &matches);
        egraph.rebuild();
        assert_eq!(applications.len(), 2);

        let actual_substs: Vec<Subst> = matches.iter().flat_map(|m| m.substs.clone()).collect();

        println!("Here are the substs!");
        for m in &actual_substs {
            println!("substs: {:?}", m);
        }

        egraph.dot().to_dot("target/simple-match.dot").unwrap();

        use crate::extract::{AstSize, Extractor};

        let mut ext = Extractor::new(&egraph, AstSize);
        let (_, best) = ext.find_best(2);
        eprintln!("Best: {:#?}", best);
    }
}
