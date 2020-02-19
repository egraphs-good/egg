use std::convert::TryFrom;

use itertools::Itertools;
use log::*;
use smallvec::{smallvec, SmallVec};

use crate::{Applier, EGraph, ENode, Id, Language, Metadata, RecExpr, Searcher, Subst, Var};

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
/// [`Pattern`]: enum.Pattern.html
/// [`Rewrite`]: struct.Rewrite.html
/// [`EGraph`]: struct.EGraph.html
/// [`Subst`]: struct.Subst.html
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
/// [`Var`]: struct.Var.html
/// [`Searcher`]: trait.Searcher.html
/// [`Applier`]: trait.Applier.html
/// [`Language`]: trait.Language.html
#[derive(Debug, PartialEq, Clone)]
#[non_exhaustive]
pub enum Pattern<L> {
    #[doc(hidden)]
    ENode(Box<ENode<L, Pattern<L>>>),
    #[doc(hidden)]
    Var(Var),
}

impl<L: Language> From<RecExpr<L>> for Pattern<L> {
    fn from(e: RecExpr<L>) -> Self {
        Pattern::ENode(e.as_ref().map_children(Pattern::from).into())
    }
}

impl<L: Language> TryFrom<Pattern<L>> for RecExpr<L> {
    type Error = String;
    fn try_from(pat: Pattern<L>) -> Result<RecExpr<L>, String> {
        match pat {
            Pattern::ENode(e) => {
                let rec_enode = e.map_children_result(RecExpr::try_from);
                Ok(rec_enode?.into())
            }
            Pattern::Var(v) => {
                let msg = format!("Found variable {:?} instead of expr term", v);
                Err(msg)
            }
        }
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
        egraph
            .classes()
            .filter_map(|e| self.search_eclass(egraph, e.id))
            .collect()
    }

    fn search_eclass(&self, egraph: &EGraph<L, M>, eclass: Id) -> Option<SearchMatches> {
        let substs = search_pat(self, 0, egraph, eclass);
        if substs.is_empty() {
            None
        } else {
            Some(SearchMatches {
                eclass,
                substs: substs.into_vec(),
            })
        }
    }
}

impl<L: Language, M: Metadata<L>> Applier<L, M> for Pattern<L> {
    fn apply_one(&self, egraph: &mut EGraph<L, M>, _: Id, subst: &Subst) -> Vec<Id> {
        apply_pat(self, egraph, subst)
    }
}

fn search_pat<L: Language, M>(
    pat: &Pattern<L>,
    depth: usize,
    egraph: &EGraph<L, M>,
    eclass: Id,
) -> SmallVec<[Subst; 1]> {
    let pat_expr = match pat {
        Pattern::Var(v) => return smallvec![Subst::singleton(v.clone(), eclass)],
        Pattern::ENode(e) => e,
    };

    let mut new_substs = SmallVec::new();

    if pat_expr.children.is_empty() {
        for e in egraph[eclass].iter() {
            if e.children.is_empty() && pat_expr.op == e.op {
                new_substs.push(Subst::default());
                break;
            }
        }
    } else {
        let p_len = pat_expr.children.len();
        let is_compatible = |e: &&ENode<L>| e.op == pat_expr.op && e.children.len() == p_len;

        for e in egraph[eclass].iter().filter(is_compatible) {
            let arg_substs: Vec<_> = pat_expr
                .children
                .iter()
                .zip(&e.children)
                .map(|(pa, ea)| search_pat(pa, depth + 1, egraph, *ea))
                .collect();

            'outer: for ms in arg_substs.iter().multi_cartesian_product() {
                let mut combined = ms[0].clone();
                for m in &ms[1..] {
                    for (w, id) in m.iter() {
                        if let Some(old_id) = combined.insert(w.clone(), id.clone()) {
                            if old_id != *id {
                                continue 'outer;
                            }
                        }
                    }
                }
                new_substs.push(combined)
            }
        }
    }

    trace!("new_subst for {:?}: {:?}", pat_expr, new_substs);
    new_substs
}

fn apply_pat<L: Language, M: Metadata<L>>(
    pat: &Pattern<L>,
    egraph: &mut EGraph<L, M>,
    subst: &Subst,
) -> Vec<Id> {
    trace!("apply_rec {:2?} {:?}", pat, subst);

    let result = match &pat {
        Pattern::Var(w) => vec![subst[&w]],
        Pattern::ENode(e) => {
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

    fn wc<L: Language>(name: &Var) -> Pattern<L> {
        Pattern::Var(name.clone())
    }

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

        let a: Var = "?a".parse().unwrap();
        let b: Var = "?b".parse().unwrap();

        let pat = |e| Pattern::ENode(Box::new(e));
        let commute_plus = rewrite!(
            "commute_plus";
            { pat(e!("+", wc(&a), wc(&b))) } =>
            { pat(e!("+", wc(&b), wc(&a))) }
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
