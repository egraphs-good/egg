use log::*;
use std::convert::TryFrom;
use std::fmt;

use crate::{machine, Analysis, Applier, EGraph, Id, Language, RecExpr, Searcher, Subst, Var};

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
///         "+" = Add([Id; 2]),
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
/// // Rebuild before searching
/// egraph.rebuild();
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
    /// The actual pattern as a [`RecExpr`](struct.RecExpr.html)
    pub ast: PatternAst<L>,
    program: machine::Program<L>,
}

/// A [`RecExpr`](struct.RecExpr.html) that represents a
/// [`Pattern`](struct.Pattern.html).
pub type PatternAst<L> = RecExpr<ENodeOrVar<L>>;

impl<L: Language> Pattern<L> {
    /// Returns a list of the [`Var`](struct.Var.html)s in this pattern.
    pub fn vars(&self) -> Vec<Var> {
        let mut vars = vec![];
        for n in self.ast.as_ref() {
            if let ENodeOrVar::Var(v) = n {
                if !vars.contains(v) {
                    vars.push(*v)
                }
            }
        }
        vars
    }

    /// Pretty print this pattern as a sexp with the given width
    pub fn pretty(&self, width: usize) -> String {
        self.ast.pretty(width)
    }
}

/// The language of [`Pattern`]s.
///
/// [`Pattern`]: struct.Pattern.html
#[derive(Debug, Hash, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum ENodeOrVar<L> {
    /// An enode from the underlying [`Language`](trait.Language.html)
    ENode(L),
    /// A pattern variable
    Var(Var),
}

impl<L: Language> Language for ENodeOrVar<L> {
    fn matches(&self, _other: &Self) -> bool {
        panic!("Should never call this")
    }

    fn children(&self) -> &[Id] {
        match self {
            ENodeOrVar::ENode(e) => e.children(),
            ENodeOrVar::Var(_) => &[],
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        match self {
            ENodeOrVar::ENode(e) => e.children_mut(),
            ENodeOrVar::Var(_) => &mut [],
        }
    }

    fn from_op_str(op_str: &str, children: Vec<Id>) -> Result<Self, String> {
        if op_str.starts_with('?') && op_str.len() > 1 {
            if children.is_empty() {
                op_str
                    .parse()
                    .map(ENodeOrVar::Var)
                    .map_err(|err| format!("Failed to parse var: {}", err))
            } else {
                Err(format!(
                    "Tried to parse pattern variable '{}' in the op position",
                    op_str
                ))
            }
        } else {
            L::from_op_str(op_str, children).map(ENodeOrVar::ENode)
        }
    }

    fn display_op(&self) -> &dyn std::fmt::Display {
        match self {
            ENodeOrVar::ENode(e) => e.display_op(),
            ENodeOrVar::Var(v) => v,
        }
    }
}

impl<L: Language> std::str::FromStr for Pattern<L> {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        PatternAst::from_str(s).map(Self::from)
    }
}

impl<'a, L: Language> From<&'a [L]> for Pattern<L> {
    fn from(expr: &'a [L]) -> Self {
        let nodes: Vec<_> = expr.iter().cloned().map(ENodeOrVar::ENode).collect();
        let ast = RecExpr::from(nodes);
        Self::from(ast)
    }
}

impl<'a, L: Language> From<PatternAst<L>> for Pattern<L> {
    fn from(ast: PatternAst<L>) -> Self {
        let program = machine::Program::compile_from_pat(&ast);
        Pattern { ast, program }
    }
}

impl<L: Language> TryFrom<Pattern<L>> for RecExpr<L> {
    type Error = Var;
    fn try_from(pat: Pattern<L>) -> Result<Self, Self::Error> {
        let nodes = pat.ast.as_ref().iter().cloned();
        let ns: Result<Vec<_>, _> = nodes
            .map(|n| match n {
                ENodeOrVar::ENode(n) => Ok(n),
                ENodeOrVar::Var(v) => Err(v),
            })
            .collect();
        ns.map(RecExpr::from)
    }
}

impl<L: Language> fmt::Display for Pattern<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.ast)
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

impl<L: Language, A: Analysis<L>> Searcher<L, A> for Pattern<L> {
    fn search(&self, egraph: &EGraph<L, A>) -> Vec<SearchMatches> {
        match self.ast.as_ref().last().unwrap() {
            ENodeOrVar::ENode(e) => {
                #[allow(clippy::mem_discriminant_non_enum)]
                let key = std::mem::discriminant(e);
                match egraph.classes_by_op.get(&key) {
                    None => vec![],
                    Some(ids) => ids
                        .iter()
                        .filter_map(|&id| self.search_eclass(egraph, id))
                        .collect(),
                }
            }
            ENodeOrVar::Var(_) => egraph
                .classes()
                .filter_map(|e| self.search_eclass(egraph, e.id))
                .collect(),
        }
    }

    fn search_eclass(&self, egraph: &EGraph<L, A>, eclass: Id) -> Option<SearchMatches> {
        let substs = self.program.run(egraph, eclass);
        if substs.is_empty() {
            None
        } else {
            Some(SearchMatches { eclass, substs })
        }
    }

    fn vars(&self) -> Vec<Var> {
        Pattern::vars(self)
    }
}

impl<L, A> Applier<L, A> for Pattern<L>
where
    L: Language,
    A: Analysis<L>,
{
    fn apply_one(&self, egraph: &mut EGraph<L, A>, _: Id, subst: &Subst) -> Vec<Id> {
        let id = apply_pat(self.ast.as_ref(), egraph, subst);
        vec![id]
    }

    fn vars(&self) -> Vec<Var> {
        Pattern::vars(self)
    }
}

fn apply_pat<L: Language, A: Analysis<L>>(
    pat: &[ENodeOrVar<L>],
    egraph: &mut EGraph<L, A>,
    subst: &Subst,
) -> Id {
    trace!("apply_rec {:2?} {:?}", pat, subst);

    let result = match pat.last().unwrap() {
        ENodeOrVar::Var(w) => subst[*w],
        ENodeOrVar::ENode(e) => {
            let n = e
                .clone()
                .map_children(|child| apply_pat(&pat[..usize::from(child) + 1], egraph, subst));
            trace!("adding: {:?}", n);
            egraph.add(n)
        }
    };

    trace!("result: {:?}", result);
    result
}

#[cfg(test)]
mod tests {

    use crate::{SymbolLang as S, *};

    type EGraph = crate::EGraph<S, ()>;

    #[test]
    fn simple_match() {
        crate::init_logger();
        let mut egraph = EGraph::default();

        let x = egraph.add(S::leaf("x"));
        let y = egraph.add(S::leaf("y"));
        let plus = egraph.add(S::new("+", vec![x, y]));

        let z = egraph.add(S::leaf("z"));
        let w = egraph.add(S::leaf("w"));
        let plus2 = egraph.add(S::new("+", vec![z, w]));

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
        let (_, best) = ext.find_best(plus);
        eprintln!("Best: {:#?}", best);
    }
}
