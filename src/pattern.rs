use log::*;
use std::convert::TryFrom;
use std::fmt;

use crate::*;

static CHECK_INTERVAL: usize = 4096;

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
/// [`FromStr`]: std::str::FromStr
#[derive(Debug, Clone)]
pub struct Pattern<L: Language> {
    /// The actual pattern as a [`RecExpr`]
    pub ast: PatternAst<L>,
    program: machine::Program<L>,
    query: Option<Query<L>>,
}

impl<L: Language> PartialEq for Pattern<L> {
    fn eq(&self, other: &Self) -> bool {
        self.ast == other.ast
    }
}

pub(crate) type LangDB<L> = qry::Database<<L as Language>::Operator, Id>;

/// A [`RecExpr`] that represents a
/// [`Pattern`].
pub type PatternAst<L> = RecExpr<ENodeOrVar<L>>;

impl<L: Language> Pattern<L> {
    /// Returns a list of the [`Var`]s in this pattern.
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
#[derive(Debug, Hash, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum ENodeOrVar<L> {
    /// An enode from the underlying [`Language`]
    ENode(L),
    /// A pattern variable
    Var(Var),
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum OpOrVar<L: Language> {
    Op(L::Operator),
    Var(Var),
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum VarOrId {
    Var(Var),
    Id(Id),
}

type Query<L> = qry::Query<VarOrId, <L as Language>::Operator, Id>;

fn compile_to_query<L: Language>(ast: &PatternAst<L>) -> Query<L> {
    use qry::*;
    let mut atoms = vec![];

    for (i, node) in ast.as_ref().iter().enumerate() {
        if let ENodeOrVar::ENode(n) = node {
            let mut terms: Vec<Term<_, _>> = vec![Term::Variable(VarOrId::Id(i.into()))];
            n.for_each(|child| {
                terms.push(match ast[child] {
                    ENodeOrVar::ENode(_) => Term::Variable(VarOrId::Id(child)),
                    ENodeOrVar::Var(v) => Term::Variable(VarOrId::Var(v)),
                })
            });
            atoms.push(Atom::new(n.operator(), terms));
        }
    }

    assert!(!atoms.is_empty());
    let q = Query::new(atoms);
    q
}

impl<L: Language> Language for ENodeOrVar<L> {
    type Operator = OpOrVar<L>;

    fn operator(&self) -> Self::Operator {
        match self {
            ENodeOrVar::ENode(op) => OpOrVar::Op(op.operator()),
            ENodeOrVar::Var(v) => OpOrVar::Var(*v),
        }
    }

    fn matches(&self, _other: &Self) -> bool {
        panic!("Should never call this")
    }

    fn for_each<F: FnMut(Id)>(&self, f: F) {
        match self {
            ENodeOrVar::ENode(n) => n.for_each(f),
            ENodeOrVar::Var(_) => (),
        }
    }

    fn for_each_mut<F: FnMut(&mut Id)>(&mut self, f: F) {
        match self {
            ENodeOrVar::ENode(n) => n.for_each_mut(f),
            ENodeOrVar::Var(_) => (),
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
        let nodes = ast.as_ref();
        let is_var = nodes.len() == 1 && matches!(nodes[0], ENodeOrVar::Var(_));
        if is_var {
            Pattern {
                query: None,
                ast,
                program,
            }
        } else {
            let q = compile_to_query(&ast);
            Pattern {
                query: Some(q),
                ast,
                program,
            }
        }
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
#[derive(Debug)]
pub struct SearchMatches {
    /// The eclass id that these matches were found in.
    pub eclass: Id,
    /// The matches themselves.
    pub substs: Vec<Subst>,
}

impl<L: Language, A: Analysis<L>> Searcher<L, A> for Pattern<L> {
    fn search(&self, egraph: &EGraph<L, A>) -> Vec<SearchMatches> {
        self.search_with_limit(egraph, usize::MAX)
    }
    fn search_with_limit(&self, egraph: &EGraph<L, A>, mut limit: usize) -> Vec<SearchMatches> {
        if limit == 0 {
            return vec![];
        }
        if let Some(q) = self.query.as_ref() {
            if egraph.strategy != Strategy::EMatch {
                let var_map = q.vars(&egraph.db);

                let vars: Vec<(Var, usize)> = var_map
                    .iter()
                    .enumerate()
                    .filter_map(|(i, vori)| match vori {
                        VarOrId::Var(v) => Some((*v, i)),
                        VarOrId::Id(_) => None,
                    })
                    .collect();

                let root = self.ast.as_ref().len() - 1;
                let root_expr = VarOrId::Id(root.into());
                let root_index = var_map.iter().position(|e| e == &root_expr).unwrap();

                let mut map: HashMap<Id, Vec<Subst>> = Default::default();
                use std::borrow::BorrowMut;
                q.join(
                    &var_map,
                    &egraph.db,
                    egraph.eval_ctx.try_lock().unwrap().borrow_mut(),
                    |tuple| {
                        let vec = vars.iter().map(|(v, i)| (*v, tuple[*i])).collect();
                        let subst = Subst { vec };
                        let root = egraph.find(tuple[root_index]);
                        map.entry(root).or_default().push(subst);
                        limit -= 1;
                        if limit == 0 {
                            return Err(());
                        }
                        Ok(())
                    },
                )
                .unwrap_or_default();

                return map
                    .into_iter()
                    .map(|(eclass, substs)| SearchMatches { eclass, substs })
                    .collect();
            }
        }

        match self.ast.as_ref().last().unwrap() {
            ENodeOrVar::ENode(e) => {
                #[allow(clippy::mem_discriminant_non_enum)]
                let key = std::mem::discriminant(e);
                match egraph.classes_by_op.get(&key) {
                    None => vec![],
                    Some(ids) => {
                        let res: Vec<_> = ids
                            .iter()
                            .filter_map(|&id| {
                                let res = self.search_eclass_with_limit(egraph, id, limit)?;
                                assert!(res.substs.len() <= limit);
                                limit -= res.substs.len();
                                Some(res)
                            })
                            .collect();
                        res
                    }
                }
            }
            ENodeOrVar::Var(_) => egraph
                .classes()
                .filter_map(|e| self.search_eclass_with_limit(egraph, e.id, limit))
                .collect(),
        }
    }

    fn search_eclass(&self, egraph: &EGraph<L, A>, eclass: Id) -> Option<SearchMatches> {
        self.search_eclass_with_limit(egraph, eclass, usize::MAX)
    }

    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<L, A>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches> {
        if self.query.is_some() && egraph.strategy != Strategy::EMatch {
            // TODO: could be further optimized
            let id = egraph.find(eclass);
            self.search_with_limit(egraph, limit)
                .into_iter()
                .find(|m| m.eclass == id)
        } else {
            let substs = self.program.run_with_limit(egraph, eclass, limit);
            if substs.is_empty() {
                None
            } else {
                Some(SearchMatches { eclass, substs })
            }
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
        let ast = self.ast.as_ref();
        let mut id_buf = vec![0.into(); ast.len()];
        let id = apply_pat(&mut id_buf, ast, egraph, subst);
        vec![id]
    }

    fn vars(&self) -> Vec<Var> {
        Pattern::vars(self)
    }

    fn apply_matches(&self, egraph: &mut EGraph<L, A>, matches: &[SearchMatches]) -> Vec<Id> {
        self.apply_matches_with_limit(egraph, matches, usize::MAX)
    }

    fn apply_matches_with_limit(
        &self,
        egraph: &mut EGraph<L, A>,
        matches: &[SearchMatches],
        limit: usize,
    ) -> Vec<Id> {
        let mut added = vec![];
        let ast = self.ast.as_ref();
        let mut id_buf = vec![0.into(); ast.len()];
        for mat in matches {
            for subst in &mat.substs {
                let id = apply_pat(&mut id_buf, ast, egraph, subst);
                let (to, did_something) = egraph.union(id, mat.eclass);
                if did_something {
                    added.push(to);
                    if added.len() >= limit {
                        return added;
                    }
                }
            }
        }
        added
    }
}

fn apply_pat<L: Language, A: Analysis<L>>(
    ids: &mut [Id],
    pat: &[ENodeOrVar<L>],
    egraph: &mut EGraph<L, A>,
    subst: &Subst,
) -> Id {
    debug_assert_eq!(pat.len(), ids.len());
    trace!("apply_rec {:2?} {:?}", pat, subst);

    for (i, pat_node) in pat.iter().enumerate() {
        let id = match pat_node {
            ENodeOrVar::Var(w) => subst[*w],
            ENodeOrVar::ENode(e) => {
                let n = e.clone().map_children(|child| ids[usize::from(child)]);
                trace!("adding: {:?}", n);
                egraph.add(n)
            }
        };
        ids[i] = id;
    }

    *ids.last().unwrap()
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

        let matches = commute_plus.searcher.search(&egraph);
        let n_matches: usize = matches.iter().map(|m| m.substs.len()).sum();
        assert_eq!(n_matches, 2, "matches is wrong: {:#?}", matches);

        let applications = commute_plus.applier.apply_matches(&mut egraph, &matches);
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
