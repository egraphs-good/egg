use log::*;
use std::convert::TryFrom;
use std::fmt;

use crate::*;

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
    expr: Option<(Query<L>, qry::VarMap<VarOrId>, qry::Expr<L::Operator, Id>)>,
}

impl<L: Language> PartialEq for Pattern<L> {
    fn eq(&self, other: &Self) -> bool {
        self.ast == other.ast
    }
}

pub type LangDB<L> = qry::Database<<L as Language>::Operator, Id>;

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
    // println!("Compiled {}\n      to {:?}\n      vars: {:?}", ast, q.atoms, q.vars);
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
        // TODO: this should be deleted
        // Currently, our GJ does not handle variable constraints
        // Also, conditions like is_const should be used to prune
        // the search space.
        // Meanwhile, should consider adding support for multi-pattern soon
        // let contains_only_vars = nodes.iter().all(|n| match n {
        //     ENodeOrVar::Var(_) => true,
        //     _ => false
        // });
        let contains_only_vars = true;
        if is_var || !contains_only_vars {
            Pattern {
                expr: None,
                ast,
                program,
            }
        } else {
            let q = compile_to_query(&ast);
            let (var_map, expr) = q.compile();
            Pattern {
                expr: Some((q.clone(), var_map, expr)),
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
        use crate::egraph::Strategy;
        if let Some((q, var_map, expr)) = self.expr.as_ref() {
            if egraph.strategy != Strategy::EMatch {
                let var_map = q.vars(&egraph.db);

                let mut map: HashMap<Id, Vec<Subst>> = Default::default();
                let vars: Vec<(Var, usize)> = var_map
                    .iter()
                    .filter_map(|(vori, i)| match vori {
                        VarOrId::Var(v) => Some((*v, *i)),
                        VarOrId::Id(_) => None,
                    })
                    .collect();

                let root = self.ast.as_ref().len() - 1;
                let root_index = var_map[&VarOrId::Id(root.into())];

                // expr.for_each(&egraph.db, &mut egraph.eval_ctx.borrow_mut(), |tuple| {
                //     let vec = vars.iter().map(|(v, i)| (*v, tuple[*i])).collect();
                //     let subst = Subst { vec };
                //     let root = egraph.find(tuple[root_index]);
                //     map.entry(root).or_default().push(subst);
                // });

                q.join(
                    &var_map,
                    &egraph.db,
                    &mut egraph.eval_ctx.borrow_mut(),
                    |tuple| {
                        let vec = vars.iter().map(|(v, i)| (*v, tuple[*i])).collect();
                        let subst = Subst { vec };
                        let root = egraph.find(tuple[root_index]);
                        map.entry(root).or_default().push(subst);
                    },
                );

                return map
                    .into_iter()
                    .map(|(eclass, substs)| SearchMatches { eclass, substs })
                    .collect();
            }
        }

        // performs e-matching
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
        use crate::egraph::Strategy;
        if self.expr.is_some() && egraph.strategy != Strategy::EMatch {
            // could be further optimized
            let id = egraph.find(eclass);
            self.search(egraph).into_iter().find(|m| m.eclass == id)
        } else {
            let substs = self.program.run(egraph, eclass);
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
        let mut added = vec![];
        let ast = self.ast.as_ref();
        let mut id_buf = vec![0.into(); ast.len()];
        for mat in matches {
            for subst in &mat.substs {
                let id = apply_pat(&mut id_buf, ast, egraph, subst);
                let (to, did_something) = egraph.union(id, mat.eclass);
                if did_something {
                    added.push(to)
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

#[cfg(test)]
mod qry_bench {
    use super::*;
    use std::str::FromStr;
    #[allow(non_snake_case)]
    fn V(s: &str) -> VarOrId {
        VarOrId::Var(Var::from_str(s).unwrap())
    }

    #[allow(non_snake_case)]
    fn I(n: usize) -> VarOrId {
        VarOrId::Id(Id::from(n))
    }

    mod math {
        use super::*;
        use crate::egraph::Strategy;
        use crate::{rewrite as rw, *};
        use ordered_float::NotNan;
        pub type EGraph = crate::EGraph<Math, ()>;
        pub type Rewrite = crate::Rewrite<Math, ()>;
        pub type Constant = NotNan<f64>;
        define_language! {
            pub enum Math {
                "+" = Add([Id; 2]),
                "-" = Sub([Id; 2]),
                "*" = Mul([Id; 2]),
                "/" = Div([Id; 2]),
                Constant(Constant),
                Symbol(Symbol),
            }
        }

        #[rustfmt::skip]
        pub fn rules() -> Vec<Rewrite> { vec![
            rw!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
            rw!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
            rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
            rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        
            rw!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
        
            rw!("zero-add"; "(+ ?a 0)" => "?a"),
            rw!("zero-mul"; "(* ?a 0)" => "0"),
            rw!("one-mul";  "(* ?a 1)" => "?a"),
        
            rw!("add-zero"; "?a" => "(+ ?a 0)"),
            rw!("mul-one";  "?a" => "(* ?a 1)"),
        
            rw!("cancel-sub"; "(- ?a ?a)" => "0"),
        
            rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
            rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        ]}

        fn saturate() -> EGraph {
            let rules: Vec<_> = rules();
            let expr1 = "(+ (* y (+ x y)) (- (+ x 2) (+ x x)))".parse().unwrap();
            // let expr1 = "(- ?x ?x)".parse().unwrap();
            let mut egraph: EGraph = Default::default();
            egraph.strategy = Strategy::EMatch;
            let runner: Runner<Math, ()> = Runner::default()
                // .with_egraph(egraph)
                .with_expr(&expr1)
                // .with_node_limit(200_000)
                .with_node_limit(50_000)
                .with_iter_limit(1000)
                .with_time_limit(std::time::Duration::from_secs(4000))
                .run(&rules);
            println!("stop reason: {:?}", runner.stop_reason);
            println!(
                "egraph size: {} {}",
                runner.egraph.total_number_of_nodes(),
                runner.egraph.number_of_classes()
            );
            runner.egraph
        }

        fn triangle_dist_query(
            egraph: &EGraph,
            q: &Query<Math>,
            var_map: qry::VarMap<VarOrId>,
        ) {
            let mut count = 0;
            q.join(
                &var_map,
                &egraph.db,
                &mut egraph.eval_ctx.borrow_mut(),
                |tuple| {
                    count += 1;
                },
            );
            eprintln!("size: {:?}", count);
        }

        use itertools::Itertools;
        // #[test]
        pub fn triangle_diff_order() {
            let mut egraph = saturate();
            let expr: RecExpr<ENodeOrVar<Math>> = "(+ (* ?x ?y) (* ?x ?z))".parse().unwrap();
            let query = compile_to_query(&expr);
            let var_map = query.vars(&egraph.db);
            // println!("expr: {:?}", expr);
            // println!("var_map: {:?}", var_map);
            assert!(
                var_map.keys().len() == 6
                    && var_map.keys().all(|v| vec![
                        // variable with 2 occurrences
                        V("?x"),
                        I(5),
                        I(2),
                        // variable with 1 occurrence
                        V("?y"),
                        I(6),
                        V("?z"),
                    ]
                    .contains(v))
            );
            for group1 in (0..3).permutations(3) {
                egraph.eval_ctx.borrow_mut().clear();
                let start_time = std::time::Instant::now();
                let var_map = vec![
                    // variable with 2 occurrences
                    (V("?x"), group1[0]),
                    (I(5), group1[1]),
                    (I(2), group1[2]),
                    // variable with 1 occurrence
                    (V("?y"), 3),
                    (I(6), 4),
                    (V("?z"), 5),
                ]
                .into_iter()
                .collect();
                triangle_dist_query(&mut egraph, &query, var_map);
                println!("group: {:?}", group1);
                println!("time: {:?}", std::time::Instant::now() - start_time);
            }

            let pattern = Pattern::from(expr);
            let start_time = std::time::Instant::now();
            let result = pattern.search(&egraph);
            println!(
                "baseline time: {:?}",
                std::time::Instant::now() - start_time
            );
            println!(
                "size: {:?}",
                result.iter().map(|m| m.substs.len()).sum::<usize>()
            );
        }

        struct Trie<T>(HashMap<T, Self>);
        impl<T> Default for Trie<T> {
            fn default() -> Self {
                Self(Default::default())
            }
        }
        fn intersect(t1: &Trie<Id>, t2: &Trie<Id>, k: impl FnMut((&Id, &Trie<Id>, &Trie<Id>))) {
            if t1.0.len() < t2.0.len() {
                t1.0.iter()
                    .filter_map(|(k, v)| Some((k, v, t2.0.get(k)?)))
                    .for_each(k)
            } else {
                t2.0.iter()
                    .filter_map(|(k, v)| Some((k, t1.0.get(k)?, v)))
                    .for_each(k)
            }
        }

        // #[test]
        pub fn triangle_vs_manual() {
            let egraph = saturate();
            let expr: RecExpr<ENodeOrVar<Math>> = "(+ (* ?x ?y) (* ?x ?z))".parse().unwrap();
            let query = compile_to_query(&expr);
            let var_map = query.vars(&egraph.db);
            // println!("expr: {:?}", expr);
            // println!("var_map: {:?}", var_map);
            assert!(
                var_map.keys().len() == 6
                    && var_map.keys().all(|v| vec![
                        // variable with 2 occurrences
                        V("?x"),
                        I(5),
                        I(2),
                        // variable with 1 occurrence
                        V("?y"),
                        I(6),
                        V("?z"),
                    ]
                    .contains(v))
            );
            egraph.eval_ctx.borrow_mut().clear();
            let start_time = std::time::Instant::now();
            let var_map = vec![
                // variable with 2 occurrences
                (V("?x"), 0),
                (I(5), 1),
                (I(2), 2),
                // variable with 1 occurrence
                (V("?y"), 3),
                (I(6), 4),
                (V("?z"), 5),
            ]
            .into_iter()
            .collect();
            let mut result: Vec<Vec<Id>> = vec![];
            query.join(
                &var_map,
                &egraph.db,
                &mut egraph.eval_ctx.borrow_mut(),
                |tuple| {
                    // count += 1;
                    result.push(tuple.to_vec());
                },
            );
            eprintln!("size: {:?}", result.len());
            std::thread::spawn(move || drop(result));
            eprintln!("time: {:?}", std::time::Instant::now() - start_time);
            use rustc_hash::FxHashMap as HashMap;
            let start_time = std::time::Instant::now();
            let mut add_idx: Trie<Id> = Default::default();
            let mut mul_idx: Trie<Id> = Default::default();
            for class in egraph.classes() {
                let id = class.id;
                for node in class.iter() {
                    match node {
                        Math::Add([a, b]) => {
                            add_idx
                                .0
                                .entry(*a)
                                .or_default()
                                .0
                                .entry(*b)
                                .or_default()
                                .0
                                .insert(id, Default::default());
                        }
                        Math::Mul([a, b]) => {
                            mul_idx
                                .0
                                .entry(*a)
                                .or_default()
                                .0
                                .entry(id)
                                .or_default()
                                .0
                                .insert(*b, Default::default());
                        }
                        _ => {}
                    };
                }
            }
            let mut acc = vec![];
            let mut result = vec![];
            let mut count = 0;
            // TODO:
            // my feeling is that if you are doing complex things for each match,
            // which is as expensive as a vector copying. Then the interpretative
            // overhead may not be that large.
            // And resource de-allocation takes a large amount of time...
            intersect(&mul_idx, &mul_idx, |(x, mul1, mul2)| {
                acc.push(*x);
                intersect(&mul1, &add_idx, |(xy, mul1, add)| {
                    intersect(&mul2, &add, |(xz, mul2, add)| {
                        for (root, _) in &add.0 {
                            acc.push(*root);
                            for (y, _) in &mul1.0 {
                                acc.push(*y);
                                for (z, _) in &mul2.0 {
                                    acc.push(*z);
                                    result.extend_from_slice(&acc);
                                    acc.pop();
                                }
                                acc.pop();
                            }
                            acc.pop();
                        }
                    })
                });
                acc.pop();
            });
            eprintln!("size: {:?}", result.len());
            std::thread::spawn(move || drop(result));
            eprintln!("time: {:?}", std::time::Instant::now() - start_time);
        }
    }

    mod lambda {
        use crate::egraph::Strategy;
        use crate::pattern::*;
        use super::*;
        use crate::{rewrite as rw};
        use itertools::Itertools;

        fn if_elim_query(
            egraph: &EGraph,
            q: &Query<Lambda>,
            var_map: qry::VarMap<VarOrId>,
        ) {
            let mut count = 0;
            q.join(
                &var_map,
                &egraph.db,
                &mut egraph.eval_ctx.borrow_mut(),
                |tuple| {
                    count += 1;
                },
            );
            eprintln!("size: {:?}", count);
        }

        // #[test]
        fn if_elim_query_bench() {
            let mut egraph = saturate();
            let expr: RecExpr<ENodeOrVar<Lambda>> = "(if (= (var ?x) ?e) ?then ?else)".parse().unwrap();
            let query = compile_to_query(&expr);
            let var_map = query.vars(&egraph.db);
            println!("expr: {:?}", expr);
            println!("query: {:?}", query);
            println!("var_map: {:?}", var_map);
            // println!("{:?}", egraph.db.relations.iter().map(|(k,v)| (k, v.len())).collect::<Vec<_>>());
            assert!(
                var_map.keys().len() == 7
                    && var_map.keys().all(|v| vec![
                        // variable with 2 occurrences
                        I(1),
                        I(3),
                        // variable with 1 occurrence
                        I(6),
                        V("?else"),
                        V("?then"),
                        V("?x"),
                        V("?e")
                    ]
                    .contains(v))
            );
            // TODO:
            // the difference seems to be within 2x. 
            // {I(1): 0, I(3): 1} seems to be better than {I(3): 0, I(1): 1}
            // and I(1) is the "inner" join variable (the one that connects
            // eq and var)

            // (5,6,4,3,2) and (5,6,4,2,3) are also the winner for group2.
            // {(V("?e", 2), (V("?x"), 3), (V("?then"), 4), (I(6), 5), (V("?else"), 6), }
            // Eq: 123, Var: 137, If: 10076
            // LESSON: has variables attached to smaller relations firsts (at least for
            // variables with one occurrence)
            //
            // Maybe we should first develop the engine that allows customizable optimizers 
            // before experimenting with more optimizations!
            // Idea: root probably should be the first in the sequence of all variables with one
            // occurrence since this results in better locality
            for group1 in (0..2).permutations(2) {
                for groups2 in (2..7).permutations(5) {
                    egraph.eval_ctx.borrow_mut().clear();
                    let start_time = std::time::Instant::now();
                    let var_map = vec![
                        // variable with 2 occurrences
                        (I(1), group1[0]),
                        (I(3), group1[1]),
                        // variable with 1 occurrence
                        (I(6), groups2[0]),
                        (V("?else"), groups2[1]),
                        (V("?then"), groups2[2]),
                        (V("?x"), groups2[3]),
                        (V("?e"),groups2[4])
                    ]
                    .into_iter()
                    .collect();
                    if_elim_query(&mut egraph, &query, var_map);
                    println!("group: {:?} {:?}", group1, groups2);
                    println!("time: {:?}", std::time::Instant::now() - start_time);
                }
            }
        }

        fn saturate() -> EGraph {
            let rules: Vec<_> = rules();
            let expr1 = 
            "(let compose (lam f (lam g (lam x (app (var f)
                            (app (var g) (var x))))))
            (let repeat (fix repeat (lam fun (lam n
                (if (= (var n) 0)
                    (lam i (var i))
                    (app (app (var compose) (var fun))
                            (app (app (var repeat)
                                    (var fun))
                                    (+ (var n) -1)))))))
            (let add1 (lam y (+ (var y) 1))
                (app (app (var repeat)
                    (var add1))
                    2))))".parse().unwrap();
            // let expr1 = "(- ?x ?x)".parse().unwrap();
            let mut egraph: EGraph = Default::default();
            egraph.strategy = Strategy::EMatch;
            let runner: Runner<Lambda, LambdaAnalysis> = Runner::default()
                // .with_egraph(egraph)
                .with_expr(&expr1)
                .with_node_limit(200_000)
                // .with_node_limit(50_000)
                .with_iter_limit(1000)
                .with_time_limit(std::time::Duration::from_secs(4000))
                .run(&rules);
            println!("stop reason: {:?}", runner.stop_reason);
            println!(
                "egraph size: {} {}",
                runner.egraph.total_number_of_nodes(),
                runner.egraph.number_of_classes()
            );
            runner.egraph
        }

        define_language! {
            enum Lambda {
                Bool(bool),
                Num(i32),
                "var" = Var(Id),
                "+" = Add([Id; 2]),
                "=" = Eq([Id; 2]),
                "app" = App([Id; 2]),
                "lam" = Lambda([Id; 2]),
                "let" = Let([Id; 3]),
                "fix" = Fix([Id; 2]),
                "if" = If([Id; 3]),
                Symbol(Symbol),
            }
        }

        impl Lambda {
            fn num(&self) -> Option<i32> {
                match self {
                    Lambda::Num(n) => Some(*n),
                    _ => None,
                }
            }
        }

        type EGraph = crate::EGraph<Lambda, LambdaAnalysis>;

        fn var(s: &str) -> Var {
            s.parse().unwrap()
        }
        fn is_not_same_var(v1: Var, v2: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
            move |egraph, _, subst| egraph.find(subst[v1]) != egraph.find(subst[v2])
        }
        fn is_const(v: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
            move |egraph, _, subst| egraph[subst[v]].data.constant.is_some()
        }

        #[derive(Default)]
        struct LambdaAnalysis;

        #[derive(Debug)]
        struct Data {
            free: HashSet<Id>,
            constant: Option<Lambda>,
        }

        fn eval(egraph: &EGraph, enode: &Lambda) -> Option<Lambda> {
            let x = |i: &Id| egraph[*i].data.constant.clone();
            match enode {
                Lambda::Num(_) | Lambda::Bool(_) => Some(enode.clone()),
                Lambda::Add([a, b]) => Some(Lambda::Num(x(a)?.num()? + x(b)?.num()?)),
                Lambda::Eq([a, b]) => Some(Lambda::Bool(x(a)? == x(b)?)),
                _ => None,
            }
        }

        use std::cmp::Ordering;
        impl Analysis<Lambda> for LambdaAnalysis {
            type Data = Data;
            fn merge(&self, to: &mut Data, from: Data) -> Option<Ordering> {
                let before_len = to.free.len();
                // to.free.extend(from.free);
                to.free.retain(|i| from.free.contains(i));
                let did_change = before_len != to.free.len();
                if to.constant.is_none() && from.constant.is_some() {
                    to.constant = from.constant;
                    None
                } else if did_change {
                    None
                } else {
                    Some(Ordering::Greater)
                }
            }
            fn make(egraph: &EGraph, enode: &Lambda) -> Data {
                let f = |i: &Id| egraph[*i].data.free.iter().cloned();
                let mut free = HashSet::default();
                match enode {
                    Lambda::Var(v) => {
                        free.insert(*v);
                    }
                    Lambda::Let([v, a, b]) => {
                        free.extend(f(b));
                        free.remove(v);
                        free.extend(f(a));
                    }
                    Lambda::Lambda([v, a]) | Lambda::Fix([v, a]) => {
                        free.extend(f(a));
                        free.remove(v);
                    }
                    _ => enode.for_each(|c| free.extend(&egraph[c].data.free)),
                }
                let constant = eval(egraph, enode);
                Data { constant, free }
            }
            fn modify(egraph: &mut EGraph, id: Id) {
                if let Some(c) = egraph[id].data.constant.clone() {
                    let const_id = egraph.add(c);
                    egraph.union(id, const_id);
                }
            }
        }
        fn rules() -> Vec<Rewrite<Lambda, LambdaAnalysis>> {
            vec![
                // open term rules
                rw!("if-true";  "(if  true ?then ?else)" => "?then"),
                rw!("if-false"; "(if false ?then ?else)" => "?else"),
                rw!("if-elim"; "(if (= (var ?x) ?e) ?then ?else)" => "?else"
                    if ConditionEqual::parse("(let ?x ?e ?then)", "(let ?x ?e ?else)")),
                rw!("add-comm";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
                rw!("add-assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
                rw!("eq-comm";   "(= ?a ?b)"        => "(= ?b ?a)"),
                // subst rules
                rw!("fix";      "(fix ?v ?e)"             => "(let ?v (fix ?v ?e) ?e)"),
                rw!("beta";     "(app (lam ?v ?body) ?e)" => "(let ?v ?e ?body)"),
                rw!("let-app";  "(let ?v ?e (app ?a ?b))" => "(app (let ?v ?e ?a) (let ?v ?e ?b))"),
                rw!("let-add";  "(let ?v ?e (+   ?a ?b))" => "(+   (let ?v ?e ?a) (let ?v ?e ?b))"),
                rw!("let-eq";   "(let ?v ?e (=   ?a ?b))" => "(=   (let ?v ?e ?a) (let ?v ?e ?b))"),
                rw!("let-const";
                    "(let ?v ?e ?c)" => "?c" if is_const(var("?c"))),
                rw!("let-if";
                    "(let ?v ?e (if ?cond ?then ?else))" =>
                    "(if (let ?v ?e ?cond) (let ?v ?e ?then) (let ?v ?e ?else))"
                ),
                rw!("let-var-same"; "(let ?v1 ?e (var ?v1))" => "?e"),
                rw!("let-var-diff"; "(let ?v1 ?e (var ?v2))" => "(var ?v2)"
                    if is_not_same_var(var("?v1"), var("?v2"))),
                rw!("let-lam-same"; "(let ?v1 ?e (lam ?v1 ?body))" => "(lam ?v1 ?body)"),
                rw!("let-lam-diff";
                    "(let ?v1 ?e (lam ?v2 ?body))" =>
                    { CaptureAvoid {
                        fresh: var("?fresh"), v2: var("?v2"), e: var("?e"),
                        if_not_free: "(lam ?v2 (let ?v1 ?e ?body))".parse().unwrap(),
                        if_free: "(lam ?fresh (let ?v1 ?e (let ?v2 (var ?fresh) ?body)))".parse().unwrap(),
                    }}
                    if is_not_same_var(var("?v1"), var("?v2"))),
            ]
        }
        struct CaptureAvoid {
            fresh: Var,
            v2: Var,
            e: Var,
            if_not_free: Pattern<Lambda>,
            if_free: Pattern<Lambda>,
        }
        impl Applier<Lambda, LambdaAnalysis> for CaptureAvoid {
            fn apply_one(&self, egraph: &mut EGraph, eclass: Id, subst: &Subst) -> Vec<Id> {
                let e = subst[self.e];
                let v2 = subst[self.v2];
                let v2_free_in_e = egraph[e].data.free.contains(&v2);
                if v2_free_in_e {
                    let mut subst = subst.clone();
                    let sym = Lambda::Symbol(format!("_{}", eclass).into());
                    subst.insert(self.fresh, egraph.add(sym));
                    self.if_free.apply_one(egraph, eclass, &subst)
                } else {
                    self.if_not_free.apply_one(egraph, eclass, &subst)
                }
            }
        }
    }
}
