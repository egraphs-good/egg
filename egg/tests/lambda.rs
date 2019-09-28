use egg::{
    define_term,
    egraph::{AddResult, EClass, Metadata},
    expr::{Expr, Language, QuestionMarkName},
    extract::{calculate_cost, Extractor},
    parse::ParsableLanguage,
    pattern::{Applier, Rewrite, WildMap},
};

use log::*;
use smallvec::smallvec;
use std::rc::Rc;

type EGraph = egg::egraph::EGraph<Lang, Meta>;

define_term! {
    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    enum Lang {
        Bool(bool),
        Num(i32),

        Int = "int",
        Var = "var",

        Add = "+",

        App = "app",
        Lambda = "lam",
        Let = "let",

        Subst = "subst",
    }
}

impl Language for Lang {
    fn cost(&self, children: &[u64]) -> u64 {
        let mine = match self {
            Lang::Bool(_) => 1,
            Lang::Num(_) => 1,

            Lang::Int => 1,
            Lang::Var => 2,
            Lang::Let => 1,
            Lang::App => 200,

            Lang::Subst => 1,
            _ => 3,
        };
        mine + children.iter().sum::<u64>()
    }
}

#[rustfmt::skip]
fn rules() -> Vec<Rewrite<Lang, Meta>> {
    let rw = |name, l, r| Lang::parse_rewrite(name, l, r).unwrap();
    vec![
        rw(
            "beta",
            "(app (lam ?v ?body) ?e)",
            "(subst ?e ?v ?body)"
        ),

        rw("let-lam", "(let ?v ?e ?body)", "(app (lam ?v ?body) ?e)"),
        rw("lam-let", "(app (lam ?v ?body) ?e)", "(let ?v ?e ?body)"),

        rw(
            "subst-lam",
            // NOTE this will capture if variables aren't unique
            "(subst ?e ?v (lam ?var ?body))",
            "(lam ?var (subst ?e ?v ?body))",
        ),

        rw(
            "subst-app",
            "(subst ?e ?v (app ?a ?b))",
            "(app (subst ?e ?v ?a) (subst ?e ?v ?b))",
        ),

        rw(
            "subst-add",
            "(subst ?e ?v (+ ?a ?b))",
            "(+ (subst ?e ?v ?a) (subst ?e ?v ?b))",
        ),

        rw(
            "subst-int",
            "(subst ?e ?v (int ?i))",
            "(int ?i)",
        ),

        rw(
            "add-int",
            "(+ (int ?a) (int ?b)))",
            "(int (+ ?a ?b))",
        ),

        rw("add-comm", "(+ ?a ?b)", "(+ ?b ?a)"),
        rw("add-assoc", "(+ (+ ?a ?b) ?c)", "(+ ?a (+ ?b ?c))"),

        // NOTE variable substitution has to be done by a dynamic
        // pattern, because it knows that if the two variables aren't
        // equal by name, they never will be because names are
        // unique. Egg doesn't have a way for you to write inequality
        // contraints
        Rewrite {
            name: "var-subst".into(),
            lhs: Lang::parse_pattern("(subst ?e ?v1 (var ?v2))").unwrap(),
            applier: Rc::new(VarSubst {
                v1: "?v1".parse().unwrap(),
                v2: "?v2".parse().unwrap(),
                e: "?e".parse().unwrap(),
            }),
            conditions: vec![],
        }
    ]
}

#[derive(Debug)]
struct VarSubst {
    v1: QuestionMarkName,
    v2: QuestionMarkName,
    e: QuestionMarkName,
}

impl Applier<Lang, Meta> for VarSubst {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let v1 = map[&self.v1][0];
        let v2 = map[&self.v2][0];
        let e = map[&self.e][0];
        vec![if v1 == v2 {
            AddResult {
                was_there: true,
                id: e,
            }
        } else {
            egraph.add(Expr::new(Lang::Var, smallvec![v2]))
        }]
    }
}

#[derive(Debug, Clone)]
struct Meta {
    int: Option<i32>,
}

fn map2<A, B>(x: Option<A>, y: Option<A>, f: impl FnOnce(A, A) -> B) -> Option<B> {
    Some(f(x?, y?))
}

impl Metadata<Lang> for Meta {
    type Error = std::convert::Infallible;
    fn merge(&self, other: &Self) -> Self {
        let int = self.int.or(other.int);
        Meta { int }
    }

    fn make(expr: Expr<Lang, &Self>) -> Self {
        let a = |i: usize| expr.children[i].int;
        let int = match &expr.op {
            Lang::Num(i) => Some(*i),
            Lang::Add => map2(a(0), a(1), |x, y| x + y),
            _ => None,
        };
        Meta { int }
    }

    fn modify(eclass: &mut EClass<Lang, Self>) {
        if let Some(int) = eclass.metadata.int {
            let e = Expr::unit(Lang::Num(int));
            eclass.nodes.push(e);
        }
    }
}

fn prove_something(start: &str, goals: &[&str]) {
    let _ = env_logger::builder().is_test(true).try_init();

    let start_expr = Lang::parse_expr(start).unwrap();
    println!("Start ({}): {}", calculate_cost(&start_expr), start);

    let goal_exprs: Vec<_> = goals.iter().map(|g| Lang::parse_expr(g).unwrap()).collect();

    let (mut egraph, root) = EGraph::from_expr(&start_expr);

    let rules = rules();
    let mut egraph_size = 0;
    for i in 0..20 {
        println!("\nIteration {}:", i);
        println!(
            "Size n={}, e={}",
            egraph.total_size(),
            egraph.number_of_classes()
        );

        let ext = Extractor::new(&egraph);
        let best = ext.find_best(root);
        println!("Best ({}): {}", best.cost, best.expr.pretty(40));
        let new_size = egraph.total_size();
        if new_size == egraph_size {
            println!("\nEnding early");
            break;
        }
        egraph_size = new_size;

        for rw in &rules {
            rw.run(&mut egraph);
        }
        egraph.rebuild();
    }

    for (i, (goal_expr, goal_str)) in goal_exprs.iter().zip(goals).enumerate() {
        info!("Trying to prove goal {}: {}", i, goal_str);
        let equivs = egraph.equivs(&start_expr, &goal_expr);
        if equivs.is_empty() {
            panic!("Couldn't prove goal {}: {}", i, goal_str);
        }
    }
}

#[test]
fn lambda_under() {
    prove_something(
        "(lam 0 (+ (int 4)
                   (app (lam 1 (var 1))
                        (int 4))))",
        &[
            "(lam 0 (+ (int 4) (subst (int 4) 1 (var 1))))",
            "(lam 0 (+ (int 4) (int 4)))",
            "(lam 0 (int 8)))",
        ],
    );
}

#[test]
fn lambda_let_simple() {
    prove_something(
        "(let 0 (int 0)
         (let 1 (int 1)
         (+ (var 0) (var 1))))",
        &[
            "(let 1 (int 1)
             (+ (int 0) (var 1)))",
            "(+ (int 0) (int 1))",
            "(int 1)",
        ],
    );
}

#[test]
fn lambda_compose() {
    prove_something(
        "(let 8 (lam 0 (lam 1 (lam 2 (app (var 0)
                                          (app (var 1) (var 2))))))
         (let 9 (lam 4 (+ (var 4) (int 1)))
         (app (app (var 8) (var 9))
              (var 9))))",
        &[
            "(lam 2 (+ (int 1)
                       (app (lam 4 (+ (int 1) (var 4)))
                            (var 2))))",
            "(lam 2 (+ (var 2) (int 2)))",
        ],
    );
}
