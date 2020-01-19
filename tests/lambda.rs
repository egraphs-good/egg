use egg::{
    define_term,
    egraph::{AddResult, EClass, Metadata},
    expr::{Cost, Expr, Language, QuestionMarkName},
    extract::calculate_cost,
    parse::ParsableLanguage,
    pattern::WildMap,
    rewrite::{rw, Applier, Rewrite},
    run::{Runner, SimpleRunner},
};

use log::*;
use smallvec::smallvec;

type EGraph = egg::egraph::EGraph<Lang, Meta>;

define_term! {
    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    enum Lang {
        Bool(bool),
        Num(i32),

        Int = "int",
        Var = "var",

        Add = "+",
        Eq = "=",

        App = "app",
        Lambda = "lam",
        Let = "let",
        Fix = "fix",

        If = "if",

        Subst = "subst",
        String(String),
    }
}

impl Language for Lang {
    fn cost(&self, children: &[Cost]) -> Cost {
        let mine = match self {
            Lang::Bool(_) => 1.0,
            Lang::Num(_) => 1.0,
            Lang::String(_) => 1.0,

            Lang::Int => 1.0,
            Lang::Var => 2.0,
            Lang::Let => 1.0,
            Lang::App => 200.0,

            Lang::Subst => 1.0,
            _ => 3.0,
        };
        mine + children.iter().sum::<Cost>()
    }
}

fn rules() -> Vec<Rewrite<Lang, Meta>> {
    vec![
        // open term rules

        // NOTE I can't write a false rule here
        rw("if-true")
            .p("(if (bool true) ?then ?else)")
            .a("?then")
            .mk(),
        rw("if-false")
            .p("(if (bool false) ?then ?else)")
            .a("?else")
            .mk(),
        rw("add-int")
            .p("(+ (int ?a) (int ?b)))")
            .a("(int (+ ?a ?b))")
            .mk(),
        rw("eq-int")
            .p("(= (int ?a) (int ?b)))")
            .a("(bool (= ?a ?b))")
            .mk(),
        rw("add-comm").p("(+ ?a ?b)").a("(+ ?b ?a)").mk(),
        rw("add-assoc")
            .p("(+ (+ ?a ?b) ?c)")
            .a("(+ ?a (+ ?b ?c))")
            .mk(),
        // subst rules
        rw("fix")
            .p("(fix ?v ?e)")
            .a("(subst (fix ?v ?e) ?v ?e)")
            .mk(),
        rw("beta")
            .p("(app (lam ?v ?body) ?e)")
            .a("(subst ?e ?v ?body)")
            .mk(),
        rw("let-lam")
            .p("(let ?v ?e ?body)")
            .a("(app (lam ?v ?body) ?e)")
            .mk(),
        rw("lam-let")
            .p("(app (lam ?v ?body) ?e)")
            .a("(let ?v ?e ?body)")
            .mk(),
        rw("subst-app")
            .p("(subst ?e ?v (app ?a ?b))")
            .a("(app (subst ?e ?v ?a) (subst ?e ?v ?b))")
            .mk(),
        rw("subst-add")
            .p("(subst ?e ?v (+ ?a ?b))")
            .a("(+ (subst ?e ?v ?a) (subst ?e ?v ?b))")
            .mk(),
        rw("subst-eq")
            .p("(subst ?e ?v (= ?a ?b))")
            .a("(= (subst ?e ?v ?a) (subst ?e ?v ?b))")
            .mk(),
        rw("subst-if")
            .p("(subst ?e ?v (if ?cond ?then ?else))")
            .a("(if (subst ?e ?v ?cond) (subst ?e ?v ?then) (subst ?e ?v ?else))")
            .mk(),
        rw("subst-int")
            .p("(subst ?e ?v (int ?i))")
            .a("(int ?i)")
            .mk(),
        rw("subst-bool")
            .p("(subst ?e ?v (bool ?b))")
            .a("(bool ?b)")
            .mk(),
        // NOTE variable substitution has to be done by a dynamic
        // pattern, because it knows that if the two variables aren't
        // equal by name, they never will be because names are
        // unique. Egg doesn't have a way for you to write inequality
        // contraints
        rw("var-subst")
            .p("(subst ?e ?v1 (var ?v2))")
            .with_applier(VarSubst {
                e: "?e".parse().unwrap(),
                v1: "?v1".parse().unwrap(),
                v2: "?v2".parse().unwrap(),
                body: None,
            })
            .mk(),
        rw("var-subst")
            .p("(subst ?e ?v1 (lam ?v2 ?body))")
            .with_applier(VarSubst {
                e: "?e".parse().unwrap(),
                v1: "?v1".parse().unwrap(),
                v2: "?v2".parse().unwrap(),
                body: Some("?body".parse().unwrap()),
            })
            .mk(),
    ]
}

#[derive(Debug)]
struct VarSubst {
    e: QuestionMarkName,
    v1: QuestionMarkName,
    v2: QuestionMarkName,
    body: Option<QuestionMarkName>,
}

impl Applier<Lang, Meta> for VarSubst {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let v1 = map[&self.v1][0];
        let v2 = map[&self.v2][0];
        let e = map[&self.e][0];

        let res = if let Some(body) = &self.body {
            let body = map[body][0];
            // substituting in a lambda
            if v1 == v2 {
                egraph.add(Expr::new(Lang::Lambda, smallvec![v2, body]))
            } else {
                let sub_body = egraph.add(Expr::new(Lang::Subst, smallvec![e, v1, body]));
                egraph.add(Expr::new(Lang::Lambda, smallvec![v2, sub_body.id]))
            }
        } else {
            // substituting for a variable
            if v1 == v2 {
                AddResult {
                    was_there: true,
                    id: e,
                }
            } else {
                egraph.add(Expr::new(Lang::Var, smallvec![v2]))
            }
        };

        vec![res]
    }
}

#[derive(Debug, Clone)]
struct Meta {
    constant: Option<Lang>,
}

impl Metadata<Lang> for Meta {
    type Error = std::convert::Infallible;
    fn merge(&self, other: &Self) -> Self {
        Meta {
            constant: self.constant.clone().or_else(|| other.constant.clone()),
        }
    }

    fn make(expr: Expr<Lang, &Self>) -> Self {
        use Lang::*;
        let get = |i: usize| expr.children.get(i).and_then(|m| m.constant.clone());
        let constant = match (&expr.op, get(0), get(1)) {
            (Num(i), _, _) => Some(Num(*i)),
            (Add, Some(Num(i1)), Some(Num(i2))) => Some(Num(i1 + i2)),
            (Eq, Some(Num(i1)), Some(Num(i2))) => Some(Bool(i1 == i2)),
            _ => None,
        };
        Meta { constant }
    }

    fn modify(eclass: &mut EClass<Lang, Self>) {
        if let Some(c) = eclass.metadata.constant.clone() {
            eclass.nodes.push(Expr::unit(c));
        }
    }
}

fn prove_something(start: &str, goals: &[&str]) {
    let _ = env_logger::builder().is_test(true).try_init();

    let start_expr = Lang::parse_expr(start).unwrap();
    println!("Start ({}): {}", calculate_cost(&start_expr), start);

    let goal_exprs: Vec<_> = goals.iter().map(|g| Lang::parse_expr(g).unwrap()).collect();

    let (egraph, _) = SimpleRunner::default()
        .with_iter_limit(500)
        .with_node_limit(5_000)
        .run_expr(start_expr.clone(), &rules());

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
        "(lam x (+ (int 4)
                   (app (lam y (var y))
                        (int 4))))",
        &[
            "(lam x (+ (int 4) (subst (int 4) y (var y))))",
            "(lam x (+ (int 4) (int 4)))",
            "(lam x (int 8)))",
        ],
    );
}

#[test]
fn lambda_let_simple() {
    prove_something(
        "(let x (int 0)
         (let y (int 1)
         (+ (var x) (var y))))",
        &[
            "(let y (int 1)
             (+ (int 0) (var y)))",
            "(+ (int 0) (int 1))",
            "(int 1)",
        ],
    );
}

#[test]
#[should_panic(expected = "Couldn't prove goal 0")]
fn lambda_capture() {
    prove_something("(subst (int 1) x (lam x (var x)))", &["(lam x (int 1))"]);
}

#[test]
fn lambda_compose() {
    prove_something(
        "(let compose (lam f (lam g (lam x (app (var f)
                                           (app (var g) (var x))))))
         (let add1 (lam y (+ (var y) (int 1)))
         (app (app (var compose) (var add1)) (var add1))))",
        &[
            "(lam x (+ (int 1)
                       (app (lam y (+ (int 1) (var y)))
                            (var x))))",
            "(lam x (+ (var x) (int 2)))",
        ],
    );
}

#[test]
fn lambda_if() {
    prove_something(
        "(let zeroone (lam x
           (if (= (var x) (int 0))
               (int 0)
               (int 1)))
         (+ (app (var zeroone) (int 0))
            (app (var zeroone) (int 10))))",
        &[
            "(+
               (if (bool false) (int 0) (int 1))
               (if (bool true) (int 0) (int 1)))",
            "(+ (int 1) (int 0))",
            "(int 1)",
        ],
    );
}

// NOTE, for some reason this breaks the parent pointers version,
// namely it's missing a union (would require more rebuilds)
#[cfg_attr(feature = "parent-pointers", ignore)]
#[test]
fn lambda_fib() {
    prove_something(
        "(let fib (fix fib (lam n
           (if (= (var n) (int 0))
               (int 0)
           (if (= (var n) (int 1))
               (int 1)
           (+ (app (var fib)
                   (+ (var n) (int -1)))
              (app (var fib)
                   (+ (var n) (int -2))))))))
         (app (var fib) (int 4)))",
        &["(int 3)"],
    );
}
