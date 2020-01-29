use egg::{
    define_term,
    egraph::{EClass, EGraph, Metadata},
    expr::{Expr, Name},
    parse::ParsableLanguage,
    rewrite::{rw, Rewrite},
    run::{Runner, SimpleRunner},
};
use log::*;

define_term! {
    enum Prop {
        Bool(bool),
        And = "&",
        Not = "~",
        Or = "|",
        Implies = "->",
        Variable(Name),
    }
}

macro_rules! rule {
    ($name:ident, $left:expr, $right:expr) => {
        #[allow(dead_code)]
        fn $name<M: Metadata<Prop>>() -> Rewrite<Prop, M> {
            rw(stringify!($name))
                .with_pattern_str($left)
                .unwrap()
                .with_applier_str($right)
                .unwrap()
                .build()
                .unwrap()
        }
    };
    ($name:ident, $name2:ident, $left:expr, $right:expr) => {
        rule!($name, $left, $right);
        rule!($name2, $right, $left);
    };
}

rule! {def_imply, def_imply_flip,   "(-> ?a ?b)",       "(| (~ ?a) ?b)"          }
rule! {double_neg, double_neg_flip,  "(~ (~ ?a))",       "?a"                     }
rule! {assoc_or,    "(| ?a (| ?b ?c))", "(| (| ?a ?b) ?c)"       }
rule! {dist_and_or, "(& ?a (| ?b ?c))", "(| (& ?a ?b) (& ?a ?c))"}
rule! {dist_or_and, "(| ?a (& ?b ?c))", "(& (| ?a ?b) (| ?a ?c))"}
rule! {comm_or,     "(| ?a ?b)",        "(| ?b ?a)"              }
rule! {comm_and,    "(& ?a ?b)",        "(& ?b ?a)"              }
rule! {lem,         "(| ?a (~ ?a))",    "true"                      }
rule! {or_true,     "(| ?a true)",         "true"                      }
rule! {and_true,    "(& ?a true)",         "?a"                     }
rule! {contrapositive, "(-> ?a ?b)",    "(-> (~ ?b) (~ ?a))"     }
rule! {lem_imply, "(& (-> ?a ?b) (-> (~ ?a) ?c))", "(| ?b ?c)"}

fn prove_something(name: &str, start: &str, rewrites: &[Rewrite<Prop, ()>], goals: &[&str]) {
    let _ = env_logger::builder().is_test(true).try_init();
    info!("Proving {}", name);

    let start_expr = Prop::parse_expr(start).unwrap();
    let goal_exprs: Vec<_> = goals.iter().map(|g| Prop::parse_expr(g).unwrap()).collect();

    let (egraph, _) = SimpleRunner::default()
        .with_iter_limit(20)
        .with_node_limit(5_000)
        .run_expr(start_expr.clone(), rewrites);

    for (i, (goal_expr, goal_str)) in goal_exprs.iter().zip(goals).enumerate() {
        info!("Trying to prove goal {}: {}", i, goal_str);
        let equivs = egraph.equivs(&start_expr, &goal_expr);
        if equivs.is_empty() {
            panic!("Couldn't prove goal {}: {}", i, goal_str);
        }
    }
}

#[test]
fn prove_contrapositive() {
    let _ = env_logger::builder().is_test(true).try_init();
    let rules = &[def_imply(), def_imply_flip(), double_neg_flip(), comm_or()];
    prove_something(
        "contrapositive",
        "(-> x y)",
        rules,
        &[
            "(-> x y)",
            "(| (~ x) y)",
            "(| (~ x) (~ (~ y)))",
            "(| (~ (~ y)) (~ x))",
            "(-> (~ y) (~ x))",
        ],
    );
}

#[test]
fn prove_chain() {
    let _ = env_logger::builder().is_test(true).try_init();
    let rules = &[
        // rules needed for contrapositive
        def_imply(),
        def_imply_flip(),
        double_neg_flip(),
        comm_or(),
        // and some others
        comm_and(),
        lem_imply(),
    ];
    prove_something(
        "chain",
        "(& (-> x y) (-> y z))",
        rules,
        &[
            "(& (-> x y) (-> y z))",
            "(& (-> (~ y) (~ x)) (-> y z))",
            "(& (-> y z)         (-> (~ y) (~ x)))",
            "(| z (~ x))",
            "(| (~ x) z)",
            "(-> x z)",
        ],
    );
}

type ConstantFold = Option<bool>;

impl Metadata<Prop> for ConstantFold {
    type Error = std::convert::Infallible;
    fn merge(&self, other: &Self) -> Self {
        println!("Merge");
        self.and(*other)
    }
    fn make(expr: Expr<Prop, &Self>) -> Self {
        let result = match &expr.op {
            Prop::Bool(c) => Some(*c),
            Prop::Variable(_) => None,
            op => {
                let a = |i: usize| *expr.children[i];
                Some(match op {
                    Prop::And => a(0)? && a(1)?,
                    Prop::Or => a(0)? || a(1)?,
                    Prop::Implies => a(1)? || !a(0)?,
                    Prop::Not => {
                        assert_eq!(expr.children.len(), 1);
                        !a(0)?
                    }
                    _ => panic!("Unknown op: {:?}", op),
                })
            }
        };
        println!("Make: {:?} -> {:?}", expr, result);
        result
    }
    fn modify(eclass: &mut EClass<Prop, Self>) {
        println!("Modifying: {:#?}", eclass);
        if let Some(c) = eclass.metadata {
            eclass.nodes.push(Expr::unit(Prop::Bool(c)))
        }
    }
}

#[test]
fn const_fold() {
    let start = "(| (& false true) (& true false))";
    let start_expr = Prop::parse_expr(start).unwrap();
    let end = "false";
    let end_expr = Prop::parse_expr(end).unwrap();
    let (eg, _) = EGraph::<Prop, ConstantFold>::from_expr(&start_expr);
    assert!(!eg.equivs(&start_expr, &end_expr).is_empty());
}
