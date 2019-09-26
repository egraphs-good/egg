use egg::{
    define_term,
    egraph::{EClass, EGraph, Metadata},
    expr::{Expr, Language, Name},
    parse::ParsableLanguage,
    pattern::Rewrite,
};
use log::*;

define_term! {
    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    enum Prop {
        Bool(bool),
        And = "&",
        Not = "~",
        Or = "|",
        Implies = "->",
        Variable(Name),
    }
}

impl Language for Prop {
    fn cost(&self, _children: &[u64]) -> u64 {
        unimplemented!()
    }
}

macro_rules! rule {
    ($name:ident, $left:expr, $right:expr) => {
        #[allow(dead_code)]
        fn $name<M: Metadata<Prop>>() -> Rewrite<Prop, M> {
            trace!(
                "Building rule {} ==> {}",
                stringify!($left),
                stringify!($right)
            );
            Prop::parse_rewrite(stringify!($name), $left, $right).unwrap()
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

    let start_expr = Prop::parse_expr(start).unwrap();
    let goal_exprs: Vec<_> = goals.iter().map(|g| Prop::parse_expr(g).unwrap()).collect();

    let (mut egraph, _old_root) = EGraph::<Prop, ()>::from_expr(&start_expr);

    egraph.dump_dot(&format!("{}-1.dot", name));

    for _ in 0..20 {
        for rw in rewrites {
            rw.run(&mut egraph);
        }
        egraph.rebuild();
    }
    egraph.dump_dot(&format!("{}-2.dot", name));

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
