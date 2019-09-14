use egg::{
    egraph::{EClass, EGraph, Metadata},
    expr::{Expr, Language, Name, QuestionMarkName},
    parse::ParsableLanguage,
    pattern::Rewrite,
};
use log::*;
use std::str::FromStr;

use strum_macros::{Display, EnumString};

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct Prop;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, EnumString, Display)]
enum Bool {
    #[strum(serialize = "T")]
    True,
    #[strum(serialize = "F")]
    False,
}

fn conjoin(x: Bool, y: Bool) -> Bool {
    if (x == Bool::True) && (y == Bool::True) {
        Bool::True
    } else {
        Bool::False
    }
}

fn disjoin(x: Bool, y: Bool) -> Bool {
    if (x == Bool::True) || (y == Bool::True) {
        Bool::True
    } else {
        Bool::False
    }
}

fn negate(x: Bool) -> Bool {
    if x == Bool::True {
        Bool::False
    } else {
        Bool::True
    }
}

fn implies(x: Bool, y: Bool) -> Bool {
    disjoin(y, negate(x))
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, EnumString, Display)]
enum Op {
    #[strum(serialize = "&")]
    And,
    #[strum(serialize = "~")]
    Not,
    #[strum(serialize = "|")]
    Or,
    #[strum(serialize = "->")]
    Implies,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Display)]
enum Term {
    Bool(Bool),
    Op(Op),
    Variable(Name),
}

type BoxedErr = Box<dyn std::error::Error>;
impl FromStr for Term {
    type Err = BoxedErr;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse()
            .map(Term::Bool)
            .map_err(BoxedErr::from)
            .or_else(|_| s.parse().map(Term::Op).map_err(BoxedErr::from))
            .or_else(|_| s.parse().map(Term::Variable).map_err(BoxedErr::from))
    }
}

impl Language for Prop {
    type Term = Term;
    type Wildcard = QuestionMarkName;

    fn cost(_node: &Expr<Prop, u64>) -> u64 {
        unimplemented!()
    }
}

macro_rules! rule {
    ($name:ident, $left:expr, $right:expr) => {
        #[allow(dead_code)]
        fn $name() -> Rewrite<Prop> {
            trace!(
                "Building rule {} ==> {}",
                stringify!($left),
                stringify!($right)
            );
            Prop.parse_rewrite(stringify!($name), $left, $right)
                .unwrap()
        }
    };
}

rule! {def_imply,   "(-> ?a ?b)",       "(| (~ ?a) ?b)"          }
rule! {double_neg,  "(~ (~ ?a))",       "?a"                     }
rule! {assoc_or,    "(| ?a (| ?b ?c))", "(| (| ?a ?b) ?c)"       }
rule! {dist_and_or, "(& ?a (| ?b ?c))", "(| (& ?a ?b) (& ?a ?c))"}
rule! {dist_or_and, "(| ?a (& ?b ?c))", "(& (| ?a ?b) (| ?a ?c))"}
rule! {comm_or,     "(| ?a ?b)",        "(| ?b ?a)"              }
rule! {comm_and,    "(& ?a ?b)",        "(& ?b ?a)"              }
rule! {lem,         "(| ?a (~ ?a))",    "T"                      }
rule! {or_true,     "(| ?a T)",         "T"                      }
rule! {and_true,    "(& ?a T)",         "?a"                     }
rule! {contrapositive, "(-> ?a ?b)",    "(-> (~ ?b) (~ ?a))"     }
rule! {lem_imply, "(& (-> ?a ?b) (-> (~ ?a) ?c))", "(| ?b ?c)"}

fn prove_something(name: &str, start: &str, rewrites: &[Rewrite<Prop>], goals: &[&str]) {
    let _ = env_logger::builder().is_test(true).try_init();

    let start_expr = Prop.parse_expr(start).unwrap();
    let goal_exprs: Vec<_> = goals.iter().map(|g| Prop.parse_expr(g).unwrap()).collect();

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
    let rules = &[
        def_imply(),
        def_imply().flip(),
        double_neg().flip(),
        comm_or(),
    ];
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
        def_imply().flip(),
        double_neg().flip(),
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

type ConstantFold = Option<Bool>;

impl Metadata<Prop> for ConstantFold {
    type Error = std::convert::Infallible;
    fn merge(&self, other: &Self) -> Self {
        println!("Merge");
        self.and(*other)
    }
    fn make(expr: Expr<Prop, &Self>) -> Self {
        let result = match &expr.t {
            Term::Bool(c) => Some(*c),
            Term::Variable(_) => None,
            Term::Op(op) => {
                let args = &expr.children;
                fn map2<T>(a: Option<T>, b: Option<T>, f: impl Fn(T, T) -> T) -> Option<T> {
                    a.and_then(|a| b.map(|b| f(a, b)))
                }

                match op {
                    Op::And => map2(*args[0], *args[1], conjoin),
                    Op::Or => map2(*args[0], *args[1], disjoin),
                    Op::Implies => map2(*args[0], *args[1], implies),
                    Op::Not => {
                        assert_eq!(args.len(), 1);
                        args[0].map(negate)
                    }
                }
            }
        };
        println!("Make: {:?} -> {:?}", expr, result);
        result
    }
    fn modify(eclass: &mut EClass<Prop, Self>) {
        println!("Modifying: {:#?}", eclass);
        if let Some(c) = eclass.metadata {
            eclass.nodes.push(Expr::unit(Term::Bool(c)))
        }
    }
}

#[test]
fn const_fold() {
    let start = "(| (& F T) (& T F))";
    let start_expr = Prop.parse_expr(start).unwrap();
    let end = "F";
    let end_expr = Prop.parse_expr(end).unwrap();
    let (eg, _) = EGraph::<Prop, ConstantFold>::from_expr(&start_expr);
    assert!(!eg.equivs(&start_expr, &end_expr).is_empty());
}
