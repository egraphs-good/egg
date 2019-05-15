use egg::{
    egraph::EGraph,
    expr::{Expr, Language, Name, QuestionMarkName},
    parse::ParsableLanguage,
    pattern::Rewrite,
};
use log::*;

use strum_macros::{Display, EnumString};

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct Prop;

#[derive(Debug, PartialEq, Eq, Hash, Clone, EnumString, Display)]
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

impl Language for Prop {
    type Constant = Bool;
    type Operator = Op;
    type Variable = Name;
    type Wildcard = QuestionMarkName;

    fn cost(_node: &Expr<Prop, u64>) -> u64 {
        unimplemented!()
    }

    fn eval(op: Op, args: &[Bool]) -> Bool {
        match op {
            Op::And => args.iter().fold(Bool::True, |x, y| conjoin(x, y.clone())),
            Op::Or => args.iter().fold(Bool::False, |x, y| disjoin(x, y.clone())),
            Op::Not => {
                assert_eq!(args.len(), 1);
                negate(args[0].clone())
            }
            Op::Implies => {
                assert_eq!(args.len(), 2);
                implies(args[0].clone(), args[1].clone())
            }
        }
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

    let (mut egraph, _old_root) = EGraph::from_expr(&start_expr);
    egraph.debug(true);

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
        if equivs.len() == 0 {
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

#[test]
fn evaluate() {
    assert_eq!(Prop::eval(Op::And, &[Bool::True, Bool::True]), Bool::True);
    assert_eq!(Prop::eval(Op::And, &[Bool::True, Bool::False]), Bool::False);
    assert_eq!(Prop::eval(Op::And, &[Bool::False, Bool::True]), Bool::False);
    assert_eq!(
        Prop::eval(Op::And, &[Bool::False, Bool::False]),
        Bool::False
    );

    assert_eq!(Prop::eval(Op::Or, &[Bool::True, Bool::True]), Bool::True);
    assert_eq!(Prop::eval(Op::Or, &[Bool::True, Bool::False]), Bool::True);
    assert_eq!(Prop::eval(Op::Or, &[Bool::False, Bool::True]), Bool::True);
    assert_eq!(Prop::eval(Op::Or, &[Bool::False, Bool::False]), Bool::False);

    assert_eq!(
        Prop::eval(Op::Implies, &[Bool::True, Bool::False]),
        Bool::False
    );
    assert_eq!(
        Prop::eval(Op::Implies, &[Bool::True, Bool::True]),
        Bool::True
    );
    assert_eq!(
        Prop::eval(Op::Implies, &[Bool::False, Bool::True]),
        Bool::True
    );
    assert_eq!(
        Prop::eval(Op::Implies, &[Bool::False, Bool::True]),
        Bool::True
    );

    assert_eq!(Prop::eval(Op::Not, &[Bool::True]), Bool::False);
    assert_eq!(Prop::eval(Op::Not, &[Bool::False]), Bool::True);
}

#[test]
fn const_fold() {
    let start = "(| (& F T) (& T F))";
    let start_expr = Prop.parse_expr(start).unwrap();
    let end = "F";
    let end_expr = Prop.parse_expr(end).unwrap();
    let (mut eg, _) = EGraph::from_expr(&start_expr);
    eg.dump_dot("constant_folding0.dot");
    assert_eq!(eg.fold_constants(), 2);
    eg.rebuild();
    eg.dump_dot("constant_folding1.dot");
    assert_eq!(eg.fold_constants(), 1);
    eg.rebuild();
    eg.dump_dot("constant_folding2.dot");
    assert!(!eg.equivs(&start_expr, &end_expr).is_empty());
}
