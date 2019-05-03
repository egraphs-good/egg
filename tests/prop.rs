use ears::{
    egraph::EGraph,
    expr::{Expr, Id, Language, Name, QuestionMarkName},
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

    fn cost(_node: &Expr<Prop, Id>) -> u64 {
        unimplemented!()
    }
}

macro_rules! rule {
    ($name:ident, $left:expr, $right:expr) => {
        fn $name() -> Rewrite<Prop> {
            trace!(
                "Building rule {} ==> {}",
                stringify!($left),
                stringify!($right)
            );
            Prop.parse_rewrite($left, $right).unwrap()
        }
    };
}

rule! {def_imply,   "(-> ?a ?b)",       "(| (~ ?a) ?b)"          }
rule! {double_neg,  "(~ (~ ?a))",       "?a"                     }
rule! {assoc_or,    "(| ?a (| ?b ?c))", "(| (| ?a ?b) ?c)"       }
rule! {dist_and_or, "(& ?a (| ?b ?c))", "(| (& ?a ?b) (& ?a ?c))"}
rule! {comm_or,     "(| ?a ?b)",        "(| ?b ?a)"              }

fn prove_something(name: &str, start: &str, goal: &str, rewrites: &[Rewrite<Prop>]) {
    let _ = env_logger::builder().is_test(true).try_init();

    let start_expr = Prop.parse_expr(start).unwrap();
    let goal_expr = Prop.parse_expr(goal).unwrap();

    let (mut egraph, _old_root) = EGraph::from_expr(&start_expr);

    egraph.dump_dot(&format!("{}-1.dot", name));

    for _ in 0..20 {
        for rw in rewrites {
            rw.run(&mut egraph);
        }
    }
    egraph.dump_dot(&format!("{}-2.dot", name));

    // eprintln!("{:#?}", egraph.nodes);

    let equivs = egraph.equivs(&start_expr, &goal_expr);
    assert!(equivs.len() > 0);
}

#[test]
fn prove_contrapositive() {
    // a -> b
    // ~a | b
    // ~a | ~~b
    // ~~b | ~a
    // ~b -> ~a
    let rules = &[
        def_imply(),
        def_imply().flip(),
        double_neg(),
        double_neg().flip(),
        comm_or(),
    ];
    prove_something("contrapositive", "(-> x y)", "(-> (~ y) (~ x))", rules);
}

#[ignore = "failing"]
#[test]
fn prove_chain() {
    let rules = &[
        def_imply(),
        def_imply().flip(),
        double_neg(),
        double_neg().flip(),
        comm_or(),
        assoc_or(),
        dist_and_or(),
    ];
    prove_something("chain", "(& (-> x y) (-> y z))", "(-> y z)", rules);
}
