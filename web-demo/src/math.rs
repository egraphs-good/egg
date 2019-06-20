use egg::{
    egraph::{EGraph, Metadata},
    expr::{Expr, Language, Name, QuestionMarkName, RecExpr},
    parse::ParsableLanguage,
};
use ordered_float::NotNan;

use strum_macros::{Display, EnumString};

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Math;

#[derive(Debug, PartialEq, Eq, Hash, Clone, EnumString, Display)]
pub enum Op {
    #[strum(serialize = "+")]
    Add,
    #[strum(serialize = "-")]
    Sub,
    #[strum(serialize = "*")]
    Mul,
    #[strum(serialize = "/")]
    Div,
    #[strum(serialize = "pow")]
    Pow,
    #[strum(serialize = "exp")]
    Exp,
    #[strum(serialize = "log")]
    Log,
    #[strum(serialize = "sqrt")]
    Sqrt,
    #[strum(serialize = "cbrt")]
    Cbrt,
    #[strum(serialize = "fabs")]
    Fabs,
}

impl Language for Math {
    type Constant = NotNan<f64>;
    type Operator = Op;
    type Variable = Name;
    type Wildcard = QuestionMarkName;

    fn cost(node: &Expr<Math, u64>) -> u64 {
        match node {
            Expr::Constant(_) | Expr::Variable(_) => 1,
            Expr::Operator(op, child_costs) => {
                let cost = match op {
                    Op::Add => 40,
                    Op::Sub => 40,
                    Op::Mul => 40,
                    Op::Div => 40,
                    Op::Pow => 210,
                    Op::Exp => 70,
                    Op::Log => 70,
                    Op::Sqrt => 40,
                    Op::Cbrt => 80,
                    Op::Fabs => 40,
                };
                cost + child_costs.iter().sum::<u64>()
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct BestExpr {
    pub cost: u64,
    pub expr: RecExpr<Math>,
}

impl Metadata<Math> for BestExpr {
    type Error = std::convert::Infallible;
    fn merge(&self, other: &Self) -> Self {
        if other.cost < self.cost {
            other.clone()
        } else {
            self.clone()
        }
    }
    fn make(expr: Expr<Math, &Self>) -> Self {
        let cost = match &expr {
            Expr::Constant(_) | Expr::Variable(_) => 1,
            Expr::Operator(op, children) => {
                let cost = match op {
                    Op::Add => 40,
                    Op::Sub => 40,
                    Op::Mul => 40,
                    Op::Div => 40,
                    Op::Pow => 210,
                    Op::Exp => 70,
                    Op::Log => 70,
                    Op::Sqrt => 40,
                    Op::Cbrt => 80,
                    Op::Fabs => 40,
                };
                cost + children.iter().map(|best| best.cost).sum::<u64>()
            }
        };

        let expr: RecExpr<Math> = expr.map_children(|b| b.expr.clone()).into();
        BestExpr { cost, expr }
    }
}

pub type MathEGraph = EGraph<Math, BestExpr>;

use crate::{OptionalRewrite, RewriteGroup};

fn mk_rules(tuples: &[(&str, &str, &str)]) -> Vec<OptionalRewrite> {
    tuples
        .iter()
        .map(|(name, left, right)| {
            let rw = Math.parse_rewrite(name, left, right).unwrap();
            OptionalRewrite::new(rw)
        })
        .collect()
}

#[rustfmt::skip]
pub(crate) fn rules() -> Vec<RewriteGroup> {
    let mut groups = Vec::default();
    let mut add = |name: &str, rules| {
        groups.push(RewriteGroup {
            name: name.into(),
            enabled: true,
            rewrites: mk_rules(rules)
        });
    };

    add(
        "commutativity",
        &[
            ("+-commutative", "(+ ?a ?b)", "(+ ?b ?a)"),
            ("*-commutative", "(* ?a ?b)", "(* ?b ?a)"),
        ],
    );
    add(
        "associativity",
        &[
            ("associate-+r+", "(+ ?a (+ ?b ?c))", "(+ (+ ?a ?b) ?c)"),
            ("associate-+l+", "(+ (+ ?a ?b) ?c)", "(+ ?a (+ ?b ?c))"),
            ("associate-+r-", "(+ ?a (- ?b ?c))", "(- (+ ?a ?b) ?c)"),
            ("associate-+l-", "(+ (- ?a ?b) ?c)", "(- ?a (- ?b ?c))"),
            ("associate--r+", "(- ?a (+ ?b ?c))", "(- (- ?a ?b) ?c)"),
            ("associate--l+", "(- (+ ?a ?b) ?c)", "(+ ?a (- ?b ?c))"),
            ("associate--l-", "(- (- ?a ?b) ?c)", "(- ?a (+ ?b ?c))"),
            ("associate--r-", "(- ?a (- ?b ?c))", "(+ (- ?a ?b) ?c)"),
            ("associate-*r*", "(* ?a (* ?b ?c))", "(* (* ?a ?b) ?c)"),
            ("associate-*l*", "(* (* ?a ?b) ?c)", "(* ?a (* ?b ?c))"),
            ("associate-*r/", "(* ?a (/ ?b ?c))", "(/ (* ?a ?b) ?c)"),
            ("associate-*l/", "(* (/ ?a ?b) ?c)", "(/ (* ?a ?c) ?b)"),
            ("associate-/r*", "(/ ?a (* ?b ?c))", "(/ (/ ?a ?b) ?c)"),
            ("associate-/l*", "(/ (* ?b ?c) ?a)", "(/ ?b (/ ?a ?c))"),
            ("associate-/r/", "(/ ?a (/ ?b ?c))", "(* (/ ?a ?b) ?c)"),
            ("associate-/l/", "(/ (/ ?b ?c) ?a)", "(/ ?b (* ?a ?c))"),
        ],
    );
    add(
        "distributivity",
        &[
            ("distribute-lft-in",    "(* ?a (+ ?b ?c))",        "(+ (* ?a ?b) (* ?a ?c))"),
            ("distribute-rgt-in",    "(* ?a (+ ?b ?c))",        "(+ (* ?b ?a) (* ?c ?a))"),
            ("distribute-lft-out",   "(+ (* ?a ?b) (* ?a ?c))", "(* ?a (+ ?b ?c))"),
            ("distribute-lft-out--", "(- (* ?a ?b) (* ?a ?c))", "(* ?a (- ?b ?c))"),
            ("distribute-rgt-out",   "(+ (* ?b ?a) (* ?c ?a))", "(* ?a (+ ?b ?c))"),
            ("distribute-rgt-out--", "(- (* ?b ?a) (* ?c ?a))", "(* ?a (- ?b ?c))"),
            ("distribute-lft1-in",   "(+ (* ?b ?a) ?a)",        "(* (+ ?b 1) ?a)"),
            ("distribute-rgt1-in",   "(+ ?a (* ?c ?a))",        "(* (+ ?c 1) ?a)"),
        ],
    );
    add(
        "distributivity-fp-safe",
        &[
            ("distribute-lft-neg-in",  "(- 0 (* ?a ?b))",     "(* (- 0 ?a) ?b)"),
            ("distribute-rgt-neg-in",  "(- 0 (* ?a ?b))",     "(* ?a (- 0 ?b))"),
            ("distribute-lft-neg-out", "(* (- 0 ?a) ?b)",     "(- 0 (* ?a ?b))"),
            ("distribute-rgt-neg-out", "(* ?a (- 0 ?b))",     "(- 0 (* ?a ?b))"),
            ("distribute-neg-in",      "(- 0 (+ ?a ?b))",     "(+ (- 0 ?a) (- 0 ?b))"),
            ("distribute-neg-out",     "(+ (- 0 ?a) (- 0 ?b))", "(- 0 (+ ?a ?b))"),
            ("distribute-frac-neg",    "(/ (- 0 ?a) ?b)",     "(- 0 (/ ?a ?b))"),
            ("distribute-neg-frac",    "(- 0 (/ ?a ?b))",     "(/ (- 0 ?a) ?b)"),
        ],
    );

    add(
        "difference-of-squares-canonicalize",
        &[
            ("swap-sqr",              "(* (* ?a ?b) (* ?a ?b))",     "(* (* ?a ?a) (* ?b ?b))"),
            ("unswap-sqr",            "(* (* ?a ?a) (* ?b ?b))",     "(* (* ?a ?b) (* ?a ?b))"),
            ("difference-of-squares", "(- (* ?a ?a) (* ?b ?b))",     "(* (+ ?a ?b) (- ?a ?b))"),
            ("difference-of-sqr-1",   "(- (* ?a ?a) 1)",           "(* (+ ?a 1) (- ?a 1))"),
            ("difference-of-sqr--1",  "(+ (* ?a ?a) -1)",          "(* (+ ?a 1) (- ?a 1))"),
            ("sqr-pow",               "(pow ?a ?b)",               "(* (pow ?a (/ ?b 2)) (pow ?a (/ ?b 2)))"),
            ("pow-sqr",               "(* (pow ?a ?b) (pow ?a ?b))", "(pow ?a (* 2 ?b))"),
        ],
    );

    add(
        "id-reduce",
        &[
            ("remove-double-div", "(/ 1 (/ 1 ?a))",         "?a"),
            ("rgt-mult-inverse",  "(* ?a (/ 1 ?a))",         "1"),
            ("lft-mult-inverse", "(* (/ 1 ?a) ?a)", "1"),
        ],
    );

    add(
        "id-expand",
        &[
            ("mul-expand", "?a", "(* 1 ?a)"),
        ],
    );

    add(
        "id-reduce-fp-safe-nan",
        &[
            ("+-inverses",        "(- ?a ?a)",               "0"),
            ("*-inverses",        "(/ ?a ?a)",               "1"),
            ("div0",              "(/ 0 ?a)",               "0"),
            ("mul0",              "(* 0 ?a)",               "0"),
            ("mul0", "(* ?a 0)", "0"),
        ],
    );

    add(
        "id-reduce-fp-safe",
        &[
            ("+-lft-identity",    "(+ 0 ?a)",   "?a"),
            ("+-rgt-identity",    "(+ ?a 0)",   "?a"),
            ("--rgt-identity",    "(- ?a 0)",   "?a"),
            // ("sub0-neg",          "(- 0 ?a)",   "(- ?a)"),
            ("remove-double-neg", "(- 0 (- 0 ?a))", "?a"),
            ("*-lft-identity",    "(* 1 ?a)",   "?a"),
            ("*-rgt-identity",    "(* ?a 1)",   "?a"),
            ("/-rgt-identity",    "(/ ?a 1)",   "?a"),
            ("mul-1-neg",         "(* -1 ?a)",  "(- 0 ?a)"),
        ],
    );

    add(
        "fractions-distribute",
        &[
            ("div-sub",    "(/ (- ?a ?b) ?c)",       "(- (/ ?a ?c) (/ ?b ?c))"),
            ("times-frac", "(/ (* ?a ?b) (* ?c ?d))", "(* (/ ?a ?c) (/ ?b ?d))"),
        ],
    );

    add(
        "squares-reduce",
        &[
            ("rem-square-sqrt", "(* (sqrt ?x) (sqrt ?x))",     "?x"),
            ("rem-sqrt-square", "(sqrt (* ?x ?x))",            "(fabs ?x)"),
        ],
    );

    add(
        "squares-reduce-fp-sound",
        &[
            ("sqr-neg", "(* (- 0 ?x) (- 0 ?x))", "(* ?x ?x)"),
        ],
    );

    add(
        "cubes-reduce",
        &[
            ("rem-cube-cbrt",     "(pow (cbrt ?x) 3)", "?x"),
            ("rem-cbrt-cube",     "(cbrt (pow ?x 3))", "?x"),
            ("cube-neg",          "(pow (- 0 ?x) 3)",    "(- 0 (pow ?x 3))"),
        ],
    );

    add(
        "cubes-distribute",
        &[
            ("cube-prod", "(pow (* ?x ?y) 3)", "(* (pow ?x 3) (pow ?y 3))"),
            ("cube-div",  "(pow (/ ?x ?y) 3)", "(/ (pow ?x 3) (pow ?y 3))"),
            ("cube-mult", "(pow ?x 3)",       "(* ?x (* ?x ?x))"),
        ],
    );

    add(
        "cubes-canonicalize",
        &[
            ("cube-unmult", "(* ?x (* ?x ?x))", "(pow ?x 3)"),
        ],
    );

    add(
        "exp-reduce",
        &[
            ("rem-exp-log", "(exp (log ?x))", "?x"),
            ("rem-log-exp", "(log (exp ?x))", "?x"),
        ],
    );

    add(
        "exp-reduce-fp-safe",
        &[
            ("exp-0",   "(exp 0)", "1"),
            // ("1-exp",   "1",       "(exp 0)"),
            // ("exp-1-e", "(exp 1)", "E"),
            // ("e-exp-1", "E",       "(exp 1)"),
        ],
    );

    add(
        "exp-distribute",
        &[
            ("exp-sum",  "(exp (+ ?a ?b))", "(* (exp ?a) (exp ?b))"),
            ("exp-neg",  "(exp (- 0 ?a))",  "(/ 1 (exp ?a))"),
            ("exp-diff", "(exp (- ?a ?b))", "(/ (exp ?a) (exp ?b))"),
        ],
    );

    add(
        "exp-factor",
        &[
            ("prod-exp",     "(* (exp ?a) (exp ?b))",  "(exp (+ ?a ?b))"),
            ("rec-exp",      "(/ 1 (exp ?a))",        "(exp (- 0 ?a))"),
            ("div-exp",      "(/ (exp ?a) (exp ?b))",  "(exp (- ?a ?b))"),
            ("exp-prod",     "(exp (* ?a ?b))",        "(pow (exp ?a) ?b)"),
            ("exp-sqrt",     "(exp (/ ?a 2))",        "(sqrt (exp ?a))"),
            ("exp-cbrt",     "(exp (/ ?a 3))",        "(cbrt (exp ?a))"),
            ("exp-lft-sqr",  "(exp (* ?a 2))",        "(* (exp ?a) (exp ?a))"),
            ("exp-lft-cube", "(exp (* ?a 3))",        "(pow (exp ?a) 3)"),
        ],
    );

    add(
        "pow-reduce",
        &[
            ("unpow-1", "(pow ?a -1)", "(/ 1 ?a)"),
        ],
    );

    add(
        "pow-reduce-fp-safe",
        &[
            ("unpow1",         "(pow ?a 1)",                  "?a"),
        ],
    );

    add(
        "pow-reduce-fp-safe-nan",
        &[
            ("unpow0",         "(pow ?a 0)",                  "1"),
            ("pow-base-1",     "(pow 1 ?a)",                  "1"),
        ],
    );

    add(
        "pow-canonicalize",
        &[
            ("exp-to-pow",      "(exp (* (log ?a) ?b))",        "(pow ?a ?b)"),
            ("pow-plus",        "(* (pow ?a ?b) ?a)",            "(pow ?a (+ ?b 1))"),
            // ("unpow1/2",        "(pow ?a 1/2)",                "(sqrt ?a)"),
            ("unpow2",          "(pow ?a 2)",                  "(* ?a ?a)"),
            ("unpow3",          "(pow ?a 3)",                  "(* (* ?a ?a) ?a)"),
            // ("unpow1/3", "(pow ?a 1/3)", "(cbrt ?a)"),
        ],
    );

    add(
        "log-distribute",
        &[
            ("log-prod",     "(log (* ?a ?b))",       "(+ (log ?a) (log ?b))"),
            ("log-div",      "(log (/ ?a ?b))",       "(- (log ?a) (log ?b))"),
            ("log-rec",      "(log (/ 1 ?a))",       "(- 0 (log ?a))"),
            ("log-pow",      "(log (pow ?a ?b))",     "(* ?b (log ?a))"),
        ],
    );

    groups
}
