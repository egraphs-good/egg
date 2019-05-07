use ears::{
    egraph::EGraph,
    expr::{Expr, Id, Language, Name, QuestionMarkName},
    extract::Extractor,
    parse::ParsableLanguage,
    pattern::Rewrite,
    util::HashMap,
};
use log::*;
use ordered_float::NotNan;

use strum_macros::{Display, EnumString};

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct Math;

#[derive(Debug, PartialEq, Eq, Hash, Clone, EnumString, Display)]
enum Op {
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

    fn cost(_node: &Expr<Math, Id>) -> u64 {
        1
    }
}

static EXP: &str = r#"
(/
 (*
  (*
   (*
    (pow
     (/ 1 (+ 1 (exp (- 0 s))))
     c_p)
    (pow
     (- 1 (/ 1 (+ 1 (exp (- 0 s)))))
     c_n))
   (*
    (pow
     (/ 1 (+ 1 (exp (- 0 s))))
     c_p)
    (pow
     (- 1 (/ 1 (+ 1 (exp (- 0 s)))))
     c_n)))
  (*
   (pow
    (/ 1 (+ 1 (exp (- 0 s))))
    c_p)
   (pow
    (- 1 (/ 1 (+ 1 (exp (- 0 s)))))
    c_n)))
 (*
  (*
   (*
    (pow
     (/ 1 (+ 1 (exp (- 0 t))))
     c_p)
    (pow
     (- 1 (/ 1 (+ 1 (exp (- 0 t)))))
     c_n))
   (*
    (pow
     (/ 1 (+ 1 (exp (- 0 t))))
     c_p)
    (pow
     (- 1 (/ 1 (+ 1 (exp (- 0 t)))))
     c_n)))
  (*
   (pow
    (/ 1 (+ 1 (exp (- 0 t))))
    c_p)
   (pow
    (- 1 (/ 1 (+ 1 (exp (- 0 t)))))
    c_n))))
"#;

fn mk_rules(tuples: &[(&str, &str, &str)]) -> Vec<Rewrite<Math>> {
    tuples
        .iter()
        .map(|(name, left, right)| Math.parse_rewrite(name, left, right).unwrap())
        .collect()
}

#[rustfmt::skip]
fn rules() -> HashMap<&'static str, Vec<Rewrite<Math>>> {
    let mut m = HashMap::default();
    m.insert(
        "commutativity",
        mk_rules(&[
            ("+-commutative", "(+ ?a ?b)", "(+ ?b ?a)"),
            ("*-commutative", "(* ?a ?b)", "(* ?b ?a)"),
        ]),
    );
    m.insert(
        "associativity",
        mk_rules(&[
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
        ]),
    );
    m.insert(
        "distributivity",
        mk_rules(&[
            ("distribute-lft-in",    "(* ?a (+ ?b ?c))",        "(+ (* ?a ?b) (* ?a ?c))"),
            ("distribute-rgt-in",    "(* ?a (+ ?b ?c))",        "(+ (* ?b ?a) (* ?c ?a))"),
            ("distribute-lft-out",   "(+ (* ?a ?b) (* ?a ?c))", "(* ?a (+ ?b ?c))"),
            ("distribute-lft-out--", "(- (* ?a ?b) (* ?a ?c))", "(* ?a (- ?b ?c))"),
            ("distribute-rgt-out",   "(+ (* ?b ?a) (* ?c ?a))", "(* ?a (+ ?b ?c))"),
            ("distribute-rgt-out--", "(- (* ?b ?a) (* ?c ?a))", "(* ?a (- ?b ?c))"),
            ("distribute-lft1-in",   "(+ (* ?b ?a) ?a)",        "(* (+ ?b 1) ?a)"),
            ("distribute-rgt1-in",   "(+ ?a (* ?c ?a))",        "(* (+ ?c 1) ?a)"),
        ]),
    );
    m.insert(
        "distributivity",
        mk_rules(&[
            ("distribute-lft-neg-in",  "(- 0 (* ?a ?b))",     "(* (- 0 ?a) ?b)"),
            ("distribute-rgt-neg-in",  "(- 0 (* ?a ?b))",     "(* ?a (- 0 ?b))"),
            ("distribute-lft-neg-out", "(* (- 0 ?a) ?b)",     "(- 0 (* ?a ?b))"),
            ("distribute-rgt-neg-out", "(* ?a (- 0 ?b))",     "(- 0 (* ?a ?b))"),
            ("distribute-neg-in",      "(- 0 (+ ?a ?b))",     "(+ (- 0 ?a) (- 0 ?b))"),
            ("distribute-neg-out",     "(+ (- 0 ?a) (- 0 ?b))", "(- 0 (+ ?a ?b))"),
            ("distribute-frac-neg",    "(/ (- 0 ?a) ?b)",     "(- 0 (/ ?a ?b))"),
            ("distribute-neg-frac",    "(- 0 (/ ?a ?b))",     "(/ (- 0 ?a) ?b)"),
        ]),
    );

    m.insert(
        "difference-of-squares-canonicalize",
        mk_rules(&[
            ("swap-sqr",              "(* (* ?a ?b) (* ?a ?b))",     "(* (* ?a ?a) (* ?b ?b))"),
            ("unswap-sqr",            "(* (* ?a ?a) (* ?b ?b))",     "(* (* ?a ?b) (* ?a ?b))"),
            ("difference-of-squares", "(- (* ?a ?a) (* ?b ?b))",     "(* (+ ?a ?b) (- ?a ?b))"),
            ("difference-of-sqr-1",   "(- (* ?a ?a) 1)",           "(* (+ ?a 1) (- ?a 1))"),
            ("difference-of-sqr--1",  "(+ (* ?a ?a) -1)",          "(* (+ ?a 1) (- ?a 1))"),
            ("sqr-pow",               "(pow ?a ?b)",               "(* (pow ?a (/ ?b 2)) (pow ?a (/ ?b 2)))"),
            ("pow-sqr",               "(* (pow ?a ?b) (pow ?a ?b))", "(pow ?a (* 2 ?b))"),
        ]),
    );

    m.insert(
        "id-reduce",
        mk_rules(&[
            ("remove-double-div", "(/ 1 (/ 1 ?a))",         "?a"),
            ("rgt-mult-inverse",  "(* ?a (/ 1 ?a))",         "1"),
            ("lft-mult-inverse", "(* (/ 1 ?a) ?a)", "1"),
        ]),
    );

    m.insert(
        "id-reduce-fp-safe-nan",
        mk_rules(&[
            ("+-inverses",        "(- ?a ?a)",               "0"),
            ("*-inverses",        "(/ ?a ?a)",               "1"),
            ("div0",              "(/ 0 ?a)",               "0"),
            ("mul0",              "(* 0 ?a)",               "0"),
            ("mul0", "(* ?a 0)", "0"),
        ]),
    );

    m.insert(
        "id-reduce-fp-safe",
        mk_rules(&[
            ("+-lft-identity",    "(+ 0 ?a)",   "?a"),
            ("+-rgt-identity",    "(+ ?a 0)",   "?a"),
            ("--rgt-identity",    "(- ?a 0)",   "?a"),
            // ("sub0-neg",          "(- 0 ?a)",   "(- ?a)"),
            ("remove-double-neg", "(- 0 (- 0 ?a))", "?a"),
            ("*-lft-identity",    "(* 1 ?a)",   "?a"),
            ("*-rgt-identity",    "(* ?a 1)",   "?a"),
            ("/-rgt-identity",    "(/ ?a 1)",   "?a"),
            ("mul-1-neg",         "(* -1 ?a)",  "(- 0 ?a)"),
        ]),
    );

    m.insert(
        "fractions-distribute",
        mk_rules(&[
            ("div-sub",    "(/ (- ?a ?b) ?c)",       "(- (/ ?a ?c) (/ ?b ?c))"),
            ("times-frac", "(/ (* ?a ?b) (* ?c d))", "(* (/ ?a ?c) (/ ?b d))"),
        ]),
    );

    m.insert(
        "squares-reduce",
        mk_rules(&[
            ("rem-square-sqrt", "(* (sqrt ?x) (sqrt ?x))",     "?x"),
            ("rem-sqrt-square", "(sqrt (* ?x ?x))",            "(fabs ?x)"),
        ]),
    );

    m.insert(
        "squares-reduce-fp-sound",
        mk_rules(&[
            ("sqr-neg", "(* (- 0 ?x) (- 0 ?x))", "(* ?x ?x)"),
        ]),
    );

    m.insert(
        "cubes-reduce",
        mk_rules(&[
            ("rem-cube-cbrt",     "(pow (cbrt ?x) 3)", "?x"),
            ("rem-cbrt-cube",     "(cbrt (pow ?x 3))", "?x"),
            ("cube-neg",          "(pow (- 0 ?x) 3)",    "(- 0 (pow ?x 3))"),
        ]),
    );

    m.insert(
        "cubes-distribute",
        mk_rules(&[
            ("cube-prod", "(pow (* ?x ?y) 3)", "(* (pow ?x 3) (pow ?y 3))"),
            ("cube-div",  "(pow (/ ?x ?y) 3)", "(/ (pow ?x 3) (pow ?y 3))"),
            ("cube-mult", "(pow ?x 3)",       "(* ?x (* ?x ?x))"),
        ]),
    );

    m.insert(
        "cubes-canonicalize",
        mk_rules(&[
            ("cube-unmult", "(* ?x (* ?x ?x))", "(pow ?x 3)"),
        ]),
    );

    m.insert(
        "exp-reduce",
        mk_rules(&[
            ("rem-exp-log", "(exp (log ?x))", "?x"),
            ("rem-log-exp", "(log (exp ?x))", "?x"),
        ]),
    );

    // m.insert(
    //     "exp-reduce-fp-safe",
    //     mk_rules(&[
    //         ("exp-0",   "(exp 0)", "1"),
    //         ("1-exp",   "1",       "(exp 0)"),
    //         ("exp-1-e", "(exp 1)", "E"),
    //         ("e-exp-1", "E",       "(exp 1)"),
    //     ]),
    // );

    m.insert(
        "exp-distribute",
        mk_rules(&[
            ("exp-sum",  "(exp (+ ?a ?b))", "(* (exp ?a) (exp ?b))"),
            ("exp-neg",  "(exp (- 0 ?a))",   "(/ 1 (exp ?a))"),
            ("exp-diff", "(exp (- ?a ?b))", "(/ (exp ?a) (exp ?b))"),
        ]),
    );

    m.insert(
        "exp-factor",
        mk_rules(&[
            ("prod-exp",     "(* (exp ?a) (exp ?b))",  "(exp (+ ?a ?b))"),
            ("rec-exp",      "(/ 1 (exp ?a))",        "(exp (- 0 ?a))"),
            ("div-exp",      "(/ (exp ?a) (exp ?b))",  "(exp (- ?a ?b))"),
            ("exp-prod",     "(exp (* ?a ?b))",        "(pow (exp ?a) ?b)"),
            ("exp-sqrt",     "(exp (/ ?a 2))",        "(sqrt (exp ?a))"),
            ("exp-cbrt",     "(exp (/ ?a 3))",        "(cbrt (exp ?a))"),
            ("exp-lft-sqr",  "(exp (* ?a 2))",        "(* (exp ?a) (exp ?a))"),
            ("exp-lft-cube", "(exp (* ?a 3))",        "(pow (exp ?a) 3)"),
        ]),
    );

    m.insert(
        "pow-reduce",
        mk_rules(&[
            ("unpow-1", "(pow ?a -1)", "(/ 1 ?a)"),
        ]),
    );

    m.insert(
        "pow-reduce-fp-safe",
        mk_rules(&[
            ("unpow1",         "(pow ?a 1)",                  "?a"),
        ]),
    );

    m.insert(
        "pow-reduce-fp-safe-nan",
        mk_rules(&[
            ("unpow0",         "(pow ?a 0)",                  "1"),
            ("pow-base-1",     "(pow 1 ?a)",                  "1"),
        ]),
    );

    // m.insert(
    //     "pow-canonicalize",
    //     mk_rules(&[
    //         ("exp-to-pow",      "(exp (* (log ?a) ?b))",        "(pow ?a ?b)"),
    //         ("pow-plus",        "(* (pow ?a ?b) ?a)",            "(pow ?a (+ ?b 1))"),
    //         ("unpow1/2",        "(pow ?a 1/2)",                "(sqrt ?a)"),
    //         ("unpow2",          "(pow ?a 2)",                  "(* ?a ?a)"),
    //         ("unpow3",          "(pow ?a 3)",                  "(* (* ?a ?a) ?a)"),
    //         ("unpow1/3", "(pow ?a 1/3)", "(cbrt ?a)"),
    //     ]),
    // );

    m.insert(
        "log-distribute",
        mk_rules(&[
            ("log-prod",     "(log (* ?a ?b))",       "(+ (log ?a) (log ?b))"),
            ("log-div",      "(log (/ ?a ?b))",       "(- (log ?a) (log ?b))"),
            ("log-rec",      "(log (/ 1 ?a))",       "(- 0 (log ?a))"),
            ("log-pow",      "(log (pow ?a ?b))",     "(* ?b (log ?a))"),
        ]),
    );

    // m.insert(
    //     "log-distribute-fp-safe",
    //     mk_rules(&[
    //         ("log-E", "(log E)", "1"),
    //     ]),
    // );

    // m.insert(
    //     "trig-reduce",
    //     mk_rules(&[
    //         ("cos-sin-sum", "(+ (* (cos ?a) (cos ?a)) (* (sin ?a) (sin ?a)))", "1"),
    //         ("1-sub-cos",   "(- 1 (* (cos ?a) (cos ?a)))",   "(* (sin ?a) (sin ?a))"),
    //         ("1-sub-sin",   "(- 1 (* (sin ?a) (sin ?a)))",   "(* (cos ?a) (cos ?a))"),
    //         ("-1-add-cos",  "(+ (* (cos ?a) (cos ?a)) -1)",  "(- (* (sin ?a) (sin ?a)))"),
    //         ("-1-add-sin",  "(+ (* (sin ?a) (sin ?a)) -1)",  "(- (* (cos ?a) (cos ?a)))"),
    //         ("sub-1-cos",   "(- (* (cos ?a) (cos ?a)) 1)",   "(- (* (sin ?a) (sin ?a)))"),
    //         ("sub-1-sin",   "(- (* (sin ?a) (sin ?a)) 1)",   "(- (* (cos ?a) (cos ?a)))"),
    //         ("sin-PI/6",    "(sin (/ PI 6))",        "1/2"),
    //         ("sin-PI/4",    "(sin (/ PI 4))",        "(/ (sqrt 2) 2)"),
    //         ("sin-PI/3",    "(sin (/ PI 3))",        "(/ (sqrt 3) 2)"),
    //         ("sin-PI/2",    "(sin (/ PI 2))",        "1"),
    //         ("sin-PI",      "(sin PI)",              "0"),
    //         ("sin-+PI",     "(sin (+ ?x PI))",        "(- (sin ?x))"),
    //         ("sin-+PI/2",   "(sin (+ ?x (/ PI 2)))",  "(cos ?x)"),
    //         ("cos-PI/6",    "(cos (/ PI 6))",        "(/ (sqrt 3) 2)"),
    //         ("cos-PI/4",    "(cos (/ PI 4))",        "(/ (sqrt 2) 2)"),
    //         ("cos-PI/3",    "(cos (/ PI 3))",        "1/2"),
    //         ("cos-PI/2",    "(cos (/ PI 2))",        "0"),
    //         ("cos-PI",      "(cos PI)",              "-1"),
    //         ("cos-+PI",     "(cos (+ ?x PI))",        "(- (cos ?x))"),
    //         ("cos-+PI/2",   "(cos (+ ?x (/ PI 2)))",  "(- (sin ?x))"),
    //         ("tan-PI/6",    "(tan (/ PI 6))",        "(/ 1 (sqrt 3))"),
    //         ("tan-PI/4",    "(tan (/ PI 4))",        "1"),
    //         ("tan-PI/3",    "(tan (/ PI 3))",        "(sqrt 3)"),
    //         ("tan-PI",      "(tan PI)",              "0"),
    //         ("tan-+PI",     "(tan (+ ?x PI))",        "(tan ?x)"),
    //         ("tan-+PI/2",   "(tan (+ ?x (/ PI 2)))",  "(- (/ 1 (tan ?x)))"),
    //         ("hang-0p-tan", "(/ (sin ?a) (+ 1 (cos ?a)))",     "(tan (/ ?a 2))"),
    //         ("hang-0m-tan", "(/ (- (sin ?a)) (+ 1 (cos ?a)))", "(tan (/ (- ?a) 2))"),
    //         ("hang-p0-tan", "(/ (- 1 (cos ?a)) (sin ?a))",     "(tan (/ ?a 2))"),
    //         ("hang-m0-tan", "(/ (- 1 (cos ?a)) (- (sin ?a)))", "(tan (/ (- ?a) 2))"),
    //         ("hang-p-tan",  "(/ (+ (sin ?a) (sin ?b)) (+ (cos ?a) (cos ?b)))", "(tan (/ (+ ?a ?b) 2))"),
    //         ("hang-m-tan",  "(/ (- (sin ?a) (sin ?b)) (+ (cos ?a) (cos ?b)))", "(tan (/ (- ?a ?b) 2))"),
    //     ]),
    // );

    // m.insert(
    //     "trig-reduce-fp-sound",
    //     mk_rules(&[
    //         ("sin-0",       "(sin 0)",               "0"),
    //         ("cos-0",       "(cos 0)",               "1"),
    //         ("tan-0",       "(tan 0)",               "0"),
    //     ]),
    // );

    // m.insert(
    //     "trig-reduce-fp-sound-nan",
    //     mk_rules(&[
    //         ("sin-neg",     "(sin (- ?x))",           "(- (sin ?x))"),
    //         ("cos-neg",     "(cos (- ?x))",           "(cos ?x)"),
    //         ("tan-neg", "(tan (- ?x))", "(- (tan ?x))"),
    //     ]),
    // );

    // m.insert(
    //     "htrig-reduce",
    //     mk_rules(&[
    //         ("sinh-def",    "(sinh ?x)",               "(/ (- (exp ?x) (exp (- ?x))) 2)"),
    //         ("cosh-def",    "(cosh ?x)",               "(/ (+ (exp ?x) (exp (- ?x))) 2)"),
    //         ("tanh-def",    "(tanh ?x)",               "(/ (- (exp ?x) (exp (- ?x))) (+ (exp ?x) (exp (- ?x))))"),
    //         ("tanh-def",    "(tanh ?x)",               "(/ (- (exp (* 2 ?x)) 1) (+ (exp (* 2 ?x)) 1))"),
    //         ("tanh-def",    "(tanh ?x)",               "(/ (- 1 (exp (* -2 ?x))) (+ 1 (exp (* -2 ?x))))"),
    //         ("sinh-cosh",   "(- (* (cosh ?x) (cosh ?x)) (* (sinh ?x) (sinh ?x)))", "1"),
    //         ("sinh-+-cosh", "(+ (cosh ?x) (sinh ?x))",  "(exp ?x)"),
    //         ("sinh---cosh", "(- (cosh ?x) (sinh ?x))", "(exp (- ?x))"),
    //     ]),
    // );

    m
}

fn all_rules() -> Vec<Rewrite<Math>> {
    let rules = rules();
    let mut vec = Vec::new();
    for category in rules.values() {
        for rule in category {
            vec.push(rule.clone())
        }
    }
    vec
}
#[test]
fn associate_adds() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start = "(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))";
    let start_expr = Math.parse_expr(start).unwrap();

    let (mut egraph, root) = EGraph::from_expr(&start_expr);

    let rules = {
        let all = rules();
        let mut r = Vec::new();
        r.extend(all["associativity"].clone());
        r.extend(all["commutativity"].clone());
        r
    };

    for _ in 0..4 {
        for rule in &rules {
            rule.run(&mut egraph);
            egraph.rebuild();
        }
    }

    // there are exactly 127 ways to add 7 things
    assert_eq!(egraph.classes.len(), 127);

    egraph.dump_dot("associate.dot");
}

#[test]
fn do_something() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start_expr = Math.parse_expr(EXP).unwrap();
    let (mut egraph, root) = EGraph::from_expr(&start_expr);

    let rules = rules();

    for _ in 0..1 {
        for (_name, list) in rules.iter() {
            for rule in list {
                rule.run(&mut egraph);
                egraph.rebuild();
            }
        }
    }

    egraph.dump_dot("math.dot");

    let ext = Extractor::new(&egraph);
    let best = ext.find_best(root);
    println!("Start: {:?}", start_expr);
    println!("Best: {:?}", best);
}
