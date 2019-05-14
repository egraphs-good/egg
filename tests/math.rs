use egg::{
    egraph::EGraph,
    expr::{Expr, Language, Name, QuestionMarkName},
    extract::{calculate_cost, Extractor},
    parse::ParsableLanguage,
    pattern::Rewrite,
    util::HashMap,
};
use log::*;
use ordered_float::NotNan;
use std::time::Instant;

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
    let mut add = |name, rules| {
        if m.contains_key(name) {
            panic!("{} was already there", name);
        }
        m.insert(name, mk_rules(rules));
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
            ("1-exp",   "1",       "(exp 0)"),
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

    // add(
    //     "log-distribute-fp-safe",
    //     &[
    //         ("log-E", "(log E)", "1"),
    //     ],
    // );

    // add(
    //     "trig-reduce",
    //     &[
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
    //     ],
    // );

    // add(
    //     "trig-reduce-fp-sound",
    //     &[
    //         ("sin-0",       "(sin 0)",               "0"),
    //         ("cos-0",       "(cos 0)",               "1"),
    //         ("tan-0",       "(tan 0)",               "0"),
    //     ],
    // );

    // add(
    //     "trig-reduce-fp-sound-nan",
    //     &[
    //         ("sin-neg",     "(sin (- ?x))",           "(- (sin ?x))"),
    //         ("cos-neg",     "(cos (- ?x))",           "(cos ?x)"),
    //         ("tan-neg", "(tan (- ?x))", "(- (tan ?x))"),
    //     ],
    // );

    // add(
    //     "htrig-reduce",
    //     &[
    //         ("sinh-def",    "(sinh ?x)",               "(/ (- (exp ?x) (exp (- ?x))) 2)"),
    //         ("cosh-def",    "(cosh ?x)",               "(/ (+ (exp ?x) (exp (- ?x))) 2)"),
    //         ("tanh-def",    "(tanh ?x)",               "(/ (- (exp ?x) (exp (- ?x))) (+ (exp ?x) (exp (- ?x))))"),
    //         ("tanh-def",    "(tanh ?x)",               "(/ (- (exp (* 2 ?x)) 1) (+ (exp (* 2 ?x)) 1))"),
    //         ("tanh-def",    "(tanh ?x)",               "(/ (- 1 (exp (* -2 ?x))) (+ 1 (exp (* -2 ?x))))"),
    //         ("sinh-cosh",   "(- (* (cosh ?x) (cosh ?x)) (* (sinh ?x) (sinh ?x)))", "1"),
    //         ("sinh-+-cosh", "(+ (cosh ?x) (sinh ?x))",  "(exp ?x)"),
    //         ("sinh---cosh", "(- (cosh ?x) (sinh ?x))", "(exp (- ?x))"),
    //     ],
    // );

    m
}

#[test]
fn associate_adds() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start = "(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))";
    let start_expr = Math.parse_expr(start).unwrap();

    let (mut egraph, _root) = EGraph::from_expr(&start_expr);

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
    assert_eq!(egraph.classes().len(), 127);

    egraph.dump_dot("associate.dot");
}

#[test]
fn do_something() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start_expr = Math.parse_expr(EXP).unwrap();
    let (mut egraph, root) = EGraph::from_expr(&start_expr);
    egraph.debug(true);

    let herbies_result = "(*
  (*
   (*
    (/
     (pow (- 1 (/ 1 (+ (exp (- 0 s)) 1))) c_n)
     (pow (- 1 (/ 1 (+ (exp (- 0 t)) 1))) c_n))
    (/ (pow (/ 1 (+ (exp (- 0 s)) 1)) c_p) (pow (/ 1 (+ (exp (- 0 t)) 1)) c_p)))
   (*
    (/
     (pow (- 1 (/ 1 (+ (exp (- 0 s)) 1))) c_n)
     (pow (- 1 (/ 1 (+ (exp (- 0 t)) 1))) c_n))
    (/ (pow (/ 1 (+ (exp (- 0 s)) 1)) c_p) (pow (/ 1 (+ (exp (- 0 t)) 1)) c_p))))
  (*
   (/
    (pow (- 1 (/ 1 (+ (exp (- 0 s)) 1))) c_n)
    (pow (- 1 (/ 1 (+ (exp (- 0 t)) 1))) c_n))
   (/ (pow (/ 1 (+ (exp (- 0 s)) 1)) c_p) (pow (/ 1 (+ (exp (- 0 t)) 1)) c_p))))";

    let other_expr = Math.parse_expr(herbies_result).unwrap();
    println!(
        "Herbie ({}): {}",
        calculate_cost(&other_expr),
        other_expr.to_sexp()
    );

    let rules = rules();

    let start_time = Instant::now();

    for _ in 0..2 {
        let mut applied = 0;
        let mut total_matches = 0;
        let mut last_total_matches = 0;
        let mut matches = Vec::new();
        for (_name, list) in rules.iter() {
            for rule in list {
                let ms = rule.lhs.search(&egraph);
                if ms.len() > 0 {
                    matches.push((&rule.rhs, ms));
                }
                // rule.run(&mut egraph);
                // egraph.rebuild();
            }
        }

        let match_time = Instant::now();

        for (rhs, ms) in matches {
            for m in ms {
                let actually_matched = m.apply(rhs, &mut egraph);
                applied += actually_matched.len();
                total_matches += m.mappings.len();

                // log the growth of the egraph
                if total_matches - last_total_matches > 1000 {
                    last_total_matches = total_matches;
                    let elapsed = match_time.elapsed();
                    debug!(
                        "nodes: {}, eclasses: {}, actual: {}, total: {}, us per match: {}",
                        egraph.len(),
                        egraph.classes().len(),
                        applied,
                        total_matches,
                        elapsed.as_micros() / total_matches as u128
                    );
                }
            }
        }
        egraph.rebuild();
        egraph.prune();
    }

    let rules_time = start_time.elapsed();

    let start_time = Instant::now();
    let ext = Extractor::new(&egraph);
    let best = ext.find_best(root);
    let extract_time = start_time.elapsed();

    println!(
        "Start ({}): {}",
        calculate_cost(&start_expr),
        start_expr.to_sexp()
    );
    println!("Best ({}): {}", best.cost, best.expr.to_sexp());
    println!(
        "Rules time: {}.{:03}",
        rules_time.as_secs(),
        rules_time.subsec_millis()
    );
    println!(
        "Extract time: {}.{:03}",
        extract_time.as_secs(),
        extract_time.subsec_millis()
    );

    egraph.dump_dot("math.dot");
}
