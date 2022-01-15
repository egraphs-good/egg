use egg::*;
use std::sync::atomic::{AtomicBool, Ordering};

use std::thread;

use instant::{Duration, Instant};
use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::{Pow, Signed, Zero};
use rand::seq::SliceRandom;
use rand::Rng;
use std::collections::HashSet;
use std::str::FromStr;

use std::fmt::Display;
use std::io::Read;
use std::io::Write;
use std::process::{Command, Stdio};
use symbolic_expressions::Sexp;
use wait_timeout::ChildExt;

pub type Constant = num_rational::BigRational;
pub type RecExpr = egg::RecExpr<Math>;
pub type Pattern = egg::Pattern<Math>;
pub type EGraph = egg::EGraph<Math, ConstantFold>;
pub type Rewrite = egg::Rewrite<Math, ConstantFold>;
pub type Runner = egg::Runner<Math, ConstantFold, IterData>;
pub type Iteration = egg::Iteration<IterData>;

pub struct IterData {
    pub extracted: Vec<(Id, Extracted)>,
}

pub struct Extracted {
    pub best: RecExpr,
    pub cost: usize,
}

impl IterationData<Math, ConstantFold> for IterData {
    fn make(runner: &Runner) -> Self {
        let extractor = Extractor::new(&runner.egraph, AstSize);
        let extracted = runner
            .roots
            .iter()
            .map(|&root| {
                let (cost, best) = extractor.find_best(root);
                let ext = Extracted { cost, best };
                (root, ext)
            })
            .collect();
        Self { extracted }
    }
}

// operators from FPCore
define_language! {
    pub enum Math {

        // constant-folding operators

        "+" = Add([Id; 3]),
        "-" = Sub([Id; 3]),
        "*" = Mul([Id; 3]),
        "/" = Div([Id; 3]),
        "pow" = Pow([Id; 3]),
        "neg" = Neg([Id; 2]),
        "sqrt" = Sqrt([Id; 2]),
        "fabs" = Fabs([Id; 2]),
        "ceil" = Ceil([Id; 2]),
        "floor" = Floor([Id; 2]),
        "round" = Round([Id; 2]),
        "log" = Log([Id; 2]),
        "cbrt" = Cbrt([Id; 2]),

        Constant(Constant),
        Symbol(egg::Symbol),
        Other(egg::Symbol, Vec<Id>),
    }
}

pub struct ConstantFold {
    pub unsound: AtomicBool,
    pub constant_fold: bool,
    pub prune: bool,
}

impl Default for ConstantFold {
    fn default() -> Self {
        Self {
            constant_fold: true,
            prune: true,
            unsound: AtomicBool::from(false),
        }
    }
}

impl Analysis<Math> for ConstantFold {
    type Data = Option<(Constant, (PatternAst<Math>, Subst))>;
    fn make(egraph: &EGraph, enode: &Math) -> Self::Data {
        if !egraph.analysis.constant_fold {
            return None;
        }

        let x = |id: &Id| egraph[*id].data.clone().map(|x| x.0);
        let is_zero = |id: &Id| {
            let data = egraph[*id].data.as_ref();
            match data {
                Some(data) => data.0.is_zero(),
                None => false,
            }
        };

        Some((
            match enode {
                Math::Constant(c) => c.clone(),

                // real
                Math::Add([_p, a, b]) => x(a)? + x(b)?,
                Math::Sub([_p, a, b]) => x(a)? - x(b)?,
                Math::Mul([_p, a, b]) => x(a)? * x(b)?,
                Math::Div([_p, a, b]) => {
                    if x(b)?.is_zero() {
                        return None;
                    } else {
                        x(a)? / x(b)?
                    }
                }
                Math::Neg([_p, a]) => -x(a)?.clone(),
                Math::Pow([_p, a, b]) => {
                    if is_zero(a) {
                        if x(b)?.is_positive() {
                            Ratio::new(BigInt::from(0), BigInt::from(1))
                        } else {
                            return None;
                        }
                    } else if is_zero(b) {
                        Ratio::new(BigInt::from(1), BigInt::from(1))
                    } else if x(b)?.is_integer() {
                        Pow::pow(x(a)?, x(b)?.to_integer())
                    } else {
                        return None;
                    }
                }
                Math::Sqrt([_p, a]) => {
                    let a = x(a)?;
                    if *a.numer() > BigInt::from(0) && *a.denom() > BigInt::from(0) {
                        let s1 = a.numer().sqrt();
                        let s2 = a.denom().sqrt();
                        let is_perfect = &(&s1 * &s1) == a.numer() && &(&s2 * &s2) == a.denom();
                        if is_perfect {
                            Ratio::new(s1, s2)
                        } else {
                            return None;
                        }
                    } else {
                        return None;
                    }
                }
                Math::Log([_p, a]) => {
                    if x(a)? == Ratio::new(BigInt::from(1), BigInt::from(1)) {
                        Ratio::new(BigInt::from(0), BigInt::from(1))
                    } else {
                        return None;
                    }
                }
                Math::Cbrt([_p, a]) => {
                    if x(a)? == Ratio::new(BigInt::from(1), BigInt::from(1)) {
                        Ratio::new(BigInt::from(1), BigInt::from(1))
                    } else {
                        return None;
                    }
                }
                Math::Fabs([_p, a]) => x(a)?.clone().abs(),
                Math::Floor([_p, a]) => x(a)?.floor(),
                Math::Ceil([_p, a]) => x(a)?.ceil(),
                Math::Round([_p, a]) => x(a)?.round(),

                _ => return None,
            },
            {
                let mut pattern: PatternAst<Math> = Default::default();
                let mut var_counter = 0;
                let mut subst: Subst = Default::default();
                enode.for_each(|child| {
                    if let Some(constant) = x(&child) {
                        pattern.add(ENodeOrVar::ENode(Math::Constant(constant)));
                    } else {
                        let var = ("?".to_string() + &var_counter.to_string())
                            .parse()
                            .unwrap();
                        pattern.add(ENodeOrVar::Var(var));
                        subst.insert(var, child);
                        var_counter += 1;
                    }
                });
                let mut counter = 0;
                let mut head = enode.clone();
                head.update_children(|_child| {
                    let res = Id::from(counter);
                    counter += 1;
                    res
                });
                pattern.add(ENodeOrVar::ENode(head));
                (pattern, subst)
            },
        ))
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        match (to.as_mut(), &from) {
            (None, None) => DidMerge(false, false),
            (None, Some(_)) => {
                *to = from;
                DidMerge(true, false)
            }
            (Some(_), None) => DidMerge(false, true),
            (Some(a), Some(ref b)) => {
                if a.0 != b.0 {
                    if !self.unsound.swap(true, Ordering::SeqCst) {
                        log::warn!("Bad merge detected: {} != {}", a.0, b.0);
                    }
                }
                DidMerge(false, false)
            }
        }
    }

    fn modify(egraph: &mut EGraph, class_id: Id) {
        let class = &mut egraph[class_id];
        if let Some((c, (pat, subst))) = class.data.clone() {
            egraph.union_instantiations(
                &pat,
                &format!("{}", c).parse().unwrap(),
                &subst,
                "metadata-eval".to_string(),
            );

            if egraph.analysis.prune {
                egraph[class_id].nodes.retain(|n| n.is_leaf())
            }
        }
    }
}

pub fn mk_rules(tuples: &[(&str, &str, &str)], replace: &str) -> Vec<Rewrite> {
    tuples
        .iter()
        .filter_map(|(name, left, right)| {
            let name_replaced = name.replace("binary64", replace);
            let left_replaced = left.replace("f64", replace);
            let right_replaced = right.replace("f64", replace);
            let left = Pattern::from_str(&left_replaced).unwrap();
            let right = Pattern::from_str(&right_replaced).unwrap();
            Some(Rewrite::new(name_replaced, left, right).unwrap())
        })
        .collect()
}

pub fn math_rules(type_str: &str) -> Vec<Rewrite> {
    let mut rules: Vec<Rewrite> = Default::default();
    let mut add = |new_rules| {
        rules.extend(mk_rules(new_rules, type_str));
    };

    add(
    &[("not-true", "(not real (TRUE real))", "(FALSE real)"),
("not-false", "(not real (FALSE real))", "(TRUE real)"),
("not-not", "(not real (not real ?a))", "?a"),
("not-and", "(not real (and real ?a ?b))", "(or real (not real ?a) (not real ?b))"),
("not-or", "(not real (or real ?a ?b))", "(and real (not real ?a) (not real ?b))"),
("and-true-l", "(and real (TRUE real) ?a)", "?a"),
("and-true-r", "(and real ?a (TRUE real))", "?a"),
("and-false-l", "(and real (FALSE real) ?a)", "(FALSE real)"),
("and-false-r", "(and real ?a (FALSE real))", "(FALSE real)"),
("and-same", "(and real ?a ?a)", "?a"),
("or-true-l", "(or real (TRUE real) ?a)", "(TRUE real)"),
("or-true-r", "(or real ?a (TRUE real))", "(TRUE real)"),
("or-false-l", "(or real (FALSE real) ?a)", "?a"),
("or-false-r", "(or real ?a (FALSE real))", "?a"),
("or-same", "(or real ?a ?a)", "?a"),
("erfc-erf_binary64", "(erf f64 ?x)", "(- f64 1 (erfc f64 ?x))"),
("erf-erfc_binary64", "(erfc f64 ?x)", "(- f64 1 (erf f64 ?x))"),
("erf-odd_binary64", "(erf f64 (neg f64 ?x))", "(neg f64 (erf f64 ?x))"),
("if-if-and-not_binary64", "(if real ?a (if real ?b ?y ?x) ?y)", "(if real (and real ?a (not real ?b)) ?x ?y)"),
("if-if-and_binary64", "(if real ?a (if real ?b ?x ?y) ?y)", "(if real (and real ?a ?b) ?x ?y)"),
("if-if-or-not_binary64", "(if real ?a ?x (if real ?b ?y ?x))", "(if real (or real ?a (not real ?b)) ?x ?y)"),
("if-if-or_binary64", "(if real ?a ?x (if real ?b ?x ?y))", "(if real (or real ?a ?b) ?x ?y)"),
("if-not_binary64", "(if real (not real ?a) ?x ?y)", "(if real ?a ?y ?x)"),
("if-same_binary64", "(if real ?a ?x ?x)", "?x"),
("if-false_binary64", "(if real (FALSE real) ?x ?y)", "?y"),
("if-true_binary64", "(if real (TRUE real) ?x ?y)", "?x"),
("not-gte_binary64", "(not real (>= f64 ?x ?y))", "(< f64 ?x ?y)"),
("not-lte_binary64", "(not real (<= f64 ?x ?y))", "(> f64 ?x ?y)"),
("not-gt_binary64", "(not real (> f64 ?x ?y))", "(<= f64 ?x ?y)"),
("not-lt_binary64", "(not real (< f64 ?x ?y))", "(>= f64 ?x ?y)"),
("gte-same_binary64", "(>= f64 ?x ?x)", "(TRUE real)"),
("lte-same_binary64", "(<= f64 ?x ?x)", "(TRUE real)"),
("gt-same_binary64", "(> f64 ?x ?x)", "(FALSE real)"),
("lt-same_binary64", "(< f64 ?x ?x)", "(FALSE real)"),
("fma-udef_binary64", "(fma f64 ?x ?y ?z)", "(+ f64 (* f64 ?x ?y) ?z)"),
("fma-neg_binary64", "(- f64 (* f64 ?x ?y) ?z)", "(fma f64 ?x ?y (neg f64 ?z))"),
("fma-def_binary64", "(+ f64 (* f64 ?x ?y) ?z)", "(fma f64 ?x ?y ?z)"),
("hypot-1-def_binary64", "(sqrt f64 (+ f64 1 (* f64 ?y ?y)))", "(hypot f64 1 ?y)"),
("hypot-def_binary64", "(sqrt f64 (+ f64 (* f64 ?x ?x) (* f64 ?y ?y)))", "(hypot f64 ?x ?y)"),
("expm1-log1p_binary64", "(expm1 f64 (log1p f64 ?x))", "?x"),
("log1p-expm1_binary64", "(log1p f64 (expm1 f64 ?x))", "?x"),
("log1p-def_binary64", "(log f64 (+ f64 1 ?x))", "(log1p f64 ?x)"),
("expm1-def_binary64", "(- f64 (exp f64 ?x) 1)", "(expm1 f64 ?x)"),
("sinh---cosh_binary64", "(- f64 (cosh f64 ?x) (sinh f64 ?x))", "(exp f64 (neg f64 ?x))"),
("sinh-+-cosh_binary64", "(+ f64 (cosh f64 ?x) (sinh f64 ?x))", "(exp f64 ?x)"),
("sinh-cosh_binary64", "(- f64 (* f64 (cosh f64 ?x) (cosh f64 ?x)) (* f64 (sinh f64 ?x) (sinh f64 ?x)))", "1"),
("tanh-def-c_binary64", "(tanh f64 ?x)", "(/ f64 (- f64 1 (exp f64 (* f64 -2 ?x))) (+ f64 1 (exp f64 (* f64 -2 ?x))))"),
("tanh-def-b_binary64", "(tanh f64 ?x)", "(/ f64 (- f64 (exp f64 (* f64 2 ?x)) 1) (+ f64 (exp f64 (* f64 2 ?x)) 1))"),
("tanh-def-a_binary64", "(tanh f64 ?x)", "(/ f64 (- f64 (exp f64 ?x) (exp f64 (neg f64 ?x))) (+ f64 (exp f64 ?x) (exp f64 (neg f64 ?x))))"),
("cosh-def_binary64", "(cosh f64 ?x)", "(/ f64 (+ f64 (exp f64 ?x) (exp f64 (neg f64 ?x))) 2)"),
("sinh-def_binary64", "(sinh f64 ?x)", "(/ f64 (- f64 (exp f64 ?x) (exp f64 (neg f64 ?x))) 2)"),
("tan-neg_binary64", "(tan f64 (neg f64 ?x))", "(neg f64 (tan f64 ?x))"),
("cos-neg_binary64", "(cos f64 (neg f64 ?x))", "(cos f64 ?x)"),
("sin-neg_binary64", "(sin f64 (neg f64 ?x))", "(neg f64 (sin f64 ?x))"),
("tan-0_binary64", "(tan f64 0)", "0"),
("cos-0_binary64", "(cos f64 0)", "1"),
("sin-0_binary64", "(sin f64 0)", "0"),
("hang-m-tan_binary64", "(/ f64 (- f64 (sin f64 ?a) (sin f64 ?b)) (+ f64 (cos f64 ?a) (cos f64 ?b)))", "(tan f64 (/ f64 (- f64 ?a ?b) 2))"),
("hang-p-tan_binary64", "(/ f64 (+ f64 (sin f64 ?a) (sin f64 ?b)) (+ f64 (cos f64 ?a) (cos f64 ?b)))", "(tan f64 (/ f64 (+ f64 ?a ?b) 2))"),
("hang-m0-tan_binary64", "(/ f64 (- f64 1 (cos f64 ?a)) (neg f64 (sin f64 ?a)))", "(tan f64 (/ f64 (neg f64 ?a) 2))"),
("hang-p0-tan_binary64", "(/ f64 (- f64 1 (cos f64 ?a)) (sin f64 ?a))", "(tan f64 (/ f64 ?a 2))"),
("hang-0m-tan_binary64", "(/ f64 (neg f64 (sin f64 ?a)) (+ f64 1 (cos f64 ?a)))", "(tan f64 (/ f64 (neg f64 ?a) 2))"),
("hang-0p-tan_binary64", "(/ f64 (sin f64 ?a) (+ f64 1 (cos f64 ?a)))", "(tan f64 (/ f64 ?a 2))"),
("tan-+PI/2_binary64", "(tan f64 (+ f64 ?x (/ f64 (PI f64) 2)))", "(/ f64 -1 (tan f64 ?x))"),
("tan-+PI_binary64", "(tan f64 (+ f64 ?x (PI f64)))", "(tan f64 ?x)"),
("tan-PI_binary64", "(tan f64 (PI f64))", "0"),
("tan-PI/3_binary64", "(tan f64 (/ f64 (PI f64) 3))", "(sqrt f64 3)"),
("tan-PI/4_binary64", "(tan f64 (/ f64 (PI f64) 4))", "1"),
("tan-PI/6_binary64", "(tan f64 (/ f64 (PI f64) 6))", "(/ f64 1 (sqrt f64 3))"),
("cos-+PI/2_binary64", "(cos f64 (+ f64 ?x (/ f64 (PI f64) 2)))", "(neg f64 (sin f64 ?x))"),
("cos-+PI_binary64", "(cos f64 (+ f64 ?x (PI f64)))", "(neg f64 (cos f64 ?x))"),
("cos-PI_binary64", "(cos f64 (PI f64))", "-1"),
("cos-PI/2_binary64", "(cos f64 (/ f64 (PI f64) 2))", "0"),
("cos-PI/3_binary64", "(cos f64 (/ f64 (PI f64) 3))", "1/2"),
("cos-PI/4_binary64", "(cos f64 (/ f64 (PI f64) 4))", "(/ f64 (sqrt f64 2) 2)"),
("cos-PI/6_binary64", "(cos f64 (/ f64 (PI f64) 6))", "(/ f64 (sqrt f64 3) 2)"),
("sin-+PI/2_binary64", "(sin f64 (+ f64 ?x (/ f64 (PI f64) 2)))", "(cos f64 ?x)"),
("sin-+PI_binary64", "(sin f64 (+ f64 ?x (PI f64)))", "(neg f64 (sin f64 ?x))"),
("sin-PI_binary64", "(sin f64 (PI f64))", "0"),
("sin-PI/2_binary64", "(sin f64 (/ f64 (PI f64) 2))", "1"),
("sin-PI/3_binary64", "(sin f64 (/ f64 (PI f64) 3))", "(/ f64 (sqrt f64 3) 2)"),
("sin-PI/4_binary64", "(sin f64 (/ f64 (PI f64) 4))", "(/ f64 (sqrt f64 2) 2)"),
("sin-PI/6_binary64", "(sin f64 (/ f64 (PI f64) 6))", "1/2"),
("sub-1-sin_binary64", "(- f64 (* f64 (sin f64 ?a) (sin f64 ?a)) 1)", "(neg f64 (* f64 (cos f64 ?a) (cos f64 ?a)))"),
("sub-1-cos_binary64", "(- f64 (* f64 (cos f64 ?a) (cos f64 ?a)) 1)", "(neg f64 (* f64 (sin f64 ?a) (sin f64 ?a)))"),
("-1-add-sin_binary64", "(+ f64 (* f64 (sin f64 ?a) (sin f64 ?a)) -1)", "(neg f64 (* f64 (cos f64 ?a) (cos f64 ?a)))"),
("-1-add-cos_binary64", "(+ f64 (* f64 (cos f64 ?a) (cos f64 ?a)) -1)", "(neg f64 (* f64 (sin f64 ?a) (sin f64 ?a)))"),
("1-sub-sin_binary64", "(- f64 1 (* f64 (sin f64 ?a) (sin f64 ?a)))", "(* f64 (cos f64 ?a) (cos f64 ?a))"),
("1-sub-cos_binary64", "(- f64 1 (* f64 (cos f64 ?a) (cos f64 ?a)))", "(* f64 (sin f64 ?a) (sin f64 ?a))"),
("cos-sin-sum_binary64", "(+ f64 (* f64 (cos f64 ?a) (cos f64 ?a)) (* f64 (sin f64 ?a) (sin f64 ?a)))", "1"),
("log-E_binary64", "(log f64 (E f64))", "1"),
("log-pow_binary64", "(log f64 (pow f64 ?a ?b))", "(* f64 ?b (log f64 ?a))"),
("log-rec_binary64", "(log f64 (/ f64 1 ?a))", "(neg f64 (log f64 ?a))"),
("log-div_binary64", "(log f64 (/ f64 ?a ?b))", "(- f64 (log f64 ?a) (log f64 ?b))"),
("log-prod_binary64", "(log f64 (* f64 ?a ?b))", "(+ f64 (log f64 ?a) (log f64 ?b))"),
("pow-base-0_binary64", "(pow f64 0 ?a)", "0"),
("unpow1/3_binary64", "(pow f64 ?a 1/3)", "(cbrt f64 ?a)"),
("unpow3_binary64", "(pow f64 ?a 3)", "(* f64 (* f64 ?a ?a) ?a)"),
("unpow2_binary64", "(pow f64 ?a 2)", "(* f64 ?a ?a)"),
("unpow1/2_binary64", "(pow f64 ?a 1/2)", "(sqrt f64 ?a)"),
("pow-plus_binary64", "(* f64 (pow f64 ?a ?b) ?a)", "(pow f64 ?a (+ f64 ?b 1))"),
("exp-to-pow_binary64", "(exp f64 (* f64 (log f64 ?a) ?b))", "(pow f64 ?a ?b)"),
("pow-base-1_binary64", "(pow f64 1 ?a)", "1"),
("unpow0_binary64", "(pow f64 ?a 0)", "1"),
("unpow1_binary64", "(pow f64 ?a 1)", "?a"),
("unpow-1_binary64", "(pow f64 ?a -1)", "(/ f64 1 ?a)"),
("exp-lft-cube_binary64", "(exp f64 (* f64 ?a 3))", "(pow f64 (exp f64 ?a) 3)"),
("exp-lft-sqr_binary64", "(exp f64 (* f64 ?a 2))", "(* f64 (exp f64 ?a) (exp f64 ?a))"),
("exp-cbrt_binary64", "(exp f64 (/ f64 ?a 3))", "(cbrt f64 (exp f64 ?a))"),
("exp-sqrt_binary64", "(exp f64 (/ f64 ?a 2))", "(sqrt f64 (exp f64 ?a))"),
("exp-prod_binary64", "(exp f64 (* f64 ?a ?b))", "(pow f64 (exp f64 ?a) ?b)"),
("div-exp_binary64", "(/ f64 (exp f64 ?a) (exp f64 ?b))", "(exp f64 (- f64 ?a ?b))"),
("rec-exp_binary64", "(/ f64 1 (exp f64 ?a))", "(exp f64 (neg f64 ?a))"),
("prod-exp_binary64", "(* f64 (exp f64 ?a) (exp f64 ?b))", "(exp f64 (+ f64 ?a ?b))"),
("exp-diff_binary64", "(exp f64 (- f64 ?a ?b))", "(/ f64 (exp f64 ?a) (exp f64 ?b))"),
("exp-neg_binary64", "(exp f64 (neg f64 ?a))", "(/ f64 1 (exp f64 ?a))"),
("exp-sum_binary64", "(exp f64 (+ f64 ?a ?b))", "(* f64 (exp f64 ?a) (exp f64 ?b))"),
("e-exp-1_binary64", "(E f64)", "(exp f64 1)"),
("1-exp_binary64", "1", "(exp f64 0)"),
("exp-1-e_binary64", "(exp f64 1)", "(E f64)"),
("exp-0_binary64", "(exp f64 0)", "1"),
("rem-log-exp_binary64", "(log f64 (exp f64 ?x))", "?x"),
("rem-exp-log_binary64", "(exp f64 (log f64 ?x))", "?x"),
("cube-unmult_binary64", "(* f64 ?x (* f64 ?x ?x))", "(pow f64 ?x 3)"),
("cube-mult_binary64", "(pow f64 ?x 3)", "(* f64 ?x (* f64 ?x ?x))"),
("cube-div_binary64", "(pow f64 (/ f64 ?x ?y) 3)", "(/ f64 (pow f64 ?x 3) (pow f64 ?y 3))"),
("cube-prod_binary64", "(pow f64 (* f64 ?x ?y) 3)", "(* f64 (pow f64 ?x 3) (pow f64 ?y 3))"),
("cube-neg_binary64", "(pow f64 (neg f64 ?x) 3)", "(neg f64 (pow f64 ?x 3))"),
("rem-3cbrt-rft_binary64", "(* f64 (cbrt f64 ?x) (* f64 (cbrt f64 ?x) (cbrt f64 ?x)))", "?x"),
("rem-3cbrt-lft_binary64", "(* f64 (* f64 (cbrt f64 ?x) (cbrt f64 ?x)) (cbrt f64 ?x))", "?x"),
("rem-cbrt-cube_binary64", "(cbrt f64 (pow f64 ?x 3))", "?x"),
("rem-cube-cbrt_binary64", "(pow f64 (cbrt f64 ?x) 3)", "?x"),
("fabs-div_binary64", "(fabs f64 (/ f64 ?a ?b))", "(/ f64 (fabs f64 ?a) (fabs f64 ?b))"),
("fabs-mul_binary64", "(fabs f64 (* f64 ?a ?b))", "(* f64 (fabs f64 ?a) (fabs f64 ?b))"),
("fabs-sqr_binary64", "(fabs f64 (* f64 ?x ?x))", "(* f64 ?x ?x)"),
("fabs-neg_binary64", "(fabs f64 (neg f64 ?x))", "(fabs f64 ?x)"),
("fabs-sub_binary64", "(fabs f64 (- f64 ?a ?b))", "(fabs f64 (- f64 ?b ?a))"),
("fabs-fabs_binary64", "(fabs f64 (fabs f64 ?x))", "(fabs f64 ?x)"),
("sqr-abs_binary64", "(* f64 (fabs f64 ?x) (fabs f64 ?x))", "(* f64 ?x ?x)"),
("sqr-neg_binary64", "(* f64 (neg f64 ?x) (neg f64 ?x))", "(* f64 ?x ?x)"),
("rem-sqrt-square_binary64", "(sqrt f64 (* f64 ?x ?x))", "(fabs f64 ?x)"),
("rem-square-sqrt_binary64", "(* f64 (sqrt f64 ?x) (sqrt f64 ?x))", "?x"),
("times-frac_binary64", "(/ f64 (* f64 ?a ?b) (* f64 ?c ?d))", "(* f64 (/ f64 ?a ?c) (/ f64 ?b ?d))"),
("div-sub_binary64", "(/ f64 (- f64 ?a ?b) ?c)", "(- f64 (/ f64 ?a ?c) (/ f64 ?b ?c))"),
("neg-mul-1_binary64", "(neg f64 ?a)", "(* f64 -1 ?a)"),
("neg-sub0_binary64", "(neg f64 ?b)", "(- f64 0 ?b)"),
("unsub-neg_binary64", "(+ f64 ?a (neg f64 ?b))", "(- f64 ?a ?b)"),
("sub-neg_binary64", "(- f64 ?a ?b)", "(+ f64 ?a (neg f64 ?b))"),
("mul-1-neg_binary64", "(* f64 -1 ?a)", "(neg f64 ?a)"),
("/-rgt-identity_binary64", "(/ f64 ?a 1)", "?a"),
("*-rgt-identity_binary64", "(* f64 ?a 1)", "?a"),
("*-lft-identity_binary64", "(* f64 1 ?a)", "?a"),
("remove-double-neg_binary64", "(neg f64 (neg f64 ?a))", "?a"),
("sub0-neg_binary64", "(- f64 0 ?a)", "(neg f64 ?a)"),
("--rgt-identity_binary64", "(- f64 ?a 0)", "?a"),
("+-rgt-identity_binary64", "(+ f64 ?a 0)", "?a"),
("+-lft-identity_binary64", "(+ f64 0 ?a)", "?a"),
("mul0-rgt_binary64", "(* f64 ?a 0)", "0"),
("mul0-lft_binary64", "(* f64 0 ?a)", "0"),
("div0_binary64", "(/ f64 0 ?a)", "0"),
("*-inverses_binary64", "(/ f64 ?a ?a)", "1"),
("+-inverses_binary64", "(- f64 ?a ?a)", "0"),
("lft-mult-inverse_binary64", "(* f64 (/ f64 1 ?a) ?a)", "1"),
("rgt-mult-inverse_binary64", "(* f64 ?a (/ f64 1 ?a))", "1"),
("remove-double-div_binary64", "(/ f64 1 (/ f64 1 ?a))", "?a"),
("pow-sqr_binary64", "(* f64 (pow f64 ?a ?b) (pow f64 ?a ?b))", "(pow f64 ?a (* f64 2 ?b))"),
("sqr-pow_binary64", "(pow f64 ?a ?b)", "(* f64 (pow f64 ?a (/ f64 ?b 2)) (pow f64 ?a (/ f64 ?b 2)))"),
("difference-of-sqr--1_binary64", "(+ f64 (* f64 ?a ?a) -1)", "(* f64 (+ f64 ?a 1) (- f64 ?a 1))"),
("difference-of-sqr-1_binary64", "(- f64 (* f64 ?a ?a) 1)", "(* f64 (+ f64 ?a 1) (- f64 ?a 1))"),
("difference-of-squares_binary64", "(- f64 (* f64 ?a ?a) (* f64 ?b ?b))", "(* f64 (+ f64 ?a ?b) (- f64 ?a ?b))"),
("unswap-sqr_binary64", "(* f64 (* f64 ?a ?a) (* f64 ?b ?b))", "(* f64 (* f64 ?a ?b) (* f64 ?a ?b))"),
("swap-sqr_binary64", "(* f64 (* f64 ?a ?b) (* f64 ?a ?b))", "(* f64 (* f64 ?a ?a) (* f64 ?b ?b))"),
("cancel-sign-sub-inv_binary64", "(- f64 ?a (* f64 ?b ?c))", "(+ f64 ?a (* f64 (neg f64 ?b) ?c))"),
("cancel-sign-sub_binary64", "(- f64 ?a (* f64 (neg f64 ?b) ?c))", "(+ f64 ?a (* f64 ?b ?c))"),
("distribute-neg-frac_binary64", "(neg f64 (/ f64 ?a ?b))", "(/ f64 (neg f64 ?a) ?b)"),
("distribute-frac-neg_binary64", "(/ f64 (neg f64 ?a) ?b)", "(neg f64 (/ f64 ?a ?b))"),
("distribute-neg-out_binary64", "(+ f64 (neg f64 ?a) (neg f64 ?b))", "(neg f64 (+ f64 ?a ?b))"),
("distribute-neg-in_binary64", "(neg f64 (+ f64 ?a ?b))", "(+ f64 (neg f64 ?a) (neg f64 ?b))"),
("distribute-rgt-neg-out_binary64", "(* f64 ?a (neg f64 ?b))", "(neg f64 (* f64 ?a ?b))"),
("distribute-lft-neg-out_binary64", "(* f64 (neg f64 ?a) ?b)", "(neg f64 (* f64 ?a ?b))"),
("distribute-rgt-neg-in_binary64", "(neg f64 (* f64 ?a ?b))", "(* f64 ?a (neg f64 ?b))"),
("distribute-lft-neg-in_binary64", "(neg f64 (* f64 ?a ?b))", "(* f64 (neg f64 ?a) ?b)"),
("distribute-rgt1-in_binary64", "(+ f64 ?a (* f64 ?c ?a))", "(* f64 (+ f64 ?c 1) ?a)"),
("distribute-lft1-in_binary64", "(+ f64 (* f64 ?b ?a) ?a)", "(* f64 (+ f64 ?b 1) ?a)"),
("distribute-rgt-out--_binary64", "(- f64 (* f64 ?b ?a) (* f64 ?c ?a))", "(* f64 ?a (- f64 ?b ?c))"),
("distribute-rgt-out_binary64", "(+ f64 (* f64 ?b ?a) (* f64 ?c ?a))", "(* f64 ?a (+ f64 ?b ?c))"),
("distribute-lft-out--_binary64", "(- f64 (* f64 ?a ?b) (* f64 ?a ?c))", "(* f64 ?a (- f64 ?b ?c))"),
("distribute-lft-out_binary64", "(+ f64 (* f64 ?a ?b) (* f64 ?a ?c))", "(* f64 ?a (+ f64 ?b ?c))"),
("distribute-rgt-in_binary64", "(* f64 ?a (+ f64 ?b ?c))", "(+ f64 (* f64 ?b ?a) (* f64 ?c ?a))"),
("distribute-lft-in_binary64", "(* f64 ?a (+ f64 ?b ?c))", "(+ f64 (* f64 ?a ?b) (* f64 ?a ?c))"),
("count-2_binary64", "(+ f64 ?x ?x)", "(* f64 2 ?x)"),
("associate-/l/_binary64", "(/ f64 (/ f64 ?b ?c) ?a)", "(/ f64 ?b (* f64 ?a ?c))"),
("associate-/r/_binary64", "(/ f64 ?a (/ f64 ?b ?c))", "(* f64 (/ f64 ?a ?b) ?c)"),
("associate-/l*_binary64", "(/ f64 (* f64 ?b ?c) ?a)", "(/ f64 ?b (/ f64 ?a ?c))"),
("associate-/r*_binary64", "(/ f64 ?a (* f64 ?b ?c))", "(/ f64 (/ f64 ?a ?b) ?c)"),
("associate-*l/_binary64", "(* f64 (/ f64 ?a ?b) ?c)", "(/ f64 (* f64 ?a ?c) ?b)"),
("associate-*r/_binary64", "(* f64 ?a (/ f64 ?b ?c))", "(/ f64 (* f64 ?a ?b) ?c)"),
("associate-*l*_binary64", "(* f64 (* f64 ?a ?b) ?c)", "(* f64 ?a (* f64 ?b ?c))"),
("associate-*r*_binary64", "(* f64 ?a (* f64 ?b ?c))", "(* f64 (* f64 ?a ?b) ?c)"),
("associate--r-_binary64", "(- f64 ?a (- f64 ?b ?c))", "(+ f64 (- f64 ?a ?b) ?c)"),
("associate--l-_binary64", "(- f64 (- f64 ?a ?b) ?c)", "(- f64 ?a (+ f64 ?b ?c))"),
("associate--l+_binary64", "(- f64 (+ f64 ?a ?b) ?c)", "(+ f64 ?a (- f64 ?b ?c))"),
("associate--r+_binary64", "(- f64 ?a (+ f64 ?b ?c))", "(- f64 (- f64 ?a ?b) ?c)"),
("associate-+l-_binary64", "(+ f64 (- f64 ?a ?b) ?c)", "(- f64 ?a (- f64 ?b ?c))"),
("associate-+r-_binary64", "(+ f64 ?a (- f64 ?b ?c))", "(- f64 (+ f64 ?a ?b) ?c)"),
("associate-+l+_binary64", "(+ f64 (+ f64 ?a ?b) ?c)", "(+ f64 ?a (+ f64 ?b ?c))"),
("associate-+r+_binary64", "(+ f64 ?a (+ f64 ?b ?c))", "(+ f64 (+ f64 ?a ?b) ?c)"),
("*-commutative_binary64", "(* f64 ?a ?b)", "(* f64 ?b ?a)"),
("+-commutative_binary64", "(+ f64 ?a ?b)", "(+ f64 ?b ?a)"),
],);

    rules
}

fn get_z3_funcs<L>(pattern: &PatternAst<L>) -> HashSet<(String, usize)>
where
    L: Language + Display + 'static,
{
    let mut set: HashSet<(String, usize)> = Default::default();

    for node in pattern.as_ref() {
        if let ENodeOrVar::ENode(node) = node {
            set.insert((node.to_string(), node.children().len()));
        }
    }

    set
}

fn get_all_z3_funcs_consts<L, A>(
    rules: &[egg::Rewrite<L, A>],
    start: &egg::RecExpr<L>,
    end: &egg::RecExpr<L>,
) -> (Vec<String>, Vec<String>)
where
    L: Language + Display + 'static,
    A: Analysis<L> + Default,
{
    let mut set: HashSet<(String, usize)> = Default::default();

    let mut const_set: HashSet<String> = Default::default();

    for rule in rules {
        set = set
            .union(&get_z3_funcs(rule.searcher.get_pattern_ast().unwrap()))
            .cloned()
            .collect();
        set = set
            .union(&get_z3_funcs(rule.applier.get_pattern_ast().unwrap()))
            .cloned()
            .collect();
    }

    for node in start.as_ref() {
        set.insert((node.to_string(), node.children().len()));
    }

    for node in end.as_ref() {
        set.insert((node.to_string(), node.children().len()));
    }

    let mut res = vec!["(declare-fun wrap-rat (Real) A)".to_string()];
    let mut consts = vec![];

    for s in set {
        if s.1 > 0 {
            let avec = vec!["A"; s.1];
            res.push(format!("(declare-fun {} ({}) A)", s.0, avec.join(" ")));
        } else {
            if s.0.parse::<i64>().is_err() {
                if s.0.parse::<Ratio<BigInt>>().is_err() {
                    consts.push(format!("(declare-const {} A)", s.0));
                }
            }
        }
    }

    (res, consts)
}

fn get_const_fold_rewrites() -> Vec<String> {
    let mut res = vec![];

    let ops = vec!["+", "-", "*", "/"];
    let conditions = vec!["", "", "", "(not (= ?y 0))"];

    for (op, condition) in ops.iter().zip(conditions.iter()) {
        if condition == &"" {
            res.push(format!("(assert (forall ((?t A) (?x Real) (?y Real)) (= ({} ?t (wrap-rat ?x) (wrap-rat ?y)) (wrap-rat ({} ?x ?y)))))", op, op));
        } else {
            res.push(format!("(assert (forall ((?t A) (?x Real) (?y Real)) (=> {} (= ({} ?t (wrap-rat ?x) (wrap-rat ?y)) (wrap-rat ({} ?x ?y))))))", condition, op, op));
        }
    }

    res.push(format!("(assert (forall ((?t A) (?x Real) (?y Real)) (= ({} ?t (wrap-rat ?x) (wrap-rat ?y)) (wrap-rat ({} ?x ?y)))))", "pow", "^"));
    res.push(format!("(assert (forall ((?t A) (?x Real) (?y Real)) (= ({} ?t (wrap-rat ?x) (wrap-rat 0)) (wrap-rat 1))))", "pow"));
    res.push(format!("(assert (forall ((?t A) (?x Real) (?y Real)) (= ({} ?t (wrap-rat ?x)) (wrap-rat ({} ?x (/ 1 2))))))", "sqrt", "^"));
    res.push(format!("(assert (forall ((?t A) (?x Real) (?y Real)) (= ({} ?t (wrap-rat ?x)) (wrap-rat ({} ?x (/ 1 3))))))", "cbrt", "^"));
    res.push(format!(
        "(assert (forall ((?t A) (?x Real)) (= ({} ?t (wrap-rat ?x)) (wrap-rat ({} ?x)))))",
        "neg", "-"
    ));
    res.push(format!(
        "(assert (forall ((?t A) (?x Real)) (= ({} ?t (wrap-rat ?x)) (wrap-rat ({} ?x)))))",
        "fabs", "abs"
    ));

    res
}

fn wrap_ints(sexp: Sexp) -> Sexp {
    match sexp {
        Sexp::List(l) => Sexp::List(l.into_iter().map(wrap_ints).collect()),
        Sexp::String(s) => {
            if s.parse::<i64>().is_ok() {
                Sexp::List(vec![Sexp::String("wrap-rat".to_string()), Sexp::String(s)])
            } else if let Ok(num) = s.parse::<Ratio<BigInt>>() {
                let rat_sexp = Sexp::List(vec![
                    Sexp::String("/".to_string()),
                    Sexp::String(num.numer().to_string()),
                    Sexp::String(num.denom().to_string()),
                ]);
                Sexp::List(vec![Sexp::String("wrap-rat".to_string()), rat_sexp])
            } else {
                Sexp::String(s)
            }
        }
        Empty => Empty,
    }
}

fn pat_to_z3_string<L: Language + Display>(pat: &PatternAst<L>) -> String {
    let sexp = pat.to_sexp();
    wrap_ints(sexp).to_string()
}

fn get_z3_rewrites<L, A>(rules: &[egg::Rewrite<L, A>]) -> Vec<String>
where
    L: Language + Display + 'static,
    A: Analysis<L> + Default,
{
    let mut results = get_const_fold_rewrites();
    for rule in rules {
        let left_pat = rule.searcher.get_pattern_ast().unwrap();
        let right_pat = rule.applier.get_pattern_ast().unwrap();
        let left = pat_to_z3_string(left_pat);
        let right = pat_to_z3_string(right_pat);
        let mut vars: HashSet<String> = Default::default();
        for node in left_pat.as_ref() {
            if let ENodeOrVar::Var(v) = node {
                vars.insert(v.to_string());
            }
        }
        for node in right_pat.as_ref() {
            if let ENodeOrVar::Var(v) = node {
                vars.insert(v.to_string());
            }
        }

        let final_str = if vars.len() == 0 {
            format!("(assert (= {} {}))", left, right)
        } else {
            let vars_str = format!(
                "({})",
                vars.iter()
                    .map(|v| format!("({} A)", v))
                    .collect::<Vec<_>>()
                    .join(" ")
            );

            format!(
                "(assert (forall {} (! (= {} {}) :pattern {})))",
                vars_str, left, right, left
            )
        };
        results.push(final_str);
    }

    results
}

fn test_z3<L, A>(
    rules: &[egg::Rewrite<L, A>],
    start: &egg::RecExpr<L>,
    end: &egg::RecExpr<L>,
) -> String
where
    L: Language + Display + 'static,
    A: Analysis<L> + Default,
{
    let quantified_rewrites = get_z3_rewrites(rules);
    let (funs, consts) = get_all_z3_funcs_consts(rules, start, end);

    let goal_string = format!(
        "(assert (not (= {} {})))",
        wrap_ints(start.to_sexp()),
        wrap_ints(end.to_sexp())
    );

    let mut z3_process = Command::new("z3")
        .arg("-smt2")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let z3_input = vec![
        "(set-option :produce-proofs true)".to_string(),
        "(set-option :auto-config false)".to_string(),
        "(set-option :smt.qi.eager_threshold 2000)".to_string(),
        "(set-option :smt.mbqi false)".to_string(),
        "(set-option :smt.ematching true)".to_string(),
        "(declare-sort A)".to_string(),
        consts.join("\n"),
        funs.join("\n"),
        quantified_rewrites.join("\n"),
        goal_string,
        "(check-sat)".to_string(),
        "(get-proof)".to_string(),
    ]
    .join("\n");

    //println!("{}", z3_input);

    let z3_in = z3_process.stdin.as_mut().unwrap();
    z3_in.write_all(z3_input.as_bytes()).unwrap();

    drop(z3_in);

    let TIMEOUT = Duration::from_secs(120);
    let mut timed_out = false;

    let _status_code = match z3_process.wait_timeout(TIMEOUT).unwrap() {
        Some(status) => status.code(),
        None => {
            timed_out = true;
            println!("timeout!");
            //println!("{}", start);
            //println!("{}", end);
            z3_process.kill().unwrap();
            z3_process.wait().unwrap().code()
        }
    };

    let mut output = String::new();
    z3_process
        .stdout
        .unwrap()
        .read_to_string(&mut output)
        .unwrap();

    if !timed_out && !output.starts_with("unsat\n") {
        println!("Z3 returned unknown!");
        //println!("{}", output);
    }
    return output;
}

fn count_string_in_sexp(sexp: &Sexp, func: &str) -> usize {
    match sexp {
        Sexp::List(l) => l.iter().map(|s| count_string_in_sexp(s, func)).sum(),
        Sexp::String(s) => {
            if s == func {
                1
            } else {
                0
            }
        }
        Sexp::Empty => 0,
    }
}

#[cfg(feature = "reports")]
mod proofbench {
    use super::*;
    use std::fs;
    use std::fs::{File, OpenOptions};
    use std::io::Write;
    use std::path::Path;
    use symbolic_expressions::{parser, Sexp};

    fn unwrap_sexp_list<'a>(sexp: &'a Sexp) -> &'a Vec<Sexp> {
        if let Sexp::List(l) = sexp {
            return l;
        } else {
            panic!("Expected a list, got: {}", sexp);
        }
    }

    fn unwrap_sexp_string<'a>(sexp: &'a Sexp) -> &'a str {
        if let Sexp::String(s) = sexp {
            return s;
        } else {
            panic!("Expected a string, got: {}", sexp);
        }
    }

    fn herbie_benchmark_proof(
        mut runner: Runner,
        mut runner_eqcheck: Runner,
        mut runner_upwards: Runner,
        mut runner_low_node_limit: Runner,
        start_parsed: RecExpr,
        end_parsed: RecExpr,
        rules: &[Rewrite],
    ) -> String {
        //println!("Testing {} \n {}", start_parsed, end_parsed);

        let start_egg_run = Instant::now();
        runner = runner.run(rules);
        let egg_run_duration = start_egg_run.elapsed().as_millis();

        let start_upwards_run = Instant::now();
        runner_upwards = runner_upwards.run(rules);
        let upwards_run_duration = start_upwards_run.elapsed().as_millis();
        //runner_upwards.print_report();

        let start_z3 = Instant::now();
        let z3_res = test_z3(&rules, &start_parsed, &end_parsed);
        let end_z3 = start_z3.elapsed().as_millis();

        let z3_len = if !z3_res.starts_with("unsat\n") {
            "#f".to_string()
        } else {
            match parser::parse_str(&z3_res[6..]) {
                Ok(z3_res_parsed) => {
                    format!("{}", count_string_in_sexp(&z3_res_parsed, "quant-inst"))
                }
                Err(_) => "#f".to_string(),
            }
        };

        let start_normal = Instant::now();
        let mut normal = runner.explain_equivalence(&start_parsed, &end_parsed, 0, false);
        let duration_normal = start_normal.elapsed().as_millis();
        normal.check_proof(rules);

        let equalities_normal = normal.get_grounded_equalities();
        let equalities_reduced_normal = Explanation::<L>::reduce_equalities(&equalities_normal);

        let start_slow = Instant::now();
        let mut slow = runner.explain_equivalence(&start_parsed, &end_parsed, 10, true);
        let duration_slow = start_slow.elapsed().as_millis();
        slow.check_proof(rules);

        let equalities_greedy = slow.get_grounded_equalities();
        let equalities_reduced_greedy = Explanation::<L>::reduce_equalities(&equalities_greedy);


        let start_eqcheck_run = Instant::now();
        runner_eqcheck = runner_eqcheck.run(rules);
        let eqcheck_run_duration = start_eqcheck_run.elapsed().as_millis();

        let eqcheck_normal_time;
        let eqcheck_normal_len;
        let eqcheck_normal_tree_size;
        if runner_eqcheck.egraph.add_expr(&start_parsed)
            != runner_eqcheck.egraph.add_expr(&end_parsed)
        {
            eqcheck_normal_time = "#f".to_string();
            eqcheck_normal_len = "#f".to_string();
            eqcheck_normal_tree_size = "#f".to_string();
        } else {
            let eqcheck_normal_instant = Instant::now();
            let mut eqcheck_normal =
                runner_eqcheck.explain_equivalence(&start_parsed, &end_parsed, 10, true);
            eqcheck_normal_time = format!("{}", eqcheck_normal_instant.elapsed().as_millis());
            eqcheck_normal.check_proof(rules);
            eqcheck_normal_len = format!("{}", eqcheck_normal.get_flat_sexps().len());
            eqcheck_normal_tree_size = format!("{}", eqcheck_normal.get_tree_size());
        }

        let upwards_normal_time;
        let upwards_normal_len;
        let upwards_normal_tree_size;
        if runner_upwards.egraph.add_expr(&start_parsed)
            != runner_upwards.egraph.add_expr(&end_parsed)
        {
            upwards_normal_time = "#f".to_string();
            upwards_normal_len = "#f".to_string();
            upwards_normal_tree_size = "#f".to_string();
        } else {
            let upwards_normal_instant = Instant::now();
            let mut upwards_normal =
                runner_upwards.explain_equivalence(&start_parsed, &end_parsed, 10, true);
            upwards_normal_time = format!("{}", upwards_normal_instant.elapsed().as_millis());
            upwards_normal.check_proof(rules);
            upwards_normal_len = format!("{}", upwards_normal.get_flat_sexps().len());
            upwards_normal_tree_size = format!("{}", upwards_normal.get_tree_size());
        }

        let start_low = Instant::now();
        runner_low_node_limit = runner_low_node_limit.run(rules);
        let egg_low_duration = start_egg_run.elapsed().as_millis();
        let low_greedy_time;
        let low_optimal_time;
        let low_greedy_flat_size;
        let low_optimal_flat_size;
        let low_greedy_dag_size;
        let low_optimal_dag_size;
        let mut skip_optimal = false;
        for class in runner_low_node_limit.egraph.classes() {
            if class.len() > 200 {
                skip_optimal = true;
            }
        }
        if skip_optimal
            || runner_low_node_limit.egraph.add_expr(&start_parsed)
                != runner_low_node_limit.egraph.add_expr(&end_parsed)
        {
            low_greedy_time = "#f".to_string();
            low_optimal_time = "#f".to_string();
            low_greedy_flat_size = "#f".to_string();
            low_optimal_flat_size = "#f".to_string();
            low_greedy_dag_size = "#f".to_string();
            low_optimal_dag_size = "#f".to_string();
        } else {
            let low_greedy_instant = Instant::now();
            let mut low_greedy =
                runner_low_node_limit.explain_equivalence(&start_parsed, &end_parsed, 10, true);
            low_greedy_time = format!("{}", low_greedy_instant.elapsed().as_millis());
            low_greedy.check_proof(rules);
            low_greedy_flat_size = format!("{}", low_greedy.get_flat_sexps().len());
            low_greedy_dag_size = format!("{}", low_greedy.get_tree_size());

            let low_optimal_instant = Instant::now();
            let mut low_optimal = runner_low_node_limit.explain_equivalence(
                &start_parsed,
                &end_parsed,
                usize::MAX,
                false,
            );
            low_optimal_time = format!("{}", low_optimal_instant.elapsed().as_millis());
            low_optimal.check_proof(rules);
            low_optimal_flat_size = format!("{}", low_optimal.get_flat_sexps().len());
            low_optimal_dag_size = format!("{}", low_optimal.get_tree_size());
            println!("({}, {})", low_greedy_flat_size, low_optimal_flat_size);
        }

        let normal_flat_len = normal.get_flat_sexps().len();
        format!(
            "({} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {})",
            &start_parsed,
            &end_parsed,
            duration_normal,
            duration_slow,
            normal_flat_len,
            slow.get_flat_sexps().len(),
            normal.get_tree_size(),
            slow.get_tree_size(),
            end_z3,
            z3_len,
            egg_run_duration,
            upwards_normal_time,
            upwards_normal_len,
            upwards_normal_tree_size,
            upwards_run_duration,
            low_greedy_time,
            low_optimal_time,
            low_greedy_flat_size,
            low_optimal_flat_size,
            low_greedy_dag_size,
            low_optimal_dag_size,
            eqcheck_normal_time,
            eqcheck_normal_len,
            eqcheck_normal_tree_size,
            eqcheck_run_duration,
            equalities_reduced_normal,
            equalities_reduced_greedy,
        )
    }

    fn herbie_runner(
        expressions: &Sexp,
        node_limit: usize,
        timeout: u64,
        start: &RecExpr,
        end: &RecExpr,
        use_hook: bool,
        use_both: bool,
    ) -> Runner {
        let start_cloned = start.clone();
        let end_cloned = end.clone();
        let mut runner = Runner::new(Default::default())
            .with_explanations_enabled()
            .with_node_limit(node_limit)
            .with_iter_limit(usize::MAX) // should never hit
            .with_time_limit(Duration::from_secs(timeout))
            .with_hook(|r| {
                if r.egraph.analysis.unsound.load(Ordering::SeqCst) {
                    Err("Unsoundness detected".into())
                } else {
                    Ok(())
                }
            });

        if use_hook {
            runner = runner.with_hook(move |r| {
                let res = if r.egraph.add_expr(&start_cloned) == r.egraph.add_expr(&end_cloned) {
                    Err("Finished".into())
                } else {
                    Ok(())
                };
                r.egraph.rebuild();
                return res;
            });
        }
        for expr in unwrap_sexp_list(expressions) {
            let parsed: egg::RecExpr<_> = unwrap_sexp_string(expr).parse().unwrap();
            runner = runner.with_expr(&parsed);
        }

        if use_both {
            runner = runner.with_expr(end);
        }
        return runner;
    }

    fn herbie_benchmark_example(example: &str, output: &mut File, skip: &mut usize) {
        let is_f64 = example.contains("f64");
        let parsed: Sexp = parser::parse_str(example).unwrap();
        let e_proofs = unwrap_sexp_list(&parsed);
        let expressions = &e_proofs[0];
        let proofs = &e_proofs[1];
        let mut proofs_sexps = unwrap_sexp_list(proofs).clone();
        if proofs_sexps.len() == 0 {
            return;
        }

        let mut rng = rand::thread_rng();
        proofs_sexps.shuffle(&mut rng);
        for proof in proofs_sexps.iter().take(2) {
            let epair = unwrap_sexp_list(proof);
            if epair[0] == epair[1] {
                continue;
            }

            *skip += 1;
            let skip_copy = *skip;
            let p_copy = proof.clone();
            let exprs_copy = expressions.clone();
            let h = thread::spawn(move || {
                let rules = math_rules(if is_f64 { "f64" } else { "f32" });
                let pair = unwrap_sexp_list(&p_copy);
                let start_parsed: egg::RecExpr<_> = unwrap_sexp_string(&pair[0]).parse().unwrap();
                let end_parsed: egg::RecExpr<_> = unwrap_sexp_string(&pair[1]).parse().unwrap();

                let mut runner = herbie_runner(
                    &exprs_copy,
                    5000,
                    20,
                    &start_parsed,
                    &end_parsed,
                    false,
                    false,
                );
                let mut runner_eqcheck = herbie_runner(
                    &exprs_copy,
                    5000,
                    20,
                    &start_parsed,
                    &end_parsed,
                    false,
                    true,
                );
                let mut runner_upwards = herbie_runner(
                    &exprs_copy,
                    20000,
                    20,
                    &start_parsed,
                    &end_parsed,
                    true,
                    true,
                );
                let limit = if skip_copy % 20 == 0 { 5000 } else { 0 };
                let mut runner_low_limit = herbie_runner(
                    &exprs_copy,
                    limit,
                    20,
                    &start_parsed,
                    &end_parsed,
                    false,
                    false,
                );
                runner_upwards.upwards_merging_enabled = true;

                herbie_benchmark_proof(
                    runner,
                    runner_eqcheck,
                    runner_upwards,
                    runner_low_limit,
                    start_parsed,
                    end_parsed,
                    &rules,
                )
            });
            match h.join() {
                Ok(res) => {
                    output.write(res.as_bytes()).unwrap();
                    output.write("\n".as_bytes()).unwrap();
                    ()
                }
                Err(_) => {
                    print!("!");
                    ()
                }
            }
            output.flush().unwrap();
            print!(".");
            std::io::stdout().flush().unwrap();
        }
    }

    fn herbie_benchmark_file(file: &Path, output: &mut File, skip: &mut usize) {
        println!("Benchmarking {}", file.display());
        let contents = fs::read_to_string(file).expect("Something went wrong reading the file");
        let split: Vec<&str> = contents.split("\n").collect();
        for example in split {
            if example != "" {
                herbie_benchmark_example(example, output, skip);
            }
        }
    }

    #[test]
    fn herbie_benchmark() {
        let mut output_file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open("proof_report/herbie-bench-results.txt")
            .unwrap();
        let paths = fs::read_dir("./herbie/reports/egg-proof-examples").unwrap();

        let mut skip = 0;

        for path in paths {
            let path = path.unwrap().path();
            herbie_benchmark_file(&path, &mut output_file, &mut skip);
        }
    }
}
