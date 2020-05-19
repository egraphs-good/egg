use egg::{rewrite as rw, *};
use std::str::FromStr;

use ordered_float::NotNan;

#[derive(Default)]
pub struct MathLanguage;

pub type EGraph = egg::EGraph<MathLanguage>;
pub type Rewrite = egg::Rewrite<MathLanguage>;

pub type Constant = NotNan<f64>;

impl_enode! {
    pub enum Op {
        "d" = Diff(Id, Id),
        "i" = Integral(Id, Id),

        "+" = Add(Id, Id),
        "-" = Sub(Id, Id),
        "*" = Mul(Id, Id),
        "/" = Div(Id, Id),
        "pow" = Pow(Id, Id),
        "ln" = Ln(Id),
        "sqrt" = Sqrt(Id),

        "sin" = Sin(Id),
        "cos" = Cos(Id),

        Constant(Constant),
        Variable(String),
    }
}

// You could use egg::AstSize, but this is useful for debugging, since
// it will really try to get rid of the Diff operator
struct MathCostFn;
impl egg::CostFunction<MathLanguage> for MathCostFn {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &Op, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            Op::Diff(..) => 100,
            Op::Integral(..) => 100,
            _ => 1,
        };
        enode.fold(op_cost, |sum, i| sum + costs(i))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Meta {
    pub cost: usize,
    pub constant: Option<Constant>,
}

impl Language for MathLanguage {
    type ENode = Op;
    type Metadata = Meta;

    fn metadata_merge(&self, to: &mut Meta, from: Meta) -> bool {
        if let (Some(c1), Some(c2)) = (to.constant, from.constant) {
            assert_eq!(c1, c2);
        }

        // if from.cost < to.cost {
        if from.constant.is_some() && to.constant.is_none() {
            *to = from;
            true
        } else {
            false
        }
    }

    fn metadata_make(egraph: &mut egg::EGraph<Self>, enode: &Self::ENode) -> Self::Metadata {
        let meta = |i: Id| &egraph[i].metadata;

        let x = |&i| meta(i).constant;
        let eval = || {
            Some(match enode {
                Op::Constant(c) => c.clone(),
                Op::Add(a, b) => x(a)? + x(b)?,
                Op::Sub(a, b) => x(a)? - x(b)?,
                Op::Mul(a, b) => x(a)? * x(b)?,
                Op::Div(a, b) if x(b) != Some(0.0.into()) => x(a)? / x(b)?,
                _ => return None,
            })
        };

        let cost = MathCostFn.cost(&enode, |i| meta(i).cost);

        Meta {
            cost,
            constant: eval(),
        }
    }

    fn metadata_modify(egraph: &mut egg::EGraph<Self>, id: Id) {
        let class = &mut egraph[id];
        if let Some(c) = class.metadata.constant {
            let added = egraph.add(Op::Constant(c));
            let (id, did_something) = egraph.union(id, added);
            if did_something || true {
                // to not prune, comment this out
                egraph[id].nodes.retain(|n| n.is_leaf());

                assert!(
                    !egraph[id].nodes.is_empty(),
                    "empty eclass! {:#?}",
                    egraph[id]
                );
                #[cfg(debug_assertions)]
                egraph[id].assert_unique_leaves();
            }
        }
    }
}

fn c_is_const(egraph: &mut EGraph, _: Id, subst: &Subst) -> bool {
    let c = "?c".parse().unwrap();
    egraph[subst[&c]].nodes.iter().any(|n| match n {
        Op::Constant(_) => true,
        _ => false,
    })
}

fn c_is_const_or_var_and_not_x(egraph: &mut EGraph, _: Id, subst: &Subst) -> bool {
    let c = "?c".parse().unwrap();
    let x = "?x".parse().unwrap();
    let is_const_or_var = egraph[subst[&c]].nodes.iter().any(|n| match n {
        Op::Constant(_) | Op::Variable(_) => true,
        _ => false,
    });
    is_const_or_var && egraph.find(subst[&x]) != egraph.find(subst[&c])
}

fn is_var(var: &'static str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        egraph[subst[&var]]
            .nodes
            .iter()
            .any(|n| matches!(n, Op::Variable(..)))
    }
}

fn is_not_zero(var: &'static str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    let zero = Op::Constant(0.0.into());
    move |egraph, _, subst| !egraph[subst[&var]].nodes.contains(&zero)
}

#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite> { vec![
    rw!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
    rw!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
    rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),

    rw!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
    rw!("div-canon"; "(/ ?a ?b)" => "(* ?a (pow ?b -1))" if is_not_zero("?b")),
    // rw!("canon-sub"; "(+ ?a (* -1 ?b))"   => "(- ?a ?b)"),
    // rw!("canon-div"; "(* ?a (pow ?b -1))" => "(/ ?a ?b)" if is_not_zero("?b")),

    rw!("zero-add"; "(+ ?a 0)" => "?a"),
    rw!("zero-mul"; "(* ?a 0)" => "0"),
    rw!("one-mul";  "(* ?a 1)" => "?a"),

    rw!("add-zero"; "?a" => "(+ ?a 0)"),
    rw!("mul-one";  "?a" => "(* ?a 1)"),

    rw!("cancel-sub"; "(- ?a ?a)" => "0"),
    rw!("cancel-div"; "(/ ?a ?a)" => "1" if is_not_zero("?a")),

    rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
    rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),

    rw!("pow-intro"; "?a" => "(pow ?a 1)"),
    rw!("pow-mul"; "(* (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (+ ?b ?c))"),
    rw!("pow0"; "(pow ?x 0)" => "1"
        if is_not_zero("?x")),
    rw!("pow1"; "(pow ?x 1)" => "?x"),
    rw!("pow2"; "(pow ?x 2)" => "(* ?x ?x)"),
    rw!("pow-recip"; "(pow ?x -1)" => "(/ 1 ?x)"
        if is_not_zero("?x")),
    rw!("recip-mul-div"; "(* ?x (/ 1 ?x))" => "1" if is_not_zero("?x")),

    rw!("d-variable"; "(d ?x ?x)" => "1" if is_var("?x")),
    rw!("d-constant"; "(d ?x ?c)" => "0" if is_var("?x") if c_is_const_or_var_and_not_x),

    rw!("d-add"; "(d ?x (+ ?a ?b))" => "(+ (d ?x ?a) (d ?x ?b))"),
    rw!("d-mul"; "(d ?x (* ?a ?b))" => "(+ (* ?a (d ?x ?b)) (* ?b (d ?x ?a)))"),

    rw!("d-sin"; "(d ?x (sin ?x))" => "(cos ?x)"),
    rw!("d-cos"; "(d ?x (cos ?x))" => "(* -1 (sin ?x))"),

    rw!("d-ln"; "(d ?x (ln ?x))" => "(/ 1 ?x)" if is_not_zero("?x")),

    rw!("d-power";
        "(d ?x (pow ?f ?g))" =>
        "(* (pow ?f ?g)
            (+ (* (d ?x ?f)
                  (/ ?g ?f))
               (* (d ?x ?g)
                  (ln ?f))))"
        if is_not_zero("?f")
        if is_not_zero("?g")
    ),

    rw!("i-one"; "(i 1 ?x)" => "?x"),
    rw!("i-power-const"; "(i (pow ?x ?c) ?x)" =>
        "(/ (pow ?x (+ ?c 1)) (+ ?c 1))" if c_is_const),
    rw!("i-cos"; "(i (cos ?x) ?x)" => "(sin ?x)"),
    rw!("i-sin"; "(i (sin ?x) ?x)" => "(* -1 (cos ?x))"),
    rw!("i-sum"; "(i (+ ?f ?g) ?x)" => "(+ (i ?f ?x) (i ?g ?x))"),
    rw!("i-dif"; "(i (- ?f ?g) ?x)" => "(- (i ?f ?x) (i ?g ?x))"),
    rw!("i-parts"; "(i (* ?a ?b) ?x)" =>
        "(- (* ?a (i ?b ?x)) (i (* (d ?x ?a) (i ?b ?x)) ?x))"),
]}

// egg::test_fn! {
//     math_associate_adds, [
//         rw!("comm-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
//         rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
//     ],
//     runner = Runner::new()
//         .with_iter_limit(7)
//         .with_scheduler(SimpleScheduler),
//     "(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))"
//     =>
//     "(+ 7 (+ 6 (+ 5 (+ 4 (+ 3 (+ 2 1))))))"
//     @check |r: Runner<Op, ()>| assert_eq!(r.egraph.number_of_classes(), 127)
// }

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    math_fail, rules(),
    "(+ x y)" => "(/ x y)"
}

egg::test_fn! {math_simplify_add, rules(), "(+ x (+ x (+ x x)))" => "(* 4 x)" }
egg::test_fn! {math_powers, rules(), "(* (pow 2 x) (pow 2 y))" => "(pow 2 (+ x y))"}

egg::test_fn! {
    math_simplify_const, rules(),
    "(+ 1 (- a (* (- 2 1) a)))" => "1"
}

egg::test_fn! {
    math_simplify_root, rules(),
    runner = Runner::default().with_node_limit(75_000),
    r#"
    (/ 1
       (- (/ (+ 1 (sqrt five))
             2)
          (/ (- 1 (sqrt five))
             2)))"#
    =>
    "(/ 1 (sqrt five))"
}

egg::test_fn! {math_diff_same,      rules(), "(d x x)" => "1"}
egg::test_fn! {math_diff_different, rules(), "(d x y)" => "0"}
egg::test_fn! {math_diff_simple1,   rules(), "(d x (+ 1 (* 2 x)))" => "2"}
egg::test_fn! {math_diff_simple2,   rules(), "(d x (+ 1 (* y x)))" => "y"}
egg::test_fn! {math_diff_ln,        rules(), "(d x (ln x))" => "(/ 1 x)"}

egg::test_fn! {
    diff_power_simple, rules(),
    "(d x (pow x 3))" => "(* 3 (pow x 2))"
}

egg::test_fn! {
    diff_power_harder, rules(),
    runner = Runner::default()
        .with_time_limit(std::time::Duration::from_secs(10))
        .with_iter_limit(60)
        .with_node_limit(100_000)
        // HACK this needs to "see" the end expression
        .with_expr(RecExpr::from_str("(* x (- (* 3 x) 14))").unwrap()),
    "(d x (- (pow x 3) (* 7 (pow x 2))))"
    =>
    "(* x (- (* 3 x) 14))"
}

egg::test_fn! {
    integ_one, rules(), "(i 1 x)" => "x"
}

egg::test_fn! {
    integ_sin, rules(), "(i (cos x) x)" => "(sin x)"
}

egg::test_fn! {
    integ_x, rules(), "(i (pow x 1) x)" => "(/ (pow x 2) 2)"
}

egg::test_fn! {
    integ_part1, rules(), "(i (* x (cos x)) x)" => "(+ (* x (sin x)) (cos x))"
}

egg::test_fn! {
    integ_part2, rules(),
    "(i (* (cos x) x) x)" => "(+ (* x (sin x)) (cos x))"
}

egg::test_fn! {
    integ_part3, rules(), "(i (ln x) x)" => "(- (* x (ln x)) x)"
}
