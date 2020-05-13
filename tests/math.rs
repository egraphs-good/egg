use egg::{rewrite as rw, *};

use log::trace;
use ordered_float::NotNan;

pub type EGraph = egg::EGraph<Math, Meta>;
pub type Rewrite = egg::Rewrite<Math, Meta>;

type Constant = NotNan<f64>;

define_language! {
    pub enum Math {
        Diff = "d",
        Integral = "i",

        Constant(Constant),
        Add = "+",
        Sub = "-",
        Mul = "*",
        Div = "/",
        Pow = "pow",
        Exp = "exp",
        Ln = "ln",
        Sqrt = "sqrt",

        Sin = "sin",
        Cos = "cos",

        Variable(String),
    }
}

// You could use egg::AstSize, but this is useful for debugging, since
// it will really try to get rid of the Diff operator
struct MathCostFn;
impl egg::CostFunction<Math> for MathCostFn {
    type Cost = usize;
    fn cost(&mut self, enode: &ENode<Math, Self::Cost>) -> Self::Cost {
        let op_cost = match enode.op {
            Math::Diff => 100,
            Math::Integral => 100,
            _ => 1,
        };
        op_cost + enode.children.iter().sum::<usize>()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Meta {
    pub cost: usize,
    pub best: RecExpr<Math>,
}

fn eval(op: Math, args: &[Constant]) -> Option<Constant> {
    let a = |i| args.get(i).cloned();
    trace!("{} {:?} = ...", op, args);
    let zero = Some(0.0.into());
    let res = match op {
        Math::Add => Some(a(0)? + a(1)?),
        Math::Sub => Some(a(0)? - a(1)?),
        Math::Mul => Some(a(0)? * a(1)?),
        Math::Div if a(1) != zero => Some(a(0)? / a(1)?),
        _ => None,
    };
    trace!("{} {:?} = {:?}", op, args, res);
    res
}

impl Metadata<Math> for Meta {
    type Error = std::convert::Infallible;
    fn merge(&self, other: &Self) -> Self {
        if self.cost <= other.cost {
            self.clone()
        } else {
            other.clone()
        }
    }

    fn make(egraph: &EGraph, enode: &ENode<Math>) -> Self {
        let meta = |i: Id| &egraph[i].metadata;
        let enode = {
            let const_args: Option<Vec<Constant>> = enode
                .children
                .iter()
                .map(|id| match meta(*id).best.as_ref().op {
                    Math::Constant(c) => Some(c),
                    _ => None,
                })
                .collect();

            const_args
                .and_then(|a| eval(enode.op.clone(), &a))
                .map(|c| ENode::leaf(Math::Constant(c)))
                .unwrap_or_else(|| enode.clone())
        };

        let best: RecExpr<_> = enode.map_children(|c| meta(c).best.clone()).into();
        let cost = MathCostFn.cost(&enode.map_children(|c| meta(c).cost));
        Self { best, cost }
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let best = egraph[id].metadata.best.as_ref();
        if best.children.is_empty() {
            let leaf = ENode::leaf(best.op.clone());
            let added = egraph.add(leaf);
            let id = egraph.union(id, added);

            // to not prune, comment this out
            egraph[id].nodes.retain(|n| n.children.is_empty());

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

fn c_is_const(egraph: &mut EGraph, _: Id, subst: &Subst) -> bool {
    let c = "?c".parse().unwrap();
    egraph[subst[&c]].nodes.iter().any(|n| match n.op {
        Math::Constant(_) => true,
        _ => false,
    })
}

fn c_is_const_or_var_and_not_x(egraph: &mut EGraph, _: Id, subst: &Subst) -> bool {
    let c = "?c".parse().unwrap();
    let x = "?x".parse().unwrap();
    let is_const_or_var = egraph[subst[&c]].nodes.iter().any(|n| match &n.op {
        Math::Constant(_) | Math::Variable(_) => true,
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
            .any(|n| matches!(n.op, Math::Variable(_)))
    }
}

fn is_not_zero(var: &'static str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    let zero = enode!(Math::Constant(0.0.into()));
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

egg::test_fn! {
    math_associate_adds, [
        rw!("comm-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    ],
    runner = Runner::new()
        .with_iter_limit(7)
        .with_scheduler(SimpleScheduler),
    "(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))"
    =>
    "(+ 7 (+ 6 (+ 5 (+ 4 (+ 3 (+ 2 1))))))"
    @check |r: Runner<Math, ()>| assert_eq!(r.egraph.number_of_classes(), 127)
}

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
    runner = Runner::new().with_node_limit(75_000),
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
    runner = Runner::new()
        .with_time_limit(std::time::Duration::from_secs(10))
        .with_iter_limit(60)
        .with_node_limit(100_000)
        // HACK this needs to "see" the end expression
        .with_expr(&"(* x (- (* 3 x) 14))".parse().unwrap()),
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
