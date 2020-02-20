use egg::{rewrite as rw, *};

use log::trace;
use ordered_float::NotNan;

pub type EGraph = egg::EGraph<Math, Meta>;
pub type Rewrite = egg::Rewrite<Math, Meta>;

type Constant = NotNan<f64>;

define_language! {
    pub enum Math {
        Diff = "d",

        Constant(Constant),
        Add = "+",
        Sub = "-",
        Mul = "*",
        Div = "/",
        Pow = "pow",
        Exp = "exp",
        Log = "log",
        Sqrt = "sqrt",
        Cbrt = "cbrt",
        Fabs = "fabs",

        Log1p = "log1p",
        Expm1 = "expm1",

        RealToPosit = "real->posit",
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
            _ => 1,
        };
        op_cost + enode.children.iter().sum::<usize>()
    }
}

#[derive(Debug, Clone)]
pub struct Meta {
    pub cost: usize,
    pub best: RecExpr<Math>,
}

fn eval(op: Math, args: &[Constant]) -> Option<Constant> {
    let a = |i| args.get(i).cloned();
    let res = match op {
        Math::Add => Some(a(0)? + a(1)?),
        Math::Sub => Some(a(0)? - a(1)?),
        Math::Mul => Some(a(0)? * a(1)?),
        Math::Div => Some(a(0)? / a(1)?),
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

    fn make(expr: ENode<Math, &Self>) -> Self {
        let expr = {
            let const_args: Option<Vec<Constant>> = expr
                .children
                .iter()
                .map(|meta| match meta.best.as_ref().op {
                    Math::Constant(c) => Some(c),
                    _ => None,
                })
                .collect();

            const_args
                .and_then(|a| eval(expr.op.clone(), &a))
                .map(|c| ENode::leaf(Math::Constant(c)))
                .unwrap_or(expr)
        };

        let best: RecExpr<_> = expr.map_children(|c| c.best.clone()).into();
        let cost = MathCostFn.cost(&expr.map_children(|c| c.cost));
        Self { best, cost }
    }

    fn modify(eclass: &mut EClass<Math, Self>) {
        // NOTE pruning vs not pruning is decided right here
        // not pruning would be just pushing instead of replacing
        let best = eclass.metadata.best.as_ref();
        if best.children.is_empty() {
            eclass.nodes = vec![ENode::leaf(best.op.clone())]
        }
    }
}

fn c_is_const_or_var_and_not_x(egraph: &mut EGraph, _: Id, subst: &Subst) -> bool {
    let c = "?c".parse().unwrap();
    let x = "?x".parse().unwrap();
    let is_const_or_var = egraph[subst[&c]].nodes.iter().any(|n| match n.op {
        Math::Constant(_) | Math::Variable(_) => true,
        _ => false,
    });
    is_const_or_var && subst[&x] != subst[&c]
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
    rw!("div-canon"; "(/ ?a ?b)" => "(* ?a (pow ?b -1))"),
    // rw!("canon-sub"; "(+ ?a (* -1 ?b))"   => "(- ?a ?b)"),
    // rw!("canon-div"; "(* ?a (pow ?b -1))" => "(/ ?a ?b)" if is_not_zero("?b")),

    rw!("zero-add"; "(+ ?a 0)" => "?a"),
    rw!("zero-mul"; "(* ?a 0)" => "0"),
    rw!("one-mul";  "(* ?a 1)" => "?a"),

    rw!("add-zero"; "?a" => "(+ ?a 0)"),
    rw!("mul-one";  "?a" => "(* ?a 1)"),

    rw!("cancel-sub"; "(- ?a ?a)" => "0"),
    rw!("cancel-div"; "(/ ?a ?a)" => "1"),

    rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
    rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),

    rw!("pow-intro"; "?a" => "(pow ?a 1)"),
    rw!("pow-mul"; "(* (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (+ ?b ?c))"),
    rw!("pow0"; "(pow ?x 0)" => "1"),
    rw!("pow1"; "(pow ?x 1)" => "?x"),
    rw!("pow2"; "(pow ?x 2)" => "(* ?x ?x)"),
    rw!("pow-recip"; "(pow ?x -1)" => "(/ 1 ?x)" if is_not_zero("?x")),

    rw!("d-variable"; "(d ?x ?x)" => "1"),
    rw!("d-constant"; "(d ?x ?c)" => "0" if c_is_const_or_var_and_not_x),

    rw!("d-add"; "(d ?x (+ ?a ?b))" => "(+ (d ?x ?a) (d ?x ?b))"),
    rw!("d-mul"; "(d ?x (* ?a ?b))" => "(+ (* ?a (d ?x ?b)) (* ?b (d ?x ?a)))"),

    rw!("d-power";
        "(d ?x (pow ?f ?g))" =>
        "(* (pow ?f ?g)
            (+ (* (d ?x ?f)
                  (/ ?g ?f))
               (* (d ?x ?g)
                  (log ?f))))"
        if is_not_zero("?f")
    ),
]}

#[test]
#[cfg_attr(feature = "parent-pointers", ignore)]
fn associate_adds() {
    let start = "(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))";
    let start_expr = start.parse().unwrap();

    let rules = &[
        rw!("comm-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    ];

    // Must specfify the () metadata so pruning doesn't mess us up here
    let egraph: egg::EGraph<Math, ()> = SimpleRunner::default()
        .with_iter_limit(7)
        .with_node_limit(8_000)
        .with_initial_match_limit(100_000) // disable banning
        .run_expr(start_expr, rules)
        .0;

    // there are exactly 127 non-empty subsets of 7 things
    assert_eq!(egraph.number_of_classes(), 127);
}

macro_rules! check {
    (
        $(#[$meta:meta])*
        $name:ident, $iters:literal, $limit:literal,
        $start:literal => $end:literal
    ) => {
        $(#[$meta])*
        #[test]
        fn $name() {
            let _ = env_logger::builder().is_test(true).try_init();
            let start_expr = $start.parse().expect(concat!("Failed to parse ", $start));
            let end_expr = $end.parse().expect(concat!("Failed to parse ", $end));

            let rules = rules();
            let (egraph, root, reason) = egg_bench(stringify!($name), || {
                let (mut egraph, root) = EGraph::from_expr(&start_expr);
                // add the end expr as well
                let _goal = egraph.add_expr(&end_expr);

                let (_, reason) = SimpleRunner::default()
                    .with_iter_limit($iters)
                    .with_node_limit($limit)
                    .run(&mut egraph, &rules);

                (egraph, root, reason)
            });

            println!("Stopped because {:?}", reason);
            let (cost, best) = Extractor::new(&egraph, MathCostFn).find_best(root);
            println!("Best ({}): {}", cost, best.pretty(40));

            // make sure that pattern search also works
            let pattern = Pattern::from(end_expr);
            let matches = pattern.search_eclass(&egraph, root);

            if matches.is_none() {
                println!("start: {}", start_expr.pretty(40));
                println!("start: {:?}", start_expr);
                panic!(
                    "\nCould not simplify\n{}\nto\n{}\nfound:\n{}",
                    $start,
                    $end,
                    best.pretty(40)
                );
            }
        }
    };
}

check!(
    #[should_panic(expected = "Could not simplify")]
    simplify_fail, 5, 1_000, "(+ x y)" => "(/ x y)"
);

check!(
    #[cfg_attr(feature = "parent-pointers", ignore)]
    simplify_add,   10,  1_000, "(+ x (+ x (+ x x)))" => "(* 4 x)"
);
check!(
    #[cfg_attr(feature = "parent-pointers", ignore)]
    simplify_const,  4,  1_000, "(+ 1 (- a (* (- 2 1) a)))" => "1"
);
check!(
    #[cfg_attr(feature = "parent-pointers", ignore)]
    simplify_root, 10, 75_000, r#"
          (/ 1
             (- (/ (+ 1 (sqrt five))
                   2)
                (/ (- 1 (sqrt five))
                   2)))
        "#
       => "(/ 1 (sqrt five))"
);

check!(powers,         10, 1_000, "(* (pow 2 x) (pow 2 y))" => "(pow 2 (+ x y))");

check!(diff_same,      10, 1_000, "(d x x)" => "1");
check!(diff_different, 10, 1_000, "(d x y)" => "0");
check!(diff_simple1,   10, 5_000, "(d x (+ 1 (* 2 x)))" => "2");
check!(diff_simple2,   10, 5_000, "(d x (+ 1 (* y x)))" => "y");

check!(
    #[cfg_attr(feature = "parent-pointers", ignore)]
    diff_power_simple, 20, 50_000, "(d x (pow x 3))" => "(* 3 (pow x 2))"
);
check!(
    #[cfg_attr(feature = "parent-pointers", ignore)]
    diff_power_harder, 50, 50_000,
    "(d x (- (pow x 3) (* 7 (pow x 2))))" =>
    "(* x (- (* 3 x) 14))"
);
