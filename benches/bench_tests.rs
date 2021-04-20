#[path = "../tests/math.rs"]
mod math;
use math::*;

#[path = "../tests/lambda.rs"]
mod lambda;
use lambda::*;

mod hard_lambda {
    use egg::{rewrite as rw, *};
    use ordered_float::NotNan;
    pub type EGraph = egg::EGraph<Math, ()>;
    pub type Rewrite = egg::Rewrite<Math, ()>;
    pub type Constant = NotNan<f64>;
    define_language! {
        pub enum Math {
            "+" = Add([Id; 2]),
            "-" = Sub([Id; 2]),
            "*" = Mul([Id; 2]),
            "/" = Div([Id; 2]),
            Constant(Constant),
            Symbol(Symbol),
        }
    }
    #[rustfmt::skip]
    pub fn rules() -> Vec<Rewrite> { vec![
        rw!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rw!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
        rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
    
        rw!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
    
        rw!("zero-add"; "(+ ?a 0)" => "?a"),
        rw!("zero-mul"; "(* ?a 0)" => "0"),
        rw!("one-mul";  "(* ?a 1)" => "?a"),
    
        rw!("add-zero"; "?a" => "(+ ?a 0)"),
        rw!("mul-one";  "?a" => "(* ?a 1)"),
    
        rw!("cancel-sub"; "(- ?a ?a)" => "0"),
    
        rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
        rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
    ]}

    pub fn saturate() -> EGraph {
        let rules: Vec<_> = rules();
        let expr1 = "(+ (* y (+ x y)) (- (+ x 2) (+ x x)))".parse().unwrap();
        let runner: Runner<Math, ()> = Runner::default()
            .with_expr(&expr1)
            // .with_node_limit(200_000)
            .with_node_limit(50_000)
            .with_iter_limit(1000)
            .with_time_limit(std::time::Duration::from_secs(4000))
            .run(&rules);
        println!("stop reason: {:?}", runner.stop_reason);
        println!(
            "egraph size: {} {}",
            runner.egraph.total_number_of_nodes(),
            runner.egraph.number_of_classes()
        );
        runner.egraph
    }
}

use hard_lambda::saturate;

iai::main!(
    diff_power_harder,
    diff_power_simple,
    integ_one,
    integ_part1,
    integ_part2,
    integ_part3,
    integ_sin,
    integ_x,
    math_associate_adds,
    math_diff_different,
    math_diff_ln,
    math_diff_same,
    math_diff_simple1,
    math_diff_simple2,
    math_powers,
    math_simplify_add,
    math_simplify_const,
    math_simplify_factor,
    math_simplify_root,
    lambda_compose,
    lambda_compose_many,
    lambda_fib,
    // lambda_function_repeat,
    lambda_if,
    lambda_if_elim,
    lambda_if_simple,
    lambda_let_simple,
    lambda_under,
    saturate
);
