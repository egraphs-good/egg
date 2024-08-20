use egg::{Symbol, *};
use std::time::Duration;

define_language! {
    pub enum Math {
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "^" = Pow([Id; 2]),
        Const(u64),
        Var(Symbol),
    }
}

pub type EGraph = egg::EGraph<Math, ()>;
pub type Rewrite = egg::Rewrite<Math, ()>;
pub type Runner = egg::Runner<Math, (), ()>;

fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    |egraph, _, subst| true
}

#[test]
fn repro_cycle_existance() {
    let mut rules = vec![
        rewrite!("add_comm";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rewrite!("mul_comm";  "(* ?a ?b)"        => "(* ?b ?a)"),
        rewrite!("mul_zero"; "(* ?a 0)" => "0"),
        rewrite!("recip-mul-div"; "(* ?x (/ 1 ?x))" => "1" if is_not_zero("?x")),
    ];
    //rules.extend(rewrite!("add_assoc"; "(+ ?a (+ ?b ?c))" <=> "(+ (+ ?a ?b) ?c)"));
    rules.extend(rewrite!("mul_assoc"; "(* ?a (* ?b ?c))" <=> "(* (* ?a ?b) ?c)"));
    //rules.extend(rewrite!("add_zero"; "(+ ?a 0)" <=> "?a"));
    rules.extend(rewrite!("mul_one";  "(* ?a 1)" <=> "?a"));
    rules.extend(rewrite!("distribute"; "(* ?a (+ ?b ?c))" <=> "(+ (* ?a ?b) (* ?a ?c))"));
    rules.extend(rewrite!("div_canon"; "(/ ?a ?b)" <=> "(* ?a (^ ?b -1))" if is_not_zero("?b")));

    let start = "(+ (/ a b) c)".parse().unwrap();
    let end: RecExpr<Math> = "(/ (+ a (* b c)) b)".parse().unwrap();
    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&start)
        .with_expr(&end)
        .with_time_limit(Duration::from_secs(1000000000000))
        .with_iter_limit(6)
        .with_node_limit(usize::MAX)
        .run(&rules);

    println!(
        "{}",
        runner.explain_equivalence(&start, &end).get_flat_string()
    );
}
