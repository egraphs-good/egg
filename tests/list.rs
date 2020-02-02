use egg::*;
use log::*;

type Meta = ();
type Rewrite = egg::Rewrite<List, Meta>;

define_language! {
    enum List {
        Nil = "nil",
        Cons = "cons",
        List = "list",
        Variable(String),
    }
}

fn rules() -> Vec<Rewrite> {
    vec![
        rewrite!("fold_nil"; "nil" => "list"),
        rewrite!(
            "fold_cons";
            "(cons ?a (list ?tail...))" => "(list ?a ?tail...)"
        ),
    ]
}

fn prove_something(start: &str, rewrites: &[Rewrite], goals: &[&str]) {
    let _ = env_logger::builder().is_test(true).try_init();

    let start_expr: RecExpr<List> = start.parse().unwrap();
    let goal_exprs: Vec<_> = goals.iter().map(|g| g.parse().unwrap()).collect();

    let (egraph, _) = SimpleRunner::default()
        .with_iter_limit(20)
        .with_node_limit(5_000)
        .run_expr(start_expr.clone(), rewrites);

    for (i, (goal_expr, goal_str)) in goal_exprs.iter().zip(goals).enumerate() {
        info!("Trying to prove goal {}: {}", i, goal_str);
        let equivs = egraph.equivs(&start_expr, &goal_expr);
        if equivs.is_empty() {
            panic!("Couldn't prove goal {}: {}", i, goal_str);
        }
    }
}

#[test]
fn fold_em_up() {
    prove_something(
        "(cons a (cons b (cons c nil)))",
        &rules(),
        &[
            "(cons a (cons b (cons c list)))",
            "(cons a (cons b (list c)))",
            "(cons a (list b c))",
            "(list a b c)",
        ],
    );
}
