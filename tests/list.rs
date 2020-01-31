use egg::*;
use log::*;

type Meta = ();
type Rewrite = egg::Rewrite<List, Meta>;

define_language! {
    enum List {
        Nil = "nil",
        Cons = "cons",
        List = "list",
        Variable(Name),
    }
}

fn rules() -> Vec<Rewrite> {
    vec![
        rw("fold_nil").p("nil").a("list").mk(),
        rw("fold_cons")
            .p("(cons ?a (list ?tail...))")
            .a("(list ?a ?tail...)")
            .mk(),
    ]
}

fn prove_something(start: &str, rewrites: &[Rewrite], goals: &[&str]) {
    let _ = env_logger::builder().is_test(true).try_init();

    let start_expr = List::parse_expr(start).unwrap();
    let goal_exprs: Vec<_> = goals.iter().map(|g| List::parse_expr(g).unwrap()).collect();

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
