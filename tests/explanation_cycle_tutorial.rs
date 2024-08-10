use egg::{rewrite as rw, *};

#[test]
fn repro_tutorial_cycle() {
    let rules: &[Rewrite<SymbolLang, ()>] = &[
        rw!("div-one"; "?x" => "(/ ?x 1)"),
        rw!("unsafe-invert-division"; "(/ ?a ?b)" => "(/ 1 (/ ?b ?a))"),
        rw!("simplify-frac"; "(/ ?a (/ ?b ?c))" => "(/ (* ?a ?c) (* (/ ?b ?c) ?c))"),
        rw!("cancel-denominator"; "(* (/ ?a ?b) ?b)" => "?a"),
        rw!("times-zero"; "(* ?a 0)" => "0"),
    ];

    let start = "(/ (* (/ 2 3) (/ 3 2)) 1)".parse().unwrap();
    let end = "1".parse().unwrap();
    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&start)
        .run(rules);

    println!(
        "{}",
        runner.explain_equivalence(&start, &end).get_flat_string()
    );
}
