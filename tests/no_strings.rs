use egg::*;

define_language! {
    enum NoStrings {
        Num(i32),
        "🦑" = Squid([Id; 2]),
        "🐝" = Bee(Id),
        Symbol(Symbol),
    }
}

fn make_rules() -> Vec<Rewrite<NoStrings, (), i32>> {
    let searcher: Pattern<NoStrings, _> = Pattern::new(RecExpr::from(vec![
        ENodeOrVar::Var(12 as i32),
        ENodeOrVar::Var(13 as i32),
        ENodeOrVar::ENode(NoStrings::Squid([0.into(), 1.into()])),
    ]));
    let applier: Pattern<NoStrings, _> = Pattern::new(RecExpr::from(vec![
        ENodeOrVar::Var(13 as i32),
        ENodeOrVar::ENode(NoStrings::Bee(0.into())),
    ]));
    vec![crate::Rewrite::new("squid to bee".to_string(), searcher, applier).unwrap()]
}

#[test]
fn simple_tests() {
    assert_eq!(
        simplify(RecExpr::from(vec![
            NoStrings::Num(77 as i32),
            NoStrings::Num(88 as i32),
            NoStrings::Squid([0.into(), 1.into()]),
        ])),
        RecExpr::from(vec![NoStrings::Num(88 as i32), NoStrings::Bee(0.into()),])
    );
}

/// simplify using egg, and pretty print it back out
fn simplify(expr: RecExpr<NoStrings>) -> RecExpr<NoStrings> {
    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let runner: Runner<NoStrings, _, (), i32> =
        Runner::default().with_expr(&expr).run(&make_rules());

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);
    println!("Simplified {} to {} with cost {}", expr, best, best_cost);
    best
}
