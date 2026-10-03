#![cfg(feature = "lp")]

use std::collections::{BTreeMap, BTreeSet};

use egg::*;

#[derive(Clone)]
struct OpCosts(BTreeMap<String, f64>);

impl LpCostFunction<SymbolLang, ()> for OpCosts {
    fn node_cost(
        &mut self,
        _egraph: &EGraph<SymbolLang, ()>,
        _eclass: Id,
        enode: &SymbolLang,
    ) -> f64 {
        self.0[enode.op.as_str()]
    }
}

fn assert_roots(
    egraph: &EGraph<SymbolLang, ()>,
    expression: &RecExpr<SymbolLang>,
    result_roots: &[Id],
    roots: &[Id],
) {
    assert!(expression.is_dag());
    assert_eq!(result_roots.len(), roots.len());
    let classes = egraph.lookup_expr_ids(expression).unwrap();
    for (&result, &root) in result_roots.iter().zip(roots) {
        assert_eq!(classes[usize::from(result)], egraph.find(root));
    }
}

#[test]
fn issue_207_cyclic_egraph_remains_feasible() {
    // The original issue's rewrite equates f(v, g(v, x)) with x. The selected
    // expression must use x's leaf so that the mandatory g does not form a cycle.
    let mut egraph = EGraph::<SymbolLang, ()>::default();
    let g = egraph.add_expr(&"(g v x)".parse().unwrap());
    let v = egraph.add_expr(&"v".parse().unwrap());
    let f = egraph.add(SymbolLang::new("f", vec![v, g]));
    let top = egraph.add(SymbolLang::new("list", vec![f, g]));
    egraph.rebuild();

    let runner = Runner::default()
        .with_egraph(egraph)
        .run(&[rewrite!("f"; "(f ?v (g ?v ?a))" => "?a")]);
    let (expression, roots) = LpExtractor::new(&runner.egraph, AstSize).solve_multiple(&[top]);
    assert_eq!(expression.to_string(), "(list x (g v x))");
    assert_eq!(expression.len(), 4);
    assert_roots(&runner.egraph, &expression, &roots, &[top]);
}

fn cost_counterexample() -> (EGraph<SymbolLang, ()>, Id, Id, Id, OpCosts) {
    // https://github.com/egraphs-good/egg/issues/207#issuecomment-1268764758
    let mut egraph = EGraph::<SymbolLang, ()>::default();
    let a = egraph.add_expr(&"(A y)".parse().unwrap());
    let x = egraph.add_expr(&"x".parse().unwrap());
    let y = egraph.add_expr(&"y".parse().unwrap());
    let top = egraph.add(SymbolLang::new("list", vec![a, y]));
    egraph.union(a, x);
    egraph.rebuild();
    let costs = OpCosts(BTreeMap::from([
        ("A".into(), 1.0),
        ("B".into(), 2.0),
        ("x".into(), 10.0),
        ("y".into(), 3.0),
        ("list".into(), 0.0),
    ]));
    (egraph, x, y, top, costs)
}

#[test]
fn adding_an_scc_edge_preserves_the_optimal_dag() {
    let (mut egraph, _x, y, top, costs) = cost_counterexample();
    let before = LpExtractor::new(&egraph, costs.clone()).solve(top);
    assert_eq!(before.to_string(), "(list (A y) y)");
    assert_eq!(before.len(), 3); // y is shared rather than charged twice.

    let b = egraph.add_expr(&"(B x)".parse().unwrap());
    egraph.union(b, y);
    egraph.rebuild();
    let after = LpExtractor::new(&egraph, costs).solve(top);
    assert_eq!(after.to_string(), "(list (A y) y)");
    assert_eq!(after.len(), 3);
    assert_eq!(egraph.lookup_expr(&after), Some(egraph.find(top)));
}

#[test]
fn repeated_solves_support_multiple_ancestor_and_duplicate_roots() {
    let (mut egraph, x, y, _top, costs) = cost_counterexample();
    let b = egraph.add_expr(&"(B x)".parse().unwrap());
    egraph.union(b, y);
    egraph.rebuild();
    let mut extractor = LpExtractor::new(&egraph, costs);

    let x_expression = extractor.solve_with(x, good_lp::coin_cbc);
    assert_eq!(x_expression.to_string(), "(A y)");
    assert_eq!(extractor.solve(y).to_string(), "y");

    // Process the descendant before its ancestor, then the reverse order, and
    // preserve duplicate root positions. All three calls reuse one extractor.
    for roots in [vec![y, x], vec![x, y], vec![y, x, y, x]] {
        let (expression, result_roots) = extractor.solve_multiple_with(&roots, good_lp::coin_cbc);
        assert_eq!(expression.len(), 2);
        assert_roots(&egraph, &expression, &result_roots, &roots);
        if roots.len() == 4 {
            assert_eq!(result_roots[0], result_roots[2]);
            assert_eq!(result_roots[1], result_roots[3]);
        }
    }

    let (expression, roots) = extractor.solve_multiple(&[]);
    assert!(expression.is_empty());
    assert!(roots.is_empty());
    assert_eq!(extractor.solve(x).to_string(), "(A y)");
}

#[test]
fn self_loop_uses_its_finite_exit_and_timeout_apis() {
    let mut egraph = EGraph::<SymbolLang, ()>::default();
    let a = egraph.add(SymbolLang::leaf("a"));
    let loop_node = egraph.add(SymbolLang::new("loop", vec![a]));
    egraph.union(a, loop_node);
    egraph.rebuild();
    let costs = OpCosts(BTreeMap::from([
        ("a".into(), 1.0),
        ("unused".into(), 0.0),
        ("loop".into(), 0.0),
    ]));
    // With n = 1, the leaf is feasible and the selected self-loop is not.
    assert_eq!(egraph.number_of_classes(), 1);
    assert_eq!(
        LpExtractor::new(&egraph, costs.clone())
            .solve(a)
            .to_string(),
        "a"
    );
    // Also cover a root-free zero-cost self-loop class.
    let unused = egraph.add(SymbolLang::leaf("unused"));
    let unused_loop = egraph.add(SymbolLang::new("loop", vec![unused]));
    egraph.union(unused, unused_loop);
    egraph.rebuild();
    let mut extractor = LpExtractor::new(&egraph, costs);
    assert_eq!(extractor.solve(a).to_string(), "a");
    assert_eq!(
        extractor
            .solve_with_timeout(a, good_lp::coin_cbc, 10.0)
            .to_string(),
        "a"
    );
    let requested = [a, a];
    let (expression, roots) =
        extractor.solve_multiple_with_timeout(&requested, good_lp::coin_cbc, 10.0);
    assert_eq!(expression.len(), 1);
    assert_roots(&egraph, &expression, &roots, &requested);
}

#[test]
fn shared_and_duplicate_children_are_charged_once() {
    let mut egraph = EGraph::<SymbolLang, ()>::default();
    let a = egraph.add(SymbolLang::leaf("a"));
    let f = egraph.add(SymbolLang::new("f", vec![a, a, a]));
    let g = egraph.add(SymbolLang::new("g", vec![f, a]));
    egraph.rebuild();
    let (expression, roots) = LpExtractor::new(&egraph, AstSize).solve_multiple(&[g, f, a]);
    assert_eq!(expression.len(), 3);
    assert_roots(&egraph, &expression, &roots, &[g, f, a]);
    let f_node = &expression[roots[1]];
    assert_eq!(f_node.children(), &[roots[2], roots[2], roots[2]]);
}

#[test]
fn a_long_dag_can_use_all_classes() {
    // A complete acyclicity bound must admit a chain through every class.
    let mut egraph = EGraph::<SymbolLang, ()>::default();
    let mut root = egraph.add(SymbolLang::leaf("a"));
    for _ in 1..32 {
        root = egraph.add(SymbolLang::new("f", vec![root]));
    }
    egraph.rebuild();
    let expression = LpExtractor::new(&egraph, AstSize).solve(root);
    assert_eq!(expression.len(), 32);
    assert_eq!(egraph.lookup_expr(&expression), Some(egraph.find(root)));
}

#[test]
fn an_unselected_back_edge_does_not_restrict_a_valid_dag() {
    // Selecting both forward edges needs the full rank span n - 1. The unused
    // back edge must impose no restriction, even between those extreme ranks.
    let mut egraph = EGraph::<SymbolLang, ()>::default();
    let a = egraph.add(SymbolLang::leaf("a"));
    let b = egraph.add(SymbolLang::leaf("b"));
    let c = egraph.add(SymbolLang::leaf("c"));
    let forward_a = egraph.add(SymbolLang::new("forward_a", vec![b]));
    let forward_b = egraph.add(SymbolLang::new("forward_b", vec![c]));
    let back = egraph.add(SymbolLang::new("back", vec![a]));
    egraph.union(a, forward_a);
    egraph.union(b, forward_b);
    egraph.union(c, back);
    egraph.rebuild();
    let costs = OpCosts(BTreeMap::from([
        ("a".into(), 10.0),
        ("b".into(), 10.0),
        ("c".into(), 1.0),
        ("forward_a".into(), 0.0),
        ("forward_b".into(), 0.0),
        ("back".into(), 0.0),
    ]));
    let expression = LpExtractor::new(&egraph, costs).solve(a);
    assert_eq!(expression.to_string(), "(forward_a (forward_b c))");
    assert_eq!(expression.len(), 3);
}

#[test]
fn an_empty_egraph_has_an_empty_rootless_extraction() {
    let egraph = EGraph::<SymbolLang, ()>::default();
    let (expression, roots) = LpExtractor::new(&egraph, AstSize).solve_multiple(&[]);
    assert!(expression.is_empty());
    assert!(roots.is_empty());
}

#[derive(Debug)]
struct TestNode {
    op: String,
    cost: u32,
    children: Vec<usize>,
}

fn graph_nodes(mut code: usize) -> Vec<Vec<TestNode>> {
    let profile = code % 3;
    (0..3)
        .map(|class| {
            let shape = code % 7;
            code /= 7;
            let next = (class + 1) % 3;
            let prev = (class + 2) % 3;
            let children = match shape {
                0 => None,
                1 => Some(vec![next]),
                2 => Some(vec![prev]),
                3 => Some(vec![class]),
                4 => Some(vec![next, prev]),
                5 => Some(vec![next, next]),
                6 => Some(vec![class, next]),
                _ => unreachable!(),
            };
            let mut nodes = vec![TestNode {
                op: format!("leaf{class}"),
                cost: if profile == 2 { 0 } else { 2 + class as u32 },
                children: Vec::new(),
            }];
            if let Some(children) = children {
                nodes.push(TestNode {
                    op: format!("alt{class}"),
                    cost: if profile == 0 { 1 + class as u32 } else { 0 },
                    children,
                });
            }
            nodes
        })
        .collect()
}

fn build_graph(nodes: &[Vec<TestNode>]) -> (EGraph<SymbolLang, ()>, Vec<Id>, OpCosts) {
    let mut egraph = EGraph::<SymbolLang, ()>::default();
    let classes: Vec<_> = nodes
        .iter()
        .map(|choices| egraph.add(SymbolLang::leaf(&choices[0].op)))
        .collect();
    let mut costs = BTreeMap::new();
    for (class, choices) in nodes.iter().enumerate() {
        for node in choices {
            costs.insert(node.op.clone(), f64::from(node.cost));
            if !node.children.is_empty() {
                let children = node.children.iter().map(|&i| classes[i]).collect();
                let alternative = egraph.add(SymbolLang::new(&node.op, children));
                egraph.union(classes[class], alternative);
            }
        }
    }
    egraph.rebuild();
    assert_eq!(egraph.number_of_classes(), nodes.len());
    (egraph, classes, OpCosts(costs))
}

fn acyclic_selection(nodes: &[Vec<TestNode>], choices: &[Option<usize>]) -> bool {
    // Independent DFS over selected edges, without using any LP rank variables.
    fn visit(
        class: usize,
        nodes: &[Vec<TestNode>],
        choices: &[Option<usize>],
        colors: &mut [u8],
    ) -> bool {
        match colors[class] {
            1 => return false,
            2 => return true,
            _ => (),
        }
        let Some(choice) = choices[class] else {
            return false;
        };
        colors[class] = 1;
        for &child in &nodes[class][choice].children {
            if !visit(child, nodes, choices, colors) {
                return false;
            }
        }
        colors[class] = 2;
        true
    }

    let mut colors = vec![0; nodes.len()];
    choices
        .iter()
        .enumerate()
        .all(|(class, choice)| choice.is_none() || visit(class, nodes, choices, &mut colors))
}

fn exhaustive_optimum(nodes: &[Vec<TestNode>], roots: &[usize]) -> u32 {
    // Enumerate inactive or exactly one e-node for every class. The oracle's
    // objective counts each active class once, including shared/duplicate edges.
    // Nonnegative costs ensure removing root-free active classes cannot worsen
    // an optimum, even when zero-cost choices produce several optima.
    fn enumerate(
        class: usize,
        nodes: &[Vec<TestNode>],
        roots: &[usize],
        choices: &mut [Option<usize>],
        best: &mut u32,
    ) {
        if class == nodes.len() {
            if roots.iter().any(|&root| choices[root].is_none())
                || !acyclic_selection(nodes, choices)
            {
                return;
            }
            let cost = choices
                .iter()
                .enumerate()
                .filter_map(|(class, choice)| choice.map(|i| nodes[class][i].cost))
                .sum();
            *best = (*best).min(cost);
            return;
        }
        choices[class] = None;
        enumerate(class + 1, nodes, roots, choices, best);
        for choice in 0..nodes[class].len() {
            choices[class] = Some(choice);
            enumerate(class + 1, nodes, roots, choices, best);
        }
    }

    let mut best = u32::MAX;
    enumerate(0, nodes, roots, &mut vec![None; nodes.len()], &mut best);
    assert_ne!(best, u32::MAX); // Each generated class has a finite leaf exit.
    best
}

fn validate_selection(
    nodes: &[Vec<TestNode>],
    expression: &RecExpr<SymbolLang>,
    result_roots: &[Id],
    roots: &[usize],
) -> u32 {
    assert!(expression.is_dag());
    let mut classes = Vec::new();
    let mut seen = BTreeSet::new();
    let mut cost = 0;
    for (index, enode) in expression.as_ref().iter().enumerate() {
        let (class, node) = nodes
            .iter()
            .enumerate()
            .find_map(|(class, choices)| {
                choices
                    .iter()
                    .find(|node| node.op == enode.op.as_str())
                    .map(|node| (class, node))
            })
            .unwrap();
        assert!(seen.insert(class), "two selected e-nodes in class {class}");
        assert_eq!(enode.children.len(), node.children.len());
        for (&child, &expected) in enode.children.iter().zip(&node.children) {
            assert!(usize::from(child) < index);
            assert_eq!(classes[usize::from(child)], expected);
        }
        classes.push(class);
        cost += node.cost;
    }
    assert_eq!(result_roots.len(), roots.len());
    for (&result, &root) in result_roots.iter().zip(roots) {
        assert_eq!(classes[usize::from(result)], root);
    }
    // Every emitted node must be reachable from at least one requested root.
    let mut reached = BTreeSet::new();
    let mut todo = result_roots.to_vec();
    while let Some(id) = todo.pop() {
        if reached.insert(id) {
            todo.extend_from_slice(expression[id].children());
        }
    }
    assert_eq!(reached.len(), expression.len());
    cost
}

#[test]
fn differential_exhaustive_small_egraphs() {
    // All 7^3 combinations of absent/unary/self/binary/duplicate alternatives.
    // Across the suite, two root sets per graph cover all eight subsets, with
    // positive, mixed-zero, and all-zero finite costs (one profile per shape).
    // This performs 686 solver/oracle comparisons.
    for code in 0..7usize.pow(3) {
        let nodes = graph_nodes(code);
        let (egraph, classes, costs) = build_graph(&nodes);
        let mut extractor = LpExtractor::new(&egraph, costs);
        for mask in [code % 8, (code + 3) % 8] {
            let roots: Vec<_> = (0..nodes.len()).filter(|&i| mask & (1 << i) != 0).collect();
            let expected = exhaustive_optimum(&nodes, &roots);
            let root_classes: Vec<_> = roots.iter().map(|&i| classes[i]).collect();
            let (expression, result_roots) = extractor.solve_multiple(&root_classes);
            assert_roots(&egraph, &expression, &result_roots, &root_classes);
            let actual = validate_selection(&nodes, &expression, &result_roots, &roots);
            assert_eq!(
                actual, expected,
                "graph {code}, root mask {mask}, choices {nodes:?}, expression {expression}"
            );
        }
    }
}

#[test]
fn zero_cost_cycles_still_require_finite_representatives() {
    // All three forward alternatives form a cycle. Exercise every root subset
    // with zero-cost alternatives, then with all node costs zero (16 comparisons).
    for all_zero in [false, true] {
        let mut nodes = graph_nodes(57);
        for choices in &mut nodes {
            for node in choices {
                if all_zero || !node.children.is_empty() {
                    node.cost = 0;
                }
            }
        }
        let (egraph, classes, costs) = build_graph(&nodes);
        let mut extractor = LpExtractor::new(&egraph, costs);
        for mask in 0..8 {
            let roots: Vec<_> = (0..3).filter(|&i| mask & (1 << i) != 0).collect();
            let root_classes: Vec<_> = roots.iter().map(|&i| classes[i]).collect();
            let (expression, result_roots) = extractor.solve_multiple(&root_classes);
            assert_roots(&egraph, &expression, &result_roots, &root_classes);
            assert_eq!(
                validate_selection(&nodes, &expression, &result_roots, &roots),
                exhaustive_optimum(&nodes, &roots),
                "all_zero={all_zero}, root mask {mask}"
            );
        }
    }
}
