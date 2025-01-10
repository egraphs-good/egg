use egg::{rewrite as rw, *};

mod definitions;
use definitions::math;

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};

// fn math_() {
//     egg::test::test_runner(
//         "",
//         None,
//         &math::rules(),
//         "".parse().unwrap(),
//         &["".parse().unwrap()],
//         None,
//         true
//     )
// }

fn math_associate_adds() {
    egg::test::test_runner(
        "math_associate_adds",
        Some(Runner::default()
            .with_iter_limit(7)
            .with_scheduler(SimpleScheduler)),
        &[
            rw!("comm-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
            rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        ],
        "(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))".parse().unwrap(),
        &["(+ 7 (+ 6 (+ 5 (+ 4 (+ 3 (+ 2 1))))))".parse().unwrap()],
        Some(|r: Runner<math::Math, ()>| assert_eq!(r.egraph.number_of_classes(), 127)),
        true
    )
}

// NOTE: Less suitable for benchmarking
// fn math_fail() {
//     let _ = std::panic::catch_unwind(
//         || egg::test::test_runner(
//             "math_fail",
//             None,
//             &math::rules(),
//             "(+ x y)".parse().unwrap(),
//             &["(/ x y)".parse().unwrap()],
//             None,
//             true
//         )
//     );
// }

fn math_simplify_add() {
    egg::test::test_runner(
        "math_simplify_add",
        None,
        &math::rules(),
        "(+ x (+ x (+ x x)))".parse().unwrap(),
        &["(* 4 x)".parse().unwrap()],
        None,
        true
    )
}

fn math_powers() {
    egg::test::test_runner(
        "math_powers",
        None,
        &math::rules(),
        "(* (pow 2 x) (pow 2 y))".parse().unwrap(),
        &["(pow 2 (+ x y))".parse().unwrap()],
        None,
        true
    )
}

fn math_simplify_const() {
    egg::test::test_runner(
        "math_simplify_const",
        None,
        &math::rules(),
        "(+ 1 (- a (* (- 2 1) a)))".parse().unwrap(),
        &["1".parse().unwrap()],
        None,
        true
    )
}

fn math_simplify_root() {
    egg::test::test_runner(
        "math_simplify_root",
        Some(Runner::default().with_node_limit(75_000)),
        &math::rules(),
        r#"
        (/ 1
        (- (/ (+ 1 (sqrt five))
                2)
            (/ (- 1 (sqrt five))
                2)))"#.parse().unwrap(),
        &["(/ 1 (sqrt five))".parse().unwrap()],
        None,
        true
    )
}

fn math_simplify_factor() {
    egg::test::test_runner(
        "math_simplify_factor",
        None,
        &math::rules(),
        "(* (+ x 3) (+ x 1))".parse().unwrap(),
        &["(+ (+ (* x x) (* 4 x)) 3)".parse().unwrap()],
        None,
        true
    )
}

fn math_diff_same() {
    egg::test::test_runner(
        "math_diff_same",
        None,
        &math::rules(),
        "(d x x)".parse().unwrap(),
        &["1".parse().unwrap()],
        None,
        true
    )
}

fn math_diff_different() {
    egg::test::test_runner(
        "math_diff_different",
        None,
        &math::rules(),
        "(d x y)".parse().unwrap(),
        &["0".parse().unwrap()],
        None,
        true
    )
}

fn math_diff_simple1() {
    egg::test::test_runner(
        "math_diff_simple1",
        None,
        &math::rules(),
        "(d x (+ 1 (* 2 x)))".parse().unwrap(),
        &["2".parse().unwrap()],
        None,
        true
    )
}

fn math_diff_simple2() {
    egg::test::test_runner(
        "math_diff_simple2",
        None,
        &math::rules(),
        "(d x (+ 1 (* y x)))".parse().unwrap(),
        &["y".parse().unwrap()],
        None,
        true
    )
}

fn math_diff_ln() {
    egg::test::test_runner(
        "math_diff_ln",
        None,
        &math::rules(),
        "(d x (ln x))".parse().unwrap(),
        &["(/ 1 x)".parse().unwrap()],
        None,
        true
    )
}

fn diff_power_simple() {
    egg::test::test_runner(
        "diff_power_simple",
        None,
        &math::rules(),
        "(d x (pow x 3))".parse().unwrap(),
        &["(* 3 (pow x 2))".parse().unwrap()],
        None,
        true
    )
}

fn diff_power_harder() {
    egg::test::test_runner(
        "diff_power_harder",
        Some(Runner::default()
                .with_time_limit(std::time::Duration::from_secs(10))
                .with_iter_limit(60)
                .with_node_limit(100_000)
                .with_explanations_enabled()
                // HACK this needs to "see" the end expression
                .with_expr(&"(* x (- (* 3 x) 14))".parse().unwrap())),
        &math::rules(),
        "(d x (- (pow x 3) (* 7 (pow x 2))))".parse().unwrap(),
        &["(* x (- (* 3 x) 14))".parse().unwrap()],
        None,
        true
    )
}

fn integ_one() {
    egg::test::test_runner(
        "integ_one",
        None,
        &math::rules(),
        "(i 1 x)".parse().unwrap(),
        &["x".parse().unwrap()],
        None,
        true
    )
}

fn integ_sin() {
    egg::test::test_runner(
        "integ_sin",
        None,
        &math::rules(),
        "(i (cos x) x)".parse().unwrap(),
        &["(sin x)".parse().unwrap()],
        None,
        true
    )
}

fn integ_x() {
    egg::test::test_runner(
        "integ_x",
        None,
        &math::rules(),
        "(i (pow x 1) x)".parse().unwrap(),
        &["(/ (pow x 2) 2)".parse().unwrap()],
        None,
        true
    )
}

fn integ_part1() {
    egg::test::test_runner(
        "integ_part1",
        None,
        &math::rules(),
        "(i (* x (cos x)) x)".parse().unwrap(),
        &["(+ (* x (sin x)) (cos x))".parse().unwrap()],
        None,
        true
    )
}

fn integ_part2() {
    egg::test::test_runner(
        "integ_part2",
        None,
        &math::rules(),
        "(i (* (cos x) x) x)".parse().unwrap(),
        &["(+ (* x (sin x)) (cos x))".parse().unwrap()],
        None,
        true
    )
}

fn integ_part3() {
    egg::test::test_runner(
        "integ_part3",
        None,
        &math::rules(),
        "(i (ln x) x)".parse().unwrap(),
        &["(- (* x (ln x)) x)".parse().unwrap()],
        None,
        true
    )
}

pub fn ematching_benches(c: &mut Criterion) {
    let exprs = &[
        "(i (ln x) x)",
        "(i (+ x (cos x)) x)",
        "(i (* (cos x) x) x)",
        "(d x (+ 1 (* 2 x)))",
        "(d x (- (pow x 3) (* 7 (pow x 2))))",
        "(+ (* y (+ x y)) (- (+ x 2) (+ x x)))",
        "(/ 1 (- (/ (+ 1 (sqrt five)) 2) (/ (- 1 (sqrt five)) 2)))",
    ];

    let extra_patterns = &[
        "(+ ?a (+ ?b ?c))",
        "(+ (+ ?a ?b) ?c)",
        "(* ?a (* ?b ?c))",
        "(* (* ?a ?b) ?c)",
        "(+ ?a (* -1 ?b))",
        "(* ?a (pow ?b -1))",
        "(* ?a (+ ?b ?c))",
        "(pow ?a (+ ?b ?c))",
        "(+ (* ?a ?b) (* ?a ?c))",
        "(* (pow ?a ?b) (pow ?a ?c))",
        "(* ?x (/ 1 ?x))",
        "(d ?x (+ ?a ?b))",
        "(+ (d ?x ?a) (d ?x ?b))",
        "(d ?x (* ?a ?b))",
        "(+ (* ?a (d ?x ?b)) (* ?b (d ?x ?a)))",
        "(d ?x (sin ?x))",
        "(d ?x (cos ?x))",
        "(* -1 (sin ?x))",
        "(* -1 (cos ?x))",
        "(i (cos ?x) ?x)",
        "(i (sin ?x) ?x)",
        "(d ?x (ln ?x))",
        "(d ?x (pow ?f ?g))",
        "(* (pow ?f ?g) (+ (* (d ?x ?f) (/ ?g ?f)) (* (d ?x ?g) (ln ?f))))",
        "(i (pow ?x ?c) ?x)",
        "(/ (pow ?x (+ ?c 1)) (+ ?c 1))",
        "(i (+ ?f ?g) ?x)",
        "(i (- ?f ?g) ?x)",
        "(+ (i ?f ?x) (i ?g ?x))",
        "(- (i ?f ?x) (i ?g ?x))",
        "(i (* ?a ?b) ?x)",
        "(- (* ?a (i ?b ?x)) (i (* (d ?x ?a) (i ?b ?x)) ?x))",
    ];

    c.bench_function(
        "ematching_benches",
        |b| b.iter(
            || egg::test::bench_egraph("math", math::rules(), exprs, extra_patterns)
        )
    );
}

pub fn math_tests(c: &mut Criterion) {
    let mut group = c.benchmark_group("math_tests");
    group.bench_function(
        "math_associate_adds",
        |b| b.iter(math_associate_adds)
    );
    // group.bench_function(
    //     "math_fail",
    //     |b| b.iter(math_fail)
    // );
    group.bench_function(
        "math_simplify_add",
        |b| b.iter(math_simplify_add)
    );
    group.bench_function(
        "math_powers",
        |b| b.iter(math_powers)
    );
    group.bench_function(
        "math_simplify_const",
        |b| b.iter(math_simplify_const)
    );
    group.bench_function(
        "math_simplify_root",
        |b| b.iter(math_simplify_root)
    );
    group.bench_function(
        "math_simplify_factor",
        |b| b.iter(math_simplify_factor)
    );
    group.bench_function(
        "math_diff_same",
        |b| b.iter(math_diff_same)
    );
    group.bench_function(
        "math_diff_different",
        |b| b.iter(math_diff_different)
    );
    group.bench_function(
        "math_diff_simple1",
        |b| b.iter(math_diff_simple1)
    );
    group.bench_function(
        "math_diff_simple2",
        |b| b.iter(math_diff_simple2)
    );
    group.bench_function(
        "math_diff_ln",
        |b| b.iter(math_diff_ln)
    );
    group.bench_function(
        "diff_power_simple",
        |b| b.iter(diff_power_simple)
    );
    group.bench_function(
        "diff_power_harder",
        |b| b.iter(diff_power_harder)
    );
    group.bench_function(
        "integ_one",
        |b| b.iter(integ_one)
    );
    group.bench_function(
        "integ_sin",
        |b| b.iter(integ_sin)
    );
    group.bench_function(
        "integ_x",
        |b| b.iter(integ_x)
    );
    group.bench_function(
        "integ_part1",
        |b| b.iter(integ_part1)
    );
    group.bench_function(
        "integ_part2",
        |b| b.iter(integ_part2)
    );
    group.bench_function(
        "integ_part3",
        |b| b.iter(integ_part3)
    );
    group.finish();
}

criterion_group!(benches, ematching_benches);
criterion_main!(benches);
