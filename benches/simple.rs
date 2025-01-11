use egg::*;
use rayon::prelude::*;

mod definitions;
use definitions::simple;

mod schedulers;
use schedulers::schedulers::*;

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};


fn serial_simplify(s: &str) -> String {
    let expr: RecExpr<simple::SimpleLanguage> = s.parse().unwrap();
    let runner = Runner::default()
        .with_scheduler(SerialRewriteScheduler)
        .with_expr(&expr)
        .run(&simple::make_rules());
    let root = runner.roots[0];
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_best_cost, best) = extractor.find_best(root);
    best.to_string()
}

fn parallel_simplify(s: &str) -> String {
    let expr: RecExpr<simple::SimpleLanguage> = s.parse().unwrap();
    let runner = Runner::default()
        .with_scheduler(ParallelRewriteScheduler)
        .with_expr(&expr)
        .run(&simple::make_rules());
    let root = runner.roots[0];
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_best_cost, best) = extractor.find_best(root);
    best.to_string()
}

fn restricted_parallel_simplify(s: &str) -> String {
    let expr: RecExpr<simple::SimpleLanguage> = s.parse().unwrap();
    let runner = Runner::default()
        .with_scheduler(RestrictedParallelRewriteScheduler)
        .with_expr(&expr)
        .run(&simple::make_rules());
    let root = runner.roots[0];
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_best_cost, best) = extractor.find_best(root);
    best.to_string()
}


pub fn serial_simple_bench(c: &mut Criterion) {
    c.bench_function(
        "serial_simplify",
        |b| b.iter(
            || serial_simplify("(+ 0 (* 1 foo))")
        )
    );
}

pub fn parallel_simple_bench(c: &mut Criterion) {
    c.bench_function(
        "parallel_simplify",
        |b| b.iter(
            || parallel_simplify("(+ 0 (* 1 foo))")
        )
    );
}

pub fn restricted_parallel_simple_bench(c: &mut Criterion) {
    c.bench_function(
        "restricted_parallel_simplify",
        |b| b.iter(
            || restricted_parallel_simplify("(+ 0 (* 1 foo))")
        )
    );
}

pub fn comparison_simple_bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("simplify");
    for i in simple::EXAMPLE_INPUTS.iter() {
        group.bench_with_input(BenchmarkId::new("serial_simplify", i), i,
            |b, i| b.iter(|| serial_simplify(*i)));
        group.bench_with_input(BenchmarkId::new("parallel_simplify", i), i,
            |b, i| b.iter(|| parallel_simplify(*i)));
        group.bench_with_input(BenchmarkId::new("restricted_parallel_simplify", i), i,
        |b, i| b.iter(|| restricted_parallel_simplify(*i)));
    }
    group.finish();
}


// fn math_serial_simplify_root() {
//     egg::test::test_runner(
//         "math_simplify_root",
//         Some(Runner::default().with_node_limit(75_000)),
//         &math::rules(),
//         r#"
//         (/ 1
//            (- (/ (+ 1 (sqrt five))
//                  2)
//               (/ (- 1 (sqrt five))
//                  2)))"#.parse().unwrap(),
//         &["(/ 1 (sqrt five))".parse().unwrap()],
//         None,
//         true
//     )
// }

// pub fn math_bench(c: &mut Criterion) {
//     c.bench_function(
//         "math_simplify_root",
//         |b| b.iter(math_serial_simplify_root)
//     );
//     //c.bench_function(
//     //    "math_simplify_factor",
//     //    |b| b.iter(math_simplify_factor)
//     //);
// }


criterion_group!(benches, comparison_simple_bench);
criterion_main!(benches);
