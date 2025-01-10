use egg::*;
use rayon::prelude::*;

mod definitions;
use definitions::simple;

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};

pub struct SerialRewriteScheduler;
impl<L: Language, N: Analysis<L>> RewriteScheduler<L, N> for SerialRewriteScheduler {
    fn search_rewrites<'a>(
        &mut self,
        iteration: usize,
        egraph: &EGraph<L, N>,
        rewrites: &[&'a Rewrite<L, N>],
        limits: &RunnerLimits,
    ) -> RunnerResult<Vec<Vec<SearchMatches<'a, L>>>> {
        rewrites
            .iter()
            .map(|rw| {
                let ms = rw.search(egraph);
                limits.check_limits(iteration, egraph)?;
                Ok(ms)
            })
            .collect()
    }
}

pub struct ParallelRewriteScheduler;
impl<L, N> RewriteScheduler<L, N> for ParallelRewriteScheduler
    where
    L: Language + Sync + Send,
    L::Discriminant: Sync + Send,
    N: Analysis<L> + Sync + Send,
    N::Data: Sync + Send
{
// impl<L: Language + Send + Sync> RewriteScheduler<L, ()> for ParallelRewriteScheduler {
    fn search_rewrites<'a>(
        &mut self,
        iteration: usize,
        egraph: &EGraph<L, N>,
        rewrites: &[&'a Rewrite<L, N>],
        limits: &RunnerLimits,
    ) -> RunnerResult<Vec<Vec<SearchMatches<'a, L>>>> {
        // This implementation just ignores the limits
        // fake `par_map` to enforce Send + Sync, in real life use rayon
        // fn par_map<T, F, T2>(slice: &[T], f: F) -> Vec<T2>
        // where
        //     T: Send + Sync,
        //     F: Fn(&T) -> T2 + Send + Sync,
        //     T2: Send + Sync,
        // {
        //     slice.iter().map(f).collect()
        // }
        // Ok(par_map(rewrites, |rw| rw.search(egraph)))

        rewrites
            .par_iter()
            .map(|rw| {
                let ms = rw.search(egraph);
                limits.check_limits(iteration, egraph)?;
                Ok(ms)
            })
            .collect() // ::<RunnerResult<Vec<Vec<SearchMatches<'a, L>>>>>()

        // TODO: Note that `Sync + Send` traits were added to both language and
        //       discriminant. Could this impact correctness?
    }
}


pub struct RestrictedParallelRewriteScheduler;
impl<L> RewriteScheduler<L, ()> for RestrictedParallelRewriteScheduler
    where
    L: Language + Sync + Send,
    L::Discriminant: Sync + Send,
{
// impl<L: Language + Send + Sync> RewriteScheduler<L, ()> for ParallelRewriteScheduler {
    fn search_rewrites<'a>(
        &mut self,
        iteration: usize,
        egraph: &EGraph<L, ()>,
        rewrites: &[&'a Rewrite<L, ()>],
        limits: &RunnerLimits,
    ) -> RunnerResult<Vec<Vec<SearchMatches<'a, L>>>> {
        rewrites
            .par_iter()
            .map(|rw| {
                let ms = rw.search(egraph);
                limits.check_limits(iteration, egraph)?;
                Ok(ms)
            })
            .collect()
    }
}






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
