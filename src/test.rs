/*! Utilities for testing / benchmarking egg.

These are not considered part of the public api.
*/

use std::fmt::Display;

use crate::*;

pub fn env_var<T>(s: &str) -> Option<T>
where
    T: std::str::FromStr,
    T::Err: std::fmt::Debug,
{
    use std::env::VarError;
    match std::env::var(s) {
        Err(VarError::NotPresent) => None,
        Err(VarError::NotUnicode(_)) => panic!("Environment variable {} isn't unicode", s),
        Ok(v) if v.is_empty() => None,
        Ok(v) => match v.parse() {
            Ok(v) => Some(v),
            Err(err) => panic!("Couldn't parse environment variable {}={}, {:?}", s, v, err),
        },
    }
}

#[allow(clippy::type_complexity)]
pub fn test_runner<L, A>(
    _name: &str,
    runner: Option<Runner<L, A, ()>>,
    rules: &[Rewrite<L, A>],
    start: RecExpr<L>,
    goals: &[Pattern<L>],
    check_fn: Option<fn(Runner<L, A, ()>)>,
    should_check: bool,
) where
    L: Language + Display + 'static,
    A: Analysis<L> + Default,
{
    let mut runner = runner.unwrap_or_default();

    if let Some(lim) = env_var("EGG_NODE_LIMIT") {
        runner = runner.with_node_limit(lim)
    }
    if let Some(lim) = env_var("EGG_ITER_LIMIT") {
        runner = runner.with_iter_limit(lim)
    }
    if let Some(lim) = env_var("EGG_TIME_LIMIT") {
        runner = runner.with_time_limit(std::time::Duration::from_secs(lim))
    }

    if cfg!(feature = "test-explanations") {
        runner = runner.with_explanations_enabled();
    } else {
        runner = runner.with_explanations_disabled();
    }

    runner = runner.with_expr(&start);
    // NOTE this is a bit of hack, we rely on the fact that the
    // initial root is the last expr added by the runner. We can't
    // use egraph.find_expr(start) because it may have been pruned
    // away
    let id = runner.egraph.find(*runner.roots.last().unwrap());

    if check_fn.is_none() {
        let goals = goals.to_vec();
        runner = runner.with_hook(move |r| {
            if goals
                .iter()
                .all(|g: &Pattern<_>| g.search_eclass(&r.egraph, id).is_some())
            {
                Err("Done".into())
            } else {
                Ok(())
            }
        });
    }
    let mut runner = runner.run(rules);

    if should_check {
        runner.print_report();
        runner.egraph.check_goals(id, goals);

        if runner.egraph.are_explanations_enabled() {
            for goal in goals {
                let matches = goal.search_eclass(&runner.egraph, id).unwrap();
                let subst = matches.substs[0].clone();
                let mut explained = runner.explain_matches(&start, &goal.ast, &subst);
                println!("{}", explained);
                explained.get_sexp_with_let();
                explained.get_flat_sexps();
                explained.check_proof(rules);

                let mut existance = runner.explain_existance_pattern(&goal.ast, &subst);
                existance.get_sexp_with_let();
                existance.get_flat_sexps();
                existance.check_proof(rules);
            }
        }

        if let Some(check_fn) = check_fn {
            check_fn(runner)
        }
    }
}

fn percentile(k: f64, data: &[u128]) -> u128 {
    // assumes data is sorted
    assert!((0.0..=1.0).contains(&k));
    let i = (data.len() as f64 * k) as usize;
    let i = i.min(data.len() - 1);
    data[i]
}

pub fn bench_egraph<L, N>(
    _name: &str,
    rules: Vec<Rewrite<L, N>>,
    exprs: &[&str],
    extra_patterns: &[&str],
) -> EGraph<L, N>
where
    L: Language + FromOp + 'static + Display,
    N: Analysis<L> + Default + 'static,
{
    let mut patterns: Vec<Pattern<L>> = vec![];
    for rule in &rules {
        if let Some(ast) = rule.searcher.get_pattern_ast() {
            patterns.push(ast.alpha_rename().into())
        }
        if let Some(ast) = rule.applier.get_pattern_ast() {
            patterns.push(ast.alpha_rename().into())
        }
    }
    for extra in extra_patterns {
        let p: Pattern<L> = extra.parse().unwrap();
        patterns.push(p.ast.alpha_rename().into());
    }

    eprintln!("{} patterns", patterns.len());

    patterns.retain(|p| p.ast.as_ref().len() > 1);
    patterns.sort_by_key(|p| p.to_string());
    patterns.dedup();
    patterns.sort_by_key(|p| p.ast.as_ref().len());

    let iter_limit = env_var("EGG_ITER_LIMIT").unwrap_or(1);
    let node_limit = env_var("EGG_NODE_LIMIT").unwrap_or(1_000_000);
    let time_limit = env_var("EGG_TIME_LIMIT").unwrap_or(1000);
    let n_samples = env_var("EGG_SAMPLES").unwrap_or(100);
    eprintln!("Benching {} samples", n_samples);
    eprintln!(
        "Limits: {} iters, {} nodes, {} seconds",
        iter_limit, node_limit, time_limit
    );

    let mut runner = Runner::default()
        .with_scheduler(SimpleScheduler)
        .with_hook(move |runner| {
            let n_nodes = runner.egraph.total_number_of_nodes();
            eprintln!("Iter {}, {} nodes", runner.iterations.len(), n_nodes);
            if n_nodes > node_limit {
                Err("Bench stopped".into())
            } else {
                Ok(())
            }
        })
        .with_iter_limit(iter_limit)
        .with_node_limit(node_limit)
        .with_time_limit(Duration::from_secs(time_limit));

    for expr in exprs {
        runner = runner.with_expr(&expr.parse().unwrap());
    }

    let runner = runner.run(&rules);
    eprintln!("{}", runner.report());
    let egraph = runner.egraph;

    let get_len = |pat: &Pattern<L>| pat.to_string().len();
    let max_width = patterns.iter().map(get_len).max().unwrap_or(0);
    for pat in &patterns {
        let mut times: Vec<u128> = (0..n_samples)
            .map(|_| {
                let start = Instant::now();
                let matches = pat.search(&egraph);
                let time = start.elapsed();
                let _n_results = matches.iter().map(|m| m.substs.len()).sum::<usize>();
                time.as_nanos()
            })
            .collect();
        times.sort_unstable();

        println!(
            "test {name:<width$} ... bench: {time:>10} ns/iter (+/- {iqr})",
            name = pat.to_string().replace(' ', "_"),
            width = max_width,
            time = percentile(0.05, &times),
            iqr = percentile(0.75, &times) - percentile(0.25, &times),
        );
    }

    egraph
}

/// Make a test function
#[macro_export]
macro_rules! test_fn {
    (
        $(#[$meta:meta])*
        $name:ident, $rules:expr,
        $(runner = $runner:expr,)?
        $start:literal
        =>
        $($goal:literal),+ $(,)?
        $(@check $check_fn:expr)?
    ) => {
        mod $name {
            use super::*;
            pub fn run(check: bool) {
                let _ = env_logger::builder().is_test(true).try_init();

                $crate::test::test_runner(
                    stringify!($name),
                    None $(.or(Some($runner)))?,
                    &$rules,
                    $start.parse().unwrap(),
                    &[$( $goal.parse().unwrap() ),+],
                    None $(.or(Some($check_fn)))?,
                    check,
                )
            }

            $(#[$meta])* #[test] fn test() { run(true) }
        }

        pub fn $name() { $name::run(false) }
    };
}
