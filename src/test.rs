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
    name: &str,
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
    if let Some(is_enabled) = env_var("EGG_TEST_EXPLANATIONS") {
        if is_enabled {
            runner = runner.with_explanations_enabled();
        } else {
            // in case we enabled it in order to add expressions
            runner = runner.with_explanations_disabled();
        }
    } else {
        // in case we enabled it in order to add expressions
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
        runner.egraph.check_goals(id, &goals);

        if runner.egraph.are_explanations_enabled() && name != "lambda_function_repeat" {
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
