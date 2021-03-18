/*! Utilities for testing / benchmarking egg.

These are not considered part of the public api.
*/

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

pub struct Test<L: Language, A: Analysis<L>> {
    name: String,
    runner: Option<fn() -> Runner<L, A, ()>>,
    rules: Vec<Rewrite<L, A>>,
    start: RecExpr<L>,
    goals: Vec<Pattern<L>>,
    check_fn: Option<fn(Runner<L, A, ()>)>,
    should_check: bool,
}

impl<L, A> Test<L, A>
where
    L: Language + 'static,
    A: Analysis<L> + Default,
{
    pub fn run(&self) {
        let mk_runner = self.runner.unwrap_or(Default::default);
        let mut runner = mk_runner().with_expr(&self.start);

        // NOTE this is a bit of hack, we rely on the fact that the
        // initial root is the last expr added by the runner. We can't
        // use egraph.find_expr(start) because it may have been pruned
        // away
        let id = runner.egraph.find(*runner.roots.last().unwrap());

        if let Some(lim) = env_var("EGG_NODE_LIMIT") {
            runner = runner.with_node_limit(lim)
        }
        if let Some(lim) = env_var("EGG_ITER_LIMIT") {
            runner = runner.with_iter_limit(lim)
        }
        if let Some(lim) = env_var("EGG_TIME_LIMIT") {
            runner = runner.with_time_limit(std::time::Duration::from_secs(lim))
        }

        println!("Running {}...", self.name);

        // if check_fn.is_none() {
        //     let goals = goals.to_vec();
        //     runner = runner.with_hook(move |r| {
        //         if goals
        //             .iter()
        //             .all(|g: &Pattern<_>| g.search_eclass(&r.egraph, id).is_some())
        //         {
        //             Err("Done".into())
        //         } else {
        //             Ok(())
        //         }
        //     });
        // }
        let runner = runner.run(&self.rules);

        if self.should_check {
            runner.print_report();
            runner.egraph.check_goals(id, &self.goals);

            if let Some(check_fn) = self.check_fn.as_ref() {
                check_fn(runner)
            }
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
            pub fn run(should_check: bool) {
                let _ = env_logger::builder().is_test(true).try_init();

                $crate::test::Test {
                    name: stringify!($name).into(),
                    runner: None $(.or(Some($runner)))?,
                    rules: $rules,
                    start: $start.parse().unwrap(),
                    goals: vec![$( $goal.parse().unwrap() ),+],
                    check_fn: None $(.or(Some($check_fn)))?,
                    should_check,
                }.run();
            }

            $(#[$meta])* #[test] fn test() { run(true) }
        }

        pub fn $name() { $name::run(false) }
    };
}
