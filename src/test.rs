/*! Utilities for benchmarking egg.

These are not considered part of the public api.
*/

use std::path::PathBuf;
use std::time::{Duration, Instant};

fn mean_stdev(data: &[f64]) -> (f64, f64) {
    assert_ne!(data.len(), 0);

    let sum = data.iter().sum::<f64>();
    let n = data.len() as f64;
    let mean = sum / n;

    let variance = data
        .iter()
        .map(|value| {
            let diff = mean - (*value as f64);
            diff * diff
        })
        .sum::<f64>()
        / n;

    (mean, variance.sqrt())
}

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

pub struct Reporter<T> {
    name: String,
    times: Option<Vec<f64>>,
    result: T,
}

impl<T> Reporter<T> {
    pub fn into_inner(self) -> T {
        // consume these so rust doesn't complain
        let _ = self.name;
        let _ = self.times;
        self.result
    }

    #[cfg(not(feature = "reports"))]
    pub fn report<R>(self, to_report: impl FnOnce(&T) -> &R) -> T {
        if let Some(dir) = env_var::<PathBuf>("EGG_BENCH_DIR") {
            eprintln!(
                "EGG_BENCH_DIR is set to '{:?}', but the 'reports' feature is not enabled",
                dir
            );
        }
        to_report(&self.result);
        self.result
    }

    #[cfg(feature = "reports")]
    pub fn report<R>(self, to_report: impl FnOnce(&T) -> &R) -> T
    where
        R: serde::Serialize,
    {
        let directory = match env_var::<PathBuf>("EGG_BENCH_DIR") {
            None => {
                eprintln!("EGG_BENCH_DIR not set, skipping reporting");
                return self.result;
            }
            Some(dir) => {
                assert!(dir.is_dir(), "EGG_BENCH_DIR is not a directory: {:?}", dir);
                dir
            }
        };

        let filename = format!("{}.json", self.name);
        let path = directory.join(&filename);
        let file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .unwrap_or_else(|err| panic!("Failed to open {:?}: {}", path, err));

        let report = serde_json::json!({
            "name": &self.name,
            "times": self.times.as_deref(),
            "data": to_report(&self.result),
        });

        serde_json::to_writer_pretty(file, &report)
            .unwrap_or_else(|err| panic!("Failed to serialize report to {:?}: {}", path, err));

        println!("Wrote report to {:?}", path);
        self.result
    }
}

pub fn run<T>(name: impl Into<String>, mut f: impl FnMut() -> T) -> Reporter<T> {
    let name = name.into();
    let seconds: f64 = match env_var("EGG_BENCH") {
        Some(s) => s,
        None => {
            return Reporter {
                name,
                times: None,
                result: f(),
            }
        }
    };

    let duration = Duration::from_secs_f64(seconds);

    let start = Instant::now();
    let mut times = vec![];

    println!("benching {} for {} seconds...", name, seconds);

    let result = loop {
        let i = Instant::now();
        let result = f();
        times.push(i.elapsed().as_secs_f64());

        if start.elapsed() > duration {
            break result;
        }
    };

    let (mean, stdev) = mean_stdev(&times);
    println!("bench    {}:", name);
    println!("  n = {}", times.len());
    println!("  μ = {}", mean);
    println!("  σ = {}", stdev);

    Reporter {
        name,
        times: Some(times),
        result,
    }
}

/// Make a test function
#[macro_export]
macro_rules! test_fn {
    (
        $(#[$meta:meta])*
        $name:ident, $rules:expr,
        $start:literal
        =>
        $($goal:literal),+ $(,)?
        $(@check $check_fn:expr)?
    ) => {
        $crate::test_fn! {
            $(#[$meta])*
            $name, $rules,
            runner = $crate::Runner::<_, _, ()>::default(),
            $start => $( $goal ),+
            $(@check $check_fn)?
        }
    };

    (
        $(#[$meta:meta])*
        $name:ident, $rules:expr,
        runner = $runner:expr,
        $start:literal
        =>
        $($goal:literal),+ $(,)?
        $(@check $check_fn:expr)?
    ) => {
        $(#[$meta])*
        #[test]
        fn $name() {
            let _ = env_logger::builder().is_test(true).try_init();
            let name = stringify!($name);
            let start: $crate::RecExpr<_> = $start.parse().unwrap();
            let rules = $rules;

            let runner: $crate::Runner<_, _, ()> = $crate::test::run(name, || {
                let mut runner = $runner.with_expr(&start);
                if let Some(lim) = $crate::test::env_var("EGG_NODE_LIMIT") {
                    runner = runner.with_node_limit(lim)
                }
                if let Some(lim) = $crate::test::env_var("EGG_ITER_LIMIT") {
                    runner = runner.with_iter_limit(lim)
                }
                if let Some(lim) = $crate::test::env_var("EGG_TIME_LIMIT") {
                    runner = runner.with_time_limit(std::time::Duration::from_secs(lim))
                }
                runner.run(&rules)
            }).report(|r| &r.iterations);
            runner.print_report();

            let goals = &[$(
                $goal.parse().unwrap()
            ),+];

            // NOTE this is a bit of hack, we rely on the fact that the
            // initial root is the last expr added by the runner. We can't
            // use egraph.find_expr(start) because it may have been pruned
            // away
            let id = runner.egraph.find(*runner.roots.last().unwrap());
            runner.egraph.check_goals(id, goals);

            $( ($check_fn)(runner) )?
        }
    };
}
