use indexmap::{IndexMap, IndexSet};
use instant::{Duration, Instant};
use log::*;

use crate::{Analysis, EGraph, Id, Language, RecExpr, Rewrite, SearchMatches};

/** Faciliates running rewrites over an [`EGraph`].

One use for [`EGraph`]s is as the basis of a rewriting system.
Since an egraph never "forgets" state when applying a [`Rewrite`], you
can apply many rewrites many times quite efficiently.
After the egraph is "full" (the rewrites can no longer find new
equalities) or some other condition, the egraph compactly represents
many, many equivalent expressions.
At this point, the egraph is ready for extraction (see [`Extractor`])
which can pick the represented expression that's best according to
some cost function.

This technique is called
[equality saturation](https://www.cs.cornell.edu/~ross/publications/eqsat/)
in general.
However, there can be many challenges in implementing this "outer
loop" of applying rewrites, mostly revolving around which rules to run
and when to stop.

[`Runner`] is `egg`'s provided equality saturation engine that has
reasonable defaults and implements many useful things like saturation
checking, egraph size limits, and customizable rule
[scheduling](trait.RewriteScheduler.html).
Consider using [`Runner`] before rolling your own outer loop.

Here are some of the things [`Runner`] does for you:

- Saturation checking

  [`Runner`] checks to see if any of the rules added anything
  new to the [`EGraph`]. If none did, then it stops, returning
  [`StopReason::Saturated`](enum.StopReason.html#variant.Saturated).

- Iteration limits

  You can set a upper limit of iterations to do in case the search
  doesn't stop for some other reason. If this limit is hit, it stops with
  [`StopReason::IterationLimit`](enum.StopReason.html#variant.IterationLimit).

- [`EGraph`] size limit

  You can set a upper limit on the number of enodes in the egraph.
  If this limit is hit, it stops with
  [`StopReason::NodeLimit`](enum.StopReason.html#variant.NodeLimit).

- Time limit

  You can set a time limit on the runner.
  If this limit is hit, it stops with
  [`StopReason::TimeLimit`](enum.StopReason.html#variant.TimeLimit).

- Rule scheduling

  Some rules enable themselves, blowing up the [`EGraph`] and
  preventing other rewrites from running as many times.
  To prevent this, you can provide your own [`RewriteScheduler`] to
  govern when to run which rules.

  [`BackoffScheduler`] is the default scheduler.

[`Runner`] generates [`Iteration`]s that record some data about
each iteration.
You can add your own data to this by implementing the
[`IterationData`] trait.
[`Runner`] is generic over the [`IterationData`] that it will be in the
[`Iteration`]s, but by default it uses `()`.

[`Runner`]: struct.Runner.html
[`RewriteScheduler`]: trait.RewriteScheduler.html
[`Extractor`]: struct.Extractor.html
[`Rewrite`]: struct.Rewrite.html
[`BackoffScheduler`]: struct.BackoffScheduler.html
[`EGraph`]: struct.EGraph.html
[`Iteration`]: struct.Iteration.html
[`IterationData`]: trait.IterationData.html

# Example

```
use egg::{*, rewrite as rw};

define_language! {
    enum SimpleLanguage {
        Num(i32),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        Symbol(Symbol),
    }
}

let rules: &[Rewrite<SimpleLanguage, ()>] = &[
    rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
    rw!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),

    rw!("add-0"; "(+ ?a 0)" => "?a"),
    rw!("mul-0"; "(* ?a 0)" => "0"),
    rw!("mul-1"; "(* ?a 1)" => "?a"),
];

pub struct MyIterData {
    smallest_so_far: usize,
}

type MyRunner = Runner<SimpleLanguage, (), MyIterData>;

impl IterationData<SimpleLanguage, ()> for MyIterData {
    fn make(runner: &MyRunner) -> Self {
        let root = runner.roots[0];
        let mut extractor = Extractor::new(&runner.egraph, AstSize);
        MyIterData {
            smallest_so_far: extractor.find_best(root).0,
        }
    }
}

let start = "(+ 0 (* 1 foo))".parse().unwrap();
// Runner is customizable in the builder pattern style.
let runner = MyRunner::new(Default::default())
    .with_iter_limit(10)
    .with_node_limit(10_000)
    .with_expr(&start)
    .with_scheduler(SimpleScheduler)
    .run(rules);

// Now we can check our iteration data to make sure that the cost only
// got better over time
for its in runner.iterations.windows(2) {
    assert!(its[0].data.smallest_so_far >= its[1].data.smallest_so_far);
}

println!(
    "Stopped after {} iterations, reason: {:?}",
    runner.iterations.len(),
    runner.stop_reason
);

```
*/
pub struct Runner<L: Language, N: Analysis<L>, IterData = ()> {
    /// The [`EGraph`](struct.EGraph.html) used.
    pub egraph: EGraph<L, N>,
    /// Data accumulated over each [`Iteration`](struct.Iteration.html).
    pub iterations: Vec<Iteration<IterData>>,
    /// The roots of expressions added by the
    /// [`with_expr`](#method.with_expr) method, in insertion order.
    pub roots: Vec<Id>,
    /// Why the `Runner` stopped. This will be `None` if it hasn't
    /// stopped yet.
    pub stop_reason: Option<StopReason>,

    /// The hooks added by the
    /// [`with_hook`](#method.with_hook) method, in insertion order.
    #[allow(clippy::type_complexity)]
    pub hooks: Vec<Box<dyn FnMut(&mut Self) -> Result<(), String>>>,

    // limits
    iter_limit: usize,
    node_limit: usize,
    time_limit: Duration,

    start_time: Option<Instant>,
    scheduler: Box<dyn RewriteScheduler<L, N>>,
}

impl<L, N> Default for Runner<L, N, ()>
where
    L: Language,
    N: Analysis<L> + Default,
{
    fn default() -> Self {
        Runner::new(N::default())
    }
}

/// Error returned by [`Runner`] when it stops.
///
/// [`Runner`]: struct.Runner.html
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize))]
pub enum StopReason {
    /// The egraph saturated, i.e., there was an iteration where we
    /// didn't learn anything new from applying the rules.
    Saturated,
    /// The iteration limit was hit. The data is the iteration limit.
    IterationLimit(usize),
    /// The enode limit was hit. The data is the enode limit.
    NodeLimit(usize),
    /// The time limit was hit. The data is the time limit in seconds.
    TimeLimit(f64),
    /// Some other reason to stop.
    Other(String),
}

/// Data generated by running a [`Runner`] one iteration.
///
/// If the `serde-1` feature is enabled, this implements
/// [`serde::Serialize`][ser], which is useful if you want to output
/// this as a JSON or some other format.
///
/// [`Runner`]: struct.Runner.html
/// [ser]: https://docs.rs/serde/latest/serde/trait.Serialize.html
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize))]
#[non_exhaustive]
pub struct Iteration<IterData> {
    /// The number of enodes in the egraph at the start of this
    /// iteration.
    pub egraph_nodes: usize,
    /// The number of eclasses in the egraph at the start of this
    /// iteration.
    pub egraph_classes: usize,
    /// A map from rule name to number of times it was _newly_ applied
    /// in this iteration.
    pub applied: IndexMap<String, usize>,
    /// Seconds spent running hooks.
    pub hook_time: f64,
    /// Seconds spent searching in this iteration.
    pub search_time: f64,
    /// Seconds spent applying rules in this iteration.
    pub apply_time: f64,
    /// Seconds spent [`rebuild`](struct.EGraph.html#method.rebuild)ing
    /// the egraph in this iteration.
    pub rebuild_time: f64,
    /// Total time spent in this iteration, including data generation time.
    pub total_time: f64,
    /// The user provided annotation for this iteration
    pub data: IterData,
    /// The number of rebuild iterations done after this iteration completed.
    pub n_rebuilds: usize,
    /// If the runner stopped on this iterations, this is the reason
    pub stop_reason: Option<StopReason>,
}

type RunnerResult<T> = std::result::Result<T, StopReason>;

impl<L, N, IterData> Runner<L, N, IterData>
where
    L: Language,
    N: Analysis<L>,
    IterData: IterationData<L, N>,
{
    /// Create a new `Runner` with the given analysis and default parameters.
    pub fn new(analysis: N) -> Self {
        Self {
            iter_limit: 30,
            node_limit: 10_000,
            time_limit: Duration::from_secs(5),

            egraph: EGraph::new(analysis),
            roots: vec![],
            iterations: vec![],
            stop_reason: None,
            hooks: vec![],

            start_time: None,
            scheduler: Box::new(BackoffScheduler::default()),
        }
    }

    /// Sets the iteration limit. Default: 30
    pub fn with_iter_limit(self, iter_limit: usize) -> Self {
        Self { iter_limit, ..self }
    }

    /// Sets the egraph size limit (in enodes). Default: 10,000
    pub fn with_node_limit(self, node_limit: usize) -> Self {
        Self { node_limit, ..self }
    }

    /// Sets the runner time limit. Default: 5 seconds
    pub fn with_time_limit(self, time_limit: Duration) -> Self {
        Self { time_limit, ..self }
    }

    /// Add a hook to instrument or modify the behavior of a [`Runner`].
    ///
    /// # Example
    /// ```
    /// # use egg::*;
    /// let rules: &[Rewrite<SymbolLang, ()>] = &[
    ///     rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
    ///     // probably some others ...
    /// ];
    ///
    /// Runner::<SymbolLang, ()>::default()
    ///     .with_expr(&"(+ 5 2)".parse().unwrap())
    ///     .with_hook(|runner| {
    ///          println!("Egraph is this big: {}", runner.egraph.total_size());
    ///          Ok(())
    ///     })
    ///     .run(rules);
    /// ```
    /// [`Runner`]: struct.Runner.html
    pub fn with_hook<F>(mut self, hook: F) -> Self
    where
        F: FnMut(&mut Self) -> Result<(), String> + 'static,
    {
        self.hooks.push(Box::new(hook));
        self
    }

    /// Change out the [`RewriteScheduler`] used by this [`Runner`].
    /// The default one is [`BackoffScheduler`].
    ///
    /// [`RewriteScheduler`]: trait.RewriteScheduler.html
    /// [`BackoffScheduler`]: struct.BackoffScheduler.html
    /// [`Runner`]: struct.Runner.html
    pub fn with_scheduler(self, scheduler: impl RewriteScheduler<L, N> + 'static) -> Self {
        let scheduler = Box::new(scheduler);
        Self { scheduler, ..self }
    }

    /// Add an expression to the egraph to be run.
    ///
    /// The eclass id of this addition will be recorded in the
    /// [`roots`](struct.Runner.html#structfield.roots) field, ordered by
    /// insertion order.
    pub fn with_expr(mut self, expr: &RecExpr<L>) -> Self {
        let id = self.egraph.add_expr(expr);
        self.roots.push(id);
        self
    }

    /// Replace the [`EGraph`](struct.EGraph.html) of this `Runner`.
    pub fn with_egraph(self, egraph: EGraph<L, N>) -> Self {
        Self { egraph, ..self }
    }

    /// Run this `Runner` until it stops.
    /// After this, the field
    /// [`stop_reason`](#structfield.stop_reason) is guaranteed to be
    /// set.
    pub fn run<'a, R>(mut self, rules: R) -> Self
    where
        R: IntoIterator<Item = &'a Rewrite<L, N>>,
        L: 'a,
        N: 'a,
    {
        let rules: Vec<&Rewrite<L, N>> = rules.into_iter().collect();
        check_rules(&rules);
        self.egraph.rebuild();
        // TODO check that we haven't
        loop {
            if let Err(stop_reason) = self.run_one(&rules) {
                info!("Stopping: {:?}", stop_reason);
                self.stop_reason = Some(stop_reason);
                // push on a final iteration to mark the end state
                self.iterations.push(Iteration {
                    stop_reason: self.stop_reason.clone(),
                    egraph_nodes: self.egraph.total_number_of_nodes(),
                    egraph_classes: self.egraph.number_of_classes(),
                    data: IterData::make(&self),
                    applied: Default::default(),
                    search_time: Default::default(),
                    hook_time: Default::default(),
                    apply_time: Default::default(),
                    rebuild_time: Default::default(),
                    total_time: Default::default(),
                    n_rebuilds: Default::default(),
                });
                break;
            }
        }

        self
    }

    #[rustfmt::skip]
    /// Prints some information about a runners run.
    pub fn print_report(&self) {
        let search_time: f64 = self.iterations.iter().map(|i| i.search_time).sum();
        let apply_time: f64 = self.iterations.iter().map(|i| i.apply_time).sum();
        let rebuild_time: f64 = self.iterations.iter().map(|i| i.rebuild_time).sum();
        let total_time: f64 = self.iterations.iter().map(|i| i.total_time).sum();

        let iters = self.iterations.len();
        let rebuilds: usize = self.iterations.iter().map(|i| i.n_rebuilds).sum();

        let eg = &self.egraph;
        println!("Runner report");
        println!("=============");
        println!("  Stop reason: {:?}", self.stop_reason.as_ref().unwrap());
        println!("  Iterations: {}", iters);
        println!("  Egraph size: {} nodes, {} classes, {} memo", eg.total_number_of_nodes(), eg.number_of_classes(), eg.total_size());
        println!("  Rebuilds: {}, {:.2} per iter", rebuilds, (rebuilds as f64) / (iters as f64));
        println!("  Total time: {}", total_time);
        println!("    Search:  ({:.2}) {}", search_time / total_time, search_time);
        println!("    Apply:   ({:.2}) {}", apply_time / total_time, apply_time);
        println!("    Rebuild: ({:.2}) {}", rebuild_time / total_time, rebuild_time);
    }

    fn run_one(&mut self, rules: &[&Rewrite<L, N>]) -> RunnerResult<()> {
        assert!(self.stop_reason.is_none());

        info!("\nIteration {}", self.iterations.len());

        self.try_start();
        self.check_limits()?;

        let hook_time = Instant::now();
        let mut hooks = std::mem::take(&mut self.hooks);
        for hook in &mut hooks {
            hook(self).map_err(StopReason::Other)?
        }
        self.hooks = hooks;
        let hook_time = hook_time.elapsed().as_secs_f64();

        let i = self.iterations.len();
        let egraph_nodes = self.egraph.total_size();
        let egraph_classes = self.egraph.number_of_classes();
        trace!("EGraph {:?}", self.egraph.dump());

        let start_time = Instant::now();

        let mut matches = Vec::new();
        for rule in rules {
            let ms = self.scheduler.search_rewrite(i, &self.egraph, rule);
            matches.push(ms);
            if self.check_limits().is_err() {
                // bail on searching, make sure applying doesn't do anything
                matches.clear();
                break;
            }
        }

        let search_time = start_time.elapsed().as_secs_f64();
        info!("Search time: {}", search_time);

        let apply_time = Instant::now();

        let mut applied = IndexMap::new();
        for (rw, ms) in rules.iter().zip(matches) {
            let total_matches: usize = ms.iter().map(|m| m.substs.len()).sum();
            if total_matches == 0 {
                continue;
            }

            debug!("Applying {} {} times", rw.name(), total_matches);

            let actually_matched = self.scheduler.apply_rewrite(i, &mut self.egraph, rw, ms);
            if actually_matched > 0 {
                if let Some(count) = applied.get_mut(rw.name()) {
                    *count += actually_matched;
                } else {
                    applied.insert(rw.name().to_owned(), actually_matched);
                }
                debug!("Applied {} {} times", rw.name(), actually_matched);
            }

            if self.check_limits().is_err() {
                break;
            }
        }

        let apply_time = apply_time.elapsed().as_secs_f64();
        info!("Apply time: {}", apply_time);

        let rebuild_time = Instant::now();
        let n_rebuilds = self.egraph.rebuild();

        let rebuild_time = rebuild_time.elapsed().as_secs_f64();
        info!("Rebuild time: {}", rebuild_time);
        info!(
            "Size: n={}, e={}",
            self.egraph.total_size(),
            self.egraph.number_of_classes()
        );

        let saturated = applied.is_empty() && self.scheduler.can_stop(i);

        self.iterations.push(Iteration {
            applied,
            egraph_nodes,
            egraph_classes,
            hook_time,
            search_time,
            apply_time,
            rebuild_time,
            n_rebuilds,
            data: IterData::make(&self),
            total_time: start_time.elapsed().as_secs_f64(),
            stop_reason: None,
        });

        if saturated {
            Err(StopReason::Saturated)
        } else {
            Ok(())
        }
    }

    fn try_start(&mut self) {
        self.start_time.get_or_insert_with(Instant::now);
    }

    fn check_limits(&self) -> RunnerResult<()> {
        let elapsed = self.start_time.unwrap().elapsed();
        if elapsed > self.time_limit {
            return Err(StopReason::TimeLimit(elapsed.as_secs_f64()));
        }

        let size = self.egraph.total_size();
        if size > self.node_limit {
            return Err(StopReason::NodeLimit(size));
        }

        if self.iterations.len() >= self.iter_limit {
            return Err(StopReason::IterationLimit(self.iterations.len()));
        }

        Ok(())
    }
}

fn check_rules<L, N>(rules: &[&Rewrite<L, N>]) {
    let mut name_counts = IndexMap::new();
    for rw in rules {
        *name_counts.entry(rw.name()).or_default() += 1
    }

    name_counts.retain(|_, count: &mut usize| *count > 1);
    if !name_counts.is_empty() {
        eprintln!("WARNING: Duplicated rule names may affect rule reporting and scheduling.");
        log::warn!("Duplicated rule names may affect rule reporting and scheduling.");
        for (name, &count) in name_counts.iter() {
            assert!(count > 1);
            eprintln!("Rule '{}' appears {} times", name, count);
            log::warn!("Rule '{}' appears {} times", name, count);
        }
    }
}

/** A way to customize how a [`Runner`] runs [`Rewrite`]s.

This gives you a way to prevent certain [`Rewrite`]s from exploding
the [`EGraph`] and dominating how much time is spent while running the
[`Runner`].

[`EGraph`]: struct.EGraph.html
[`Runner`]: struct.Runner.html
[`Rewrite`]: struct.Rewrite.html
*/
#[allow(unused_variables)]
pub trait RewriteScheduler<L, N>
where
    L: Language,
    N: Analysis<L>,
{
    /// Whether or not the [`Runner`](struct.Runner.html) is allowed
    /// to say it has saturated.
    ///
    /// This is only called when the runner is otherwise saturated.
    /// Default implementation just returns `true`.
    fn can_stop(&mut self, iteration: usize) -> bool {
        true
    }

    /// A hook allowing you to customize rewrite searching behavior.
    /// Useful to implement rule management.
    ///
    /// Default implementation just calls
    /// [`Rewrite::search`](struct.Rewrite.html#method.search).
    fn search_rewrite(
        &mut self,
        iteration: usize,
        egraph: &EGraph<L, N>,
        rewrite: &Rewrite<L, N>,
    ) -> Vec<SearchMatches> {
        rewrite.search(egraph)
    }

    /// A hook allowing you to customize rewrite application behavior.
    /// Useful to implement rule management.
    ///
    /// Default implementation just calls
    /// [`Rewrite::apply`](struct.Rewrite.html#method.apply)
    /// and returns number of new applications.
    fn apply_rewrite(
        &mut self,
        iteration: usize,
        egraph: &mut EGraph<L, N>,
        rewrite: &Rewrite<L, N>,
        matches: Vec<SearchMatches>,
    ) -> usize {
        rewrite.apply(egraph, &matches).len()
    }
}

/// A very simple [`RewriteScheduler`] that runs every rewrite every
/// time.
///
/// Using this is basically turning off rule scheduling.
/// It uses the default implementation for all [`RewriteScheduler`]
/// methods.
///
/// This is not the default scheduler; choose it with the
/// [`with_scheduler`](struct.Runner.html#method.with_scheduler)
/// method.
///
/// [`RewriteScheduler`]: trait.RewriteScheduler.html
pub struct SimpleScheduler;

impl<L, N> RewriteScheduler<L, N> for SimpleScheduler
where
    L: Language,
    N: Analysis<L>,
{
}

/// A [`RewriteScheduler`] that implements exponentional rule backoff.
///
/// For each rewrite, there exists a configurable initial match limit.
/// If a rewrite search yield more than this limit, then we ban this
/// rule for number of iterations, double its limit, and double the time
/// it will be banned next time.
///
/// This seems effective at preventing explosive rules like
/// associativity from taking an unfair amount of resources.
///
/// [`BackoffScheduler`] is configurable in the builder-pattern style.
///
/// [`RewriteScheduler`]: trait.RewriteScheduler.html
/// [`BackoffScheduler`]: struct.BackoffScheduler.html
pub struct BackoffScheduler {
    initial_match_limit: usize,
    ban_length: usize,
    stats: IndexMap<String, RuleStats>,
    dont_ban: IndexSet<String>,
}

struct RuleStats {
    times_applied: usize,
    banned_until: usize,
    times_banned: usize,
}

impl BackoffScheduler {
    /// Set the initial match limit after which a rule will be banned.
    /// Default: 1,000
    pub fn with_initial_match_limit(self, initial_match_limit: usize) -> Self {
        Self {
            initial_match_limit,
            ..self
        }
    }

    /// Set the initial ban length.
    /// Default: 5 iterations
    pub fn with_ban_length(self, ban_length: usize) -> Self {
        Self { ban_length, ..self }
    }

    /// Never ban a particular rule.
    pub fn do_not_ban(mut self, name: impl Into<String>) -> Self {
        self.dont_ban.insert(name.into());
        self
    }
}

impl Default for BackoffScheduler {
    fn default() -> Self {
        Self {
            dont_ban: Default::default(),
            stats: Default::default(),
            initial_match_limit: 1_000,
            ban_length: 5,
        }
    }
}

impl<L, N> RewriteScheduler<L, N> for BackoffScheduler
where
    L: Language,
    N: Analysis<L>,
{
    fn can_stop(&mut self, iteration: usize) -> bool {
        let n_stats = self.stats.len();

        let mut banned: Vec<_> = self
            .stats
            .iter_mut()
            .filter(|(_, s)| s.banned_until > iteration)
            .collect();

        if banned.is_empty() {
            true
        } else {
            let min_ban = banned
                .iter()
                .map(|(_, s)| s.banned_until)
                .min()
                .expect("banned cannot be empty here");

            assert!(min_ban >= iteration);
            let delta = min_ban - iteration;

            let mut unbanned = vec![];
            for (name, s) in &mut banned {
                s.banned_until -= delta;
                if s.banned_until == iteration {
                    unbanned.push(name.as_str());
                }
            }

            assert!(!unbanned.is_empty());
            info!(
                "Banned {}/{}, fast-forwarded by {} to unban {}",
                banned.len(),
                n_stats,
                delta,
                unbanned.join(", "),
            );

            false
        }
    }

    fn search_rewrite(
        &mut self,
        iteration: usize,
        egraph: &EGraph<L, N>,
        rewrite: &Rewrite<L, N>,
    ) -> Vec<SearchMatches> {
        if let Some(limit) = self.stats.get_mut(rewrite.name()) {
            if iteration < limit.banned_until {
                debug!(
                    "Skipping {} ({}-{}), banned until {}...",
                    rewrite.name(),
                    limit.times_applied,
                    limit.times_banned,
                    limit.banned_until,
                );
                return vec![];
            }

            let matches = rewrite.search(egraph);
            let total_len: usize = matches.iter().map(|m| m.substs.len()).sum();
            let threshold = self.initial_match_limit << limit.times_banned;
            if total_len > threshold {
                let ban_length = self.ban_length << limit.times_banned;
                limit.times_banned += 1;
                limit.banned_until = iteration + ban_length;
                info!(
                    "Banning {} ({}-{}) for {} iters: {} < {}",
                    rewrite.name(),
                    limit.times_applied,
                    limit.times_banned,
                    ban_length,
                    threshold,
                    total_len,
                );
                vec![]
            } else {
                limit.times_applied += 1;
                matches
            }
        } else {
            if !self.dont_ban.contains(rewrite.name()) {
                self.stats.insert(
                    rewrite.name().into(),
                    RuleStats {
                        times_applied: 0,
                        banned_until: 0,
                        times_banned: 0,
                    },
                );
            }
            rewrite.search(egraph)
        }
    }
}

/// Custom data to inject into the [`Iteration`]s recorded by a [`Runner`]
///
/// This trait allows you to add custom data to the [`Iteration`]s
/// recorded as a [`Runner`] applies rules.
///
/// See the [`Runner`] docs for an example.
///
/// [`Runner`] is generic over the [`IterationData`] that it will be in the
/// [`Iteration`]s, but by default it uses `()`.
///
/// [`Runner`]: struct.Runner.html
/// [`Iteration`]: struct.Iteration.html
/// [`IterationData`]: trait.IterationData.html
pub trait IterationData<L, N>: Sized
where
    L: Language,
    N: Analysis<L>,
{
    /// Given the current [`Runner`](struct.Runner.html), make the
    /// data to be put in this [`Iteration`](struct.Iteration.html).
    fn make(runner: &Runner<L, N, Self>) -> Self;
}

impl<L, N> IterationData<L, N> for ()
where
    L: Language,
    N: Analysis<L>,
{
    fn make(_: &Runner<L, N, Self>) -> Self {}
}
