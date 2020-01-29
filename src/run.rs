use std::fmt;

use indexmap::IndexMap;
use instant::Instant;
use log::*;

use crate::{
    egraph::{EGraph, Metadata},
    expr::{Id, Language, RecExpr},
    pattern::EClassMatches,
    rewrite::Rewrite,
};

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize))]
#[non_exhaustive]
pub struct Iteration {
    pub egraph_nodes: usize,
    pub egraph_classes: usize,
    pub applied: IndexMap<String, usize>,
    pub search_time: f64,
    pub apply_time: f64,
    pub rebuild_time: f64,
    // TODO optionally put best cost back in there
    // pub best_cost: Cost,
}

#[derive(Debug, Clone)]
#[cfg_attr(
    feature = "serde-1",
    derive(serde::Serialize),
    serde(bound(serialize = "L: Language + std::fmt::Display"))
)]
#[non_exhaustive]
pub struct RunReport<L, E> {
    pub initial_expr: RecExpr<L>,
    pub initial_expr_eclass: Id,
    // pub initial_cost: Cost,
    pub iterations: Vec<Iteration>,
    // pub final_expr: RecExpr<L>,
    // pub final_cost: Cost,
    pub rules_time: f64,
    // pub extract_time: f64,
    pub stop_reason: E,
    // metrics
    // pub ast_size: usize,
    // pub ast_depth: usize,
}

pub trait Runner<L, M>
where
    L: Language,
    M: Metadata<L>,
{
    type Error: fmt::Debug;
    // TODO make it so Runners can add fields to Iteration data

    fn pre_step(&mut self, _egraph: &mut EGraph<L, M>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn post_step(
        &mut self,
        _iteration: &Iteration,
        _egraph: &mut EGraph<L, M>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn during_step(&mut self, _egraph: &EGraph<L, M>) -> Result<(), Self::Error> {
        Ok(())
    }

    /// Dictates how matches will be applied.
    fn apply_matches(
        &mut self,
        egraph: &mut EGraph<L, M>,
        rewrite: &Rewrite<L, M>,
        matches: Vec<EClassMatches>,
    ) -> usize {
        rewrite.apply(egraph, &matches).len()
    }

    fn step(
        &mut self,
        egraph: &mut EGraph<L, M>,
        rules: &[Rewrite<L, M>],
    ) -> Result<Iteration, Self::Error> {
        let egraph_nodes = egraph.total_size();
        let egraph_classes = egraph.number_of_classes();
        trace!("EGraph {:?}", egraph.dump());

        let search_time = Instant::now();

        let mut matches = Vec::new();
        for rule in rules.iter() {
            let ms = rule.search(egraph);
            matches.push(ms);
            self.during_step(egraph)?
        }

        let search_time = search_time.elapsed().as_secs_f64();
        info!("Search time: {}", search_time);

        let apply_time = Instant::now();

        let mut applied = IndexMap::new();
        for (rw, ms) in rules.iter().zip(matches) {
            let total_matches: usize = ms.iter().map(|m| m.mappings.len()).sum();
            if total_matches == 0 {
                continue;
            }

            debug!("Applying {} {} times", rw.name, total_matches);

            let actually_matched = self.apply_matches(egraph, rw, ms);
            if actually_matched > 0 {
                // applications.push((&m.rewrite.name, actually_matched));
                if let Some(count) = applied.get_mut(&rw.name) {
                    *count += 1;
                } else {
                    applied.insert(rw.name.to_owned(), 1);
                }
                debug!("Applied {} {} times", rw.name, actually_matched);
            }

            self.during_step(egraph)?
        }

        let apply_time = apply_time.elapsed().as_secs_f64();
        info!("Apply time: {}", apply_time);

        let rebuild_time = Instant::now();
        egraph.rebuild();

        let rebuild_time = rebuild_time.elapsed().as_secs_f64();
        info!("Rebuild time: {}", rebuild_time);
        info!(
            "Size: n={}, e={}",
            egraph.total_size(),
            egraph.number_of_classes()
        );

        trace!("Running post_step...");
        Ok(Iteration {
            applied,
            egraph_nodes,
            egraph_classes,
            search_time,
            apply_time,
            rebuild_time,
            // best_cost,
        })
    }

    fn run(
        &mut self,
        egraph: &mut EGraph<L, M>,
        rules: &[Rewrite<L, M>],
    ) -> (Vec<Iteration>, Self::Error) {
        let mut iterations = vec![];
        let mut fn_loop = || -> Result<(), Self::Error> {
            loop {
                trace!("Running pre_step...");
                self.pre_step(egraph)?;
                trace!("Running step...");
                iterations.push(self.step(egraph, rules)?);
                trace!("Running post_step...");
                self.post_step(iterations.last().unwrap(), egraph)?;
            }
        };
        let stop_reason = fn_loop().unwrap_err();
        info!("Stopping {:?}", stop_reason);
        (iterations, stop_reason)
    }

    fn run_expr(
        &mut self,
        initial_expr: RecExpr<L>,
        rules: &[Rewrite<L, M>],
    ) -> (EGraph<L, M>, RunReport<L, Self::Error>) {
        // let initial_cost = calculate_cost(&initial_expr);
        // info!("Without empty: {}", initial_expr.pretty(80));

        let (mut egraph, initial_expr_eclass) = EGraph::from_expr(&initial_expr);

        let rules_time = Instant::now();
        let (iterations, stop_reason) = self.run(&mut egraph, rules);
        let rules_time = rules_time.elapsed().as_secs_f64();

        // let extract_time = Instant::now();
        // let best = Extractor::new(&egraph).find_best(root);
        // let extract_time = extract_time.elapsed().as_secs_f64();

        // info!("Extract time: {}", extract_time);
        // info!("Initial cost: {}", initial_cost);
        // info!("Final cost: {}", best.cost);
        // info!("Final: {}", best.expr.pretty(80));

        let report = RunReport {
            iterations,
            rules_time,
            // extract_time,
            stop_reason,
            // ast_size: best.expr.ast_size(),
            // ast_depth: best.expr.ast_depth(),
            initial_expr,
            initial_expr_eclass,
            // initial_cost,
            // final_cost: best.cost,
            // final_expr: best.expr,
        };
        (egraph, report)
    }
}

#[non_exhaustive]
pub struct SimpleRunner {
    iter_limit: usize,
    node_limit: usize,
    i: usize,
}

impl Default for SimpleRunner {
    fn default() -> Self {
        Self {
            iter_limit: 30,
            node_limit: 10_000,
            i: 0,
        }
    }
}

impl SimpleRunner {
    pub fn with_iter_limit(self, iter_limit: usize) -> Self {
        Self { iter_limit, ..self }
    }
    pub fn with_node_limit(self, node_limit: usize) -> Self {
        Self { node_limit, ..self }
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize))]
pub enum SimpleRunnerError {
    Saturated,
    IterationLimit(usize),
    NodeLimit(usize),
}

impl<L, M> Runner<L, M> for SimpleRunner
where
    L: Language,
    M: Metadata<L>,
{
    type Error = SimpleRunnerError;

    fn pre_step(&mut self, egraph: &mut EGraph<L, M>) -> Result<(), Self::Error> {
        info!(
            "\n\nIteration {}, n={}, e={}",
            self.i,
            egraph.total_size(),
            egraph.number_of_classes()
        );
        if self.i >= self.iter_limit {
            Err(SimpleRunnerError::IterationLimit(self.i))
        } else {
            Ok(())
        }
    }

    fn during_step(&mut self, egraph: &EGraph<L, M>) -> Result<(), Self::Error> {
        let size = egraph.total_size();
        if size > self.node_limit {
            Err(SimpleRunnerError::NodeLimit(size))
        } else {
            Ok(())
        }
    }

    fn post_step(
        &mut self,
        iteration: &Iteration,
        _egraph: &mut EGraph<L, M>,
    ) -> Result<(), Self::Error> {
        self.i += 1;
        if iteration.applied.is_empty() {
            Err(SimpleRunnerError::Saturated)
        } else {
            Ok(())
        }
    }
}
