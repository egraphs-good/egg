pub mod schedulers {
    use egg::*;
    use rayon::prelude::*;

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
}
