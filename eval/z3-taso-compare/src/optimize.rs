use crate::{model::*, rewrites::*};
use egg::*;

// NOTE this optimizer needs to be hooked to the Analysis

pub fn optimize(e: &RecExpr<Mdl>) -> RecExpr<Mdl> {
    let runner: Runner<Mdl, (), ()> = Runner::default().with_expr(e).run(&rules());
    let (egraph, root) = (runner.egraph, runner.roots[0]);
    let mut extractor = Extractor::new(&egraph, Cost);
    extractor.find_best(root).1
}

struct Cost;
impl CostFunction<Mdl> for Cost {
    type Cost = (f64, Vec<usize>);
    fn cost<C: FnMut(Id) -> Self::Cost>(&mut self, enode: &Mdl, mut costs: C) -> Self::Cost {
        let children_sizes = enode.fold(vec![], |mut sizes, id| {
            sizes.push(costs(id).1);
            sizes
        });
        layouts(enode)
            .into_iter()
            .map(|layout| Self::run_time(enode, layout, &children_sizes))
            .min_by(|(x, _), (y, _)| x.partial_cmp(y).unwrap())
            .unwrap()
        // TODO gotta calc output sizes
    }
}

struct Layout;
fn layouts(_e: &Mdl) -> Vec<Layout> {
    todo!()
}

impl Cost {
    fn run_time(
        _e: &Mdl,
        _layout: Layout,
        _sizes: &[Vec<usize>],
    ) -> <Cost as CostFunction<Mdl>>::Cost {
        todo!()
    }
}
