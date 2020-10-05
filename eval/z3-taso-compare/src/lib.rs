pub mod model;
pub mod optimize;
pub mod parse;
pub mod rewrites;

pub mod verify {
    use crate::model::*;
    use crate::rewrites::*;
    use egg::*;

    type ExprPair = (RecExpr<Mdl>, RecExpr<Mdl>);
    // returns failed pairs
    pub fn verify(pairs: &[ExprPair]) -> Vec<ExprPair> {
        let mut runner = Runner::<Mdl, (), ()>::default();
        for (l, r) in pairs {
            runner = runner.with_expr(l).with_expr(r);
        }

        println!("Running...");
        let runner = runner.run(&rules());
        println!("Runner complete!");
        println!("  Nodes: {}", runner.egraph.total_size());
        println!("  Classes: {}", runner.egraph.number_of_classes());
        println!("  Stopped: {:?}", runner.stop_reason.unwrap());

        let mut failed = vec![];
        for (i, roots) in runner.roots.chunks(2).enumerate() {
            let eg = &runner.egraph;
            if eg.find(roots[0]) != eg.find(roots[1]) {
                failed.push(pairs[i].clone());
            }
        }

        failed
    }

    pub fn verify_nb(pairs: &[ExprPair]) {
        for (l, r) in pairs {
            let mut runner = Runner::<Mdl, (), ()>::default();
            runner = runner.with_expr(l).with_expr(r);
            let res = runner
                .with_hook(|runner| {
                    let eg = &runner.egraph;
                    if eg.find(runner.roots[0]) == eg.find(runner.roots[1]) {
                        Err("proven eq".to_string())
                    } else {
                        Ok(())
                    }
                })
                .run(&rules());
            assert!({
                let eg = &res.egraph;
                eg.find(res.roots[0]) == eg.find(res.roots[1])
            })
        }
    }
}
