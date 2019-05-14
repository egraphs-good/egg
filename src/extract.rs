use crate::{
    egraph::{EClass, EGraph},
    expr::{Expr, Id, Language, RecExpr},
    util::HashMap,
};

use log::*;

pub type Cost = u64;

fn calculate_cost_rec<L: Language>(map: &mut HashMap<RecExpr<L>, Cost>, expr: &RecExpr<L>) -> Cost {
    if map.contains_key(expr) {
        return 1;
    }

    let child_cost_expr = expr.as_ref().map_children(|e| calculate_cost_rec(map, &e));
    let cost = L::cost(&child_cost_expr);

    map.insert(expr.clone(), cost);
    cost
}

pub fn calculate_cost<L: Language>(expr: &RecExpr<L>) -> Cost {
    let mut map = HashMap::default();
    let cost = calculate_cost_rec(&mut map, expr);
    trace!("Found cost to be {}\n  {}", cost, expr.to_sexp());
    cost
}

pub struct CostExpr<L: Language> {
    pub cost: Cost,
    pub expr: RecExpr<L>,
}

pub struct Extractor<'a, L: Language> {
    costs: HashMap<Id, CostExpr<L>>,
    egraph: &'a EGraph<L>,
}

impl<'a, L: Language> Extractor<'a, L> {
    pub fn new(egraph: &'a EGraph<L>) -> Self {
        // initialize costs with the maximum value
        let costs = HashMap::default();

        let mut extractor = Extractor { costs, egraph };
        extractor.find_costs();

        extractor
    }

    pub fn find_best(&self, eclass: Id) -> &CostExpr<L> {
        &self.costs[&eclass]
    }

    fn build_expr(&self, root: &Expr<L, Id>) -> Option<RecExpr<L>> {
        let expr = root
            .map_children_result(|id| {
                self.costs
                    .get(&id)
                    .map(|cost_expr| cost_expr.expr.clone())
                    .ok_or(())
            })
            .ok()?;
        Some(expr.into())
    }

    fn node_total_cost(&self, node: &Expr<L, Id>) -> Option<CostExpr<L>> {
        let expr = self.build_expr(node)?;
        let cost = calculate_cost(&expr);
        Some(CostExpr { cost, expr })
    }

    fn find_costs(&mut self) {
        let mut did_something = true;
        let mut loops = 0;
        while did_something {
            did_something = false;

            for class in self.egraph.classes() {
                did_something |= self.make_pass(class);
            }

            loops += 1;
        }

        info!("Took {} loops to find costs", loops);
    }

    fn make_pass(&mut self, class: &EClass<L>) -> bool {
        let new = class
            .iter()
            .filter_map(|n| self.node_total_cost(n))
            .min_by_key(|ce| ce.cost);

        let new = match new {
            Some(new) => new,
            None => return true,
        };

        if let Some(old) = self.costs.get(&class.id) {
            if new.cost < old.cost {
                self.costs.insert(class.id, new);
                true
            } else {
                false
            }
        } else {
            self.costs.insert(class.id, new);
            true
        }
    }
}
