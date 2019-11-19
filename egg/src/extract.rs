use crate::{
    egraph::{EClass, EGraph},
    expr::{Cost, Expr, Id, Language, RecExpr},
};
use std::cmp::Ordering;

use indexmap::IndexMap;
use log::*;

fn cost_cse_rec<L: Language>(map: &mut IndexMap<RecExpr<L>, Cost>, expr: &RecExpr<L>) -> Cost {
    if map.contains_key(expr) {
        return 1.0;
    }

    let child_cost_expr = expr.as_ref().map_children(|e| cost_cse_rec(map, &e));
    let cost = child_cost_expr.cost();
    map.insert(expr.clone(), cost);
    cost
}

pub fn calculate_cost_cse<L: Language>(expr: &RecExpr<L>) -> Cost {
    let mut map = IndexMap::default();
    let cost = cost_cse_rec(&mut map, expr);

    trace!("Found cost to be {}\n  {:?}", cost, expr);
    cost
}

pub fn calculate_cost<L: Language>(expr: &RecExpr<L>) -> Cost {
    let child_cost_expr = expr.as_ref().map_children(|e| calculate_cost(&e));
    child_cost_expr.cost()
}

pub struct CostExpr<L: Language> {
    pub cost: Cost,
    pub expr: RecExpr<L>,
}

pub struct Extractor<'a, L: Language, M> {
    costs: IndexMap<Id, Cost>,
    egraph: &'a EGraph<L, M>,
}

fn cmp(a: &Option<Cost>, b: &Option<Cost>) -> Ordering {
    // None is high
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Greater,
        (Some(_), None) => Ordering::Less,
        (Some(a), Some(b)) => a.partial_cmp(&b).unwrap(),
    }
}

impl<'a, L: Language, M> Extractor<'a, L, M> {
    pub fn new(egraph: &'a EGraph<L, M>) -> Self {
        let costs = IndexMap::default();
        let mut extractor = Extractor { costs, egraph };
        extractor.find_costs();

        extractor
    }

    pub fn find_best(&self, eclass: Id) -> CostExpr<L> {
        let expr = self.find_best_expr(eclass);
        let cost = calculate_cost(&expr);
        CostExpr { cost, expr }
    }

    fn find_best_expr(&self, eclass: Id) -> RecExpr<L> {
        let eclass = self.egraph.find(eclass);

        let best_node = self.egraph[eclass]
            .iter()
            .min_by(|a, b| {
                let a = self.node_total_cost(a);
                let b = self.node_total_cost(b);
                cmp(&a, &b)
            })
            .expect("eclass shouldn't be empty");

        best_node
            .clone()
            .map_children(|child| self.find_best_expr(child))
            .into()
    }

    fn node_total_cost(&self, node: &Expr<L, Id>) -> Option<Cost> {
        let expr = node
            .map_children_result(|id| self.costs.get(&id).cloned().ok_or(()))
            .ok()?;
        Some(expr.cost())
    }

    fn find_costs(&mut self) {
        let mut did_something = true;
        while did_something {
            did_something = false;

            for class in self.egraph.classes() {
                match (self.costs.get(&class.id), self.make_pass(class)) {
                    (None, Some(cost)) => {
                        self.costs.insert(class.id, cost);
                        did_something = true;
                    }
                    (Some(old), Some(new)) if new < *old => {
                        self.costs.insert(class.id, new);
                        did_something = true;
                    }
                    _ => (),
                }
            }
        }
    }

    fn make_pass(&self, eclass: &EClass<L, M>) -> Option<Cost> {
        eclass
            .iter()
            .map(|n| self.node_total_cost(n))
            .min_by(cmp)
            .unwrap()
    }
}
