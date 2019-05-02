use std::collections::HashMap;

use crate::{
    egraph::EGraph,
    expr::{Expr, Id, Node, NodeLike},
};

pub type Cost = u64;

pub struct Extractor<'a, N: NodeLike> {
    costs: HashMap<Id, Cost>,
    egraph: &'a EGraph<N>,
}

impl<'a, N: NodeLike> Extractor<'a, N> {
    pub fn new(egraph: &'a EGraph<N>) -> Self {
        // initialize costs with the maximum value
        let mut costs = HashMap::new();
        for id in egraph.classes.keys() {
            costs.insert(*id, Cost::max_value());
        }

        let mut extractor = Extractor { costs, egraph };
        extractor.find_costs();

        extractor
    }

    pub fn find_best(&self, eclass: Id) -> Expr<N> {
        let mut expr = Expr::default();
        expr.root = self.find_best_rec(eclass, &mut expr);
        expr
    }

    fn find_best_rec(&self, eclass: Id, expr: &mut Expr<N>) -> Id {
        let best_node = self
            .egraph
            .get_eclass(eclass)
            .iter()
            .min_by_key(|n| self.node_total_cost(n))
            .expect("eclass shouldn't be empty");

        let best_transformed = best_node.clone().map_children(|child| {
            let class = self.egraph.just_find(child);
            self.find_best_rec(class, expr)
        });

        expr.add(best_transformed)
    }

    fn node_total_cost(&self, node: &Node<N, Id>) -> Cost {
        let mut cost = N::cost(&node);
        for child in node.children() {
            let class = self.egraph.just_find(*child);
            cost = cost.saturating_add(self.costs[&class])
        }
        cost
    }

    fn find_costs(&mut self) {
        let mut did_something = true;
        while did_something {
            did_something = false;

            for (id, class) in &self.egraph.classes {
                let cost = self.make_pass(class);
                if cost < self.costs[id] {
                    did_something = true;
                    self.costs.insert(*id, cost);
                }
            }
        }
    }

    fn make_pass(&self, eclass: &[Node<N, Id>]) -> Cost {
        eclass
            .iter()
            .map(|n| self.node_total_cost(n))
            .min()
            .expect("eclass shouldn't be empty")
    }
}
