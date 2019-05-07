use crate::{
    egraph::EGraph,
    expr::{Expr, FlatExpr, Id, Language},
    util::HashMap,
};

use log::*;

pub type Cost = u64;

fn calculate_cost_rec<L: Language>(
    map: &mut HashMap<Expr<L, Id>, Id>,
    expr: &FlatExpr<L>,
    id: Id,
) -> (Cost, Id) {
    let node = expr.get_node(id);
    let mut cost = L::cost(&node);

    let node = node.map_children(|child| {
        let (child_cost, child_id) = calculate_cost_rec(map, expr, child);
        cost += child_cost;
        child_id
    });

    if let Some(id) = map.get(&node) {
        return (1, *id);
    }

    map.insert(node.clone(), id);
    (cost, id)
}

pub fn calculate_cost<L: Language>(expr: &FlatExpr<L>) -> Cost {
    let mut map = HashMap::default();
    let (cost, _) = calculate_cost_rec(&mut map, expr, expr.root);
    // trace!("Found cost to be {}\n  {}", cost, expr.to_sexp());
    cost
}

pub struct CostExpr<L: Language> {
    pub cost: Cost,
    pub expr: FlatExpr<L>,
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

    fn build_expr(&self, root: &Expr<L, Id>) -> Option<FlatExpr<L>> {
        let children: Option<Vec<_>> = root
            .children()
            .iter()
            .map(|id| self.costs.get(id).map(|ce| &ce.expr))
            .collect();
        let mut children_roots = Vec::new();
        let mut offset = 0;
        let mut expr = FlatExpr::default();
        for child_expr in children? {
            for node in &child_expr.nodes {
                expr.nodes.push(node.map_children(|id| id + offset));
            }
            children_roots.push(child_expr.root + offset);
            offset += child_expr.nodes.len() as u32;
        }

        expr.root = expr.add(match root {
            Expr::Variable(_) | Expr::Constant(_) => root.clone(),
            Expr::Operator(op, _) => Expr::Operator(op.clone(), children_roots),
        });

        Some(expr)
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

            for id in self.egraph.classes.keys() {
                did_something |= self.make_pass(*id);
            }

            loops += 1;
        }

        info!("Took {} loops to find costs", loops);
    }

    fn make_pass(&mut self, id: Id) -> bool {
        let new = self
            .egraph
            .get_eclass(id)
            .iter()
            .filter_map(|n| self.node_total_cost(n))
            .min_by_key(|ce| ce.cost);

        let new = match new {
            Some(new) => new,
            None => return true,
        };

        if let Some(old) = self.costs.get(&id) {
            if new.cost < old.cost {
                self.costs.insert(id, new);
                true
            } else {
                false
            }
        } else {
            self.costs.insert(id, new);
            true
        }
    }
}
