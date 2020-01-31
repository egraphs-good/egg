use std::cmp::Ordering;
use std::fmt::Debug;

use crate::{EClass, EGraph, ENode, Expr, Id, Language, RecExpr};

use indexmap::IndexMap;

pub struct Extractor<'a, CF: CostFunction<L>, L: Language, M> {
    cost_function: CF,
    costs: IndexMap<Id, CF::Cost>,
    egraph: &'a EGraph<L, M>,
}

pub trait CostFunction<L: Language> {
    type Cost: Ord + Debug + Clone;
    fn cost(&mut self, expr: &Expr<L, Self::Cost>) -> Self::Cost;
    fn cost_rec(&mut self, expr: &RecExpr<L>) -> Self::Cost {
        let child_cost_expr = expr.as_ref().map_children(|e| self.cost_rec(&e));
        self.cost(&child_cost_expr)
    }
}

pub struct AstSize;
impl<L: Language> CostFunction<L> for AstSize {
    type Cost = usize;
    fn cost(&mut self, expr: &Expr<L, Self::Cost>) -> Self::Cost {
        1 + expr.children.iter().copied().sum::<usize>()
    }
}

pub struct AstDepth;
impl<L: Language> CostFunction<L> for AstDepth {
    type Cost = usize;
    fn cost(&mut self, expr: &Expr<L, Self::Cost>) -> Self::Cost {
        1 + expr.children.iter().copied().max().unwrap_or(0)
    }
}

fn cmp<T: Ord>(a: &Option<T>, b: &Option<T>) -> Ordering {
    // None is high
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Greater,
        (Some(_), None) => Ordering::Less,
        (Some(a), Some(b)) => a.partial_cmp(&b).unwrap(),
    }
}

impl<'a, CF, L, M> Extractor<'a, CF, L, M>
where
    CF: CostFunction<L>,
    L: Language,
{
    pub fn new(egraph: &'a EGraph<L, M>, cost_function: CF) -> Self {
        let costs = IndexMap::default();
        let mut extractor = Extractor {
            costs,
            egraph,
            cost_function,
        };
        extractor.find_costs();

        extractor
    }

    pub fn find_best(&mut self, eclass: Id) -> (CF::Cost, RecExpr<L>) {
        let expr = self.find_best_expr(eclass);
        let cost = self.cost_function.cost_rec(&expr);
        (cost, expr)
    }

    fn find_best_expr(&mut self, eclass: Id) -> RecExpr<L> {
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

    fn node_total_cost(&mut self, node: &ENode<L>) -> Option<CF::Cost> {
        let expr = node
            .map_children_result(|id| self.costs.get(&id).cloned().ok_or(()))
            .ok()?;
        Some(self.cost_function.cost(&expr))
    }

    fn find_costs(&mut self) {
        let mut did_something = true;
        while did_something {
            did_something = false;

            for class in self.egraph.classes() {
                let pass = self.make_pass(class);
                match (self.costs.get(&class.id), pass) {
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

    fn make_pass(&mut self, eclass: &EClass<L, M>) -> Option<CF::Cost> {
        eclass
            .iter()
            .map(|n| self.node_total_cost(n))
            .min_by(cmp)
            .unwrap()
    }
}
