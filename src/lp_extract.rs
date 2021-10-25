use crate::*;
use good_lp::*;

/// A cost function to be used by an [`LpExtractor`].
pub trait LpCostFunction<L: Language, N: Analysis<L>> {
    /// Returns the cost of the given e-node.
    ///
    /// This function may look at other parts of the e-graph to compute the cost
    /// of the given e-node.
    fn node_cost(&mut self, egraph: &EGraph<L, N>, eclass: Id, enode: &L) -> f64;
}

impl<L: Language, N: Analysis<L>> LpCostFunction<L, N> for AstSize {
    fn node_cost(&mut self, _egraph: &EGraph<L, N>, _eclass: Id, _enode: &L) -> f64 {
        1.0
    }
}

/// A structure to perform extraction using integer linear programming.
/// This uses the [`good_lp`](https://docs.rs/good_lp) library,
/// and it must be enabled using the `good_lp` feature on egg.
///
/// `good_lp` supports many solvers, but the easiest to use is [`cbc`](https://projects.coin-or.org/Cbc).
/// You must have it installed on your machine to use this feature.
/// You can install it using:
///
/// | OS               | Command                                  |
/// |------------------|------------------------------------------|
/// | Fedora / Red Hat | `sudo dnf install coin-or-Cbc-devel`     |
/// | Ubuntu / Debian  | `sudo apt-get install coinor-libcbc-dev` |
/// | macOS            | `brew install cbc`                       |
///
/// # Example
/// ```
/// use egg::*;
/// let mut egraph = EGraph::<SymbolLang, ()>::default();
///
/// let f = egraph.add_expr(&"(f x x x)".parse().unwrap());
/// let g = egraph.add_expr(&"(g x x)".parse().unwrap());
/// egraph.union(f, g);
/// egraph.rebuild();
///
/// let best = Extractor::new(&egraph, AstSize).find_best(f).1;
/// let lp_best = LpExtractor::new(&egraph, AstSize).solve(f);
///
/// // In regular extraction, cost is measures on the tree.
/// assert_eq!(best.to_string(), "(g x x)");
///
/// // Using ILP only counts common sub-expressions once,
/// // so it can lead to a smaller DAG expression.
/// assert_eq!(lp_best.to_string(), "(f x x x)");
/// assert_eq!(lp_best.as_ref().len(), 2);
/// ```
pub struct LpExtractor<'a, L: Language, N: Analysis<L>> {
    egraph: &'a EGraph<L, N>,
    max_order: f64,
    problem: good_lp::variable::UnsolvedProblem,
    vars: HashMap<Id, ClassVars>,
}

struct ClassVars {
    active: Variable,
    order: Variable,
    nodes: Vec<Variable>,
}

impl<'a, L, N> LpExtractor<'a, L, N>
where
    L: Language,
    N: Analysis<L>,
{
    /// Create an [`LpExtractor`] using costs from the given [`LpCostFunction`].
    /// See those docs for details.
    pub fn new<CF>(egraph: &'a EGraph<L, N>, mut cost_function: CF) -> Self
    where
        CF: LpCostFunction<L, N>,
    {
        let max_order = egraph.total_number_of_nodes() as f64 * 10.0;

        let bool_kind = VariableDefinition::new().binary();
        let order_kind = VariableDefinition::new().max(max_order);

        let mut problem_vars = good_lp::ProblemVariables::default();
        let vars: HashMap<Id, ClassVars> = egraph
            .classes()
            .map(|class| {
                let cvars = ClassVars {
                    active: problem_vars.add(bool_kind.clone()),
                    order: problem_vars.add(order_kind.clone()),
                    nodes: problem_vars.add_vector(bool_kind.clone(), class.len()),
                };
                (class.id, cvars)
            })
            .collect();

        // cost is the weighted sum of all the nodes
        let mut cost: Expression = 0.into();
        for class in egraph.classes() {
            for (node, &node_active) in class.iter().zip(&vars[&class.id].nodes) {
                cost += node_active * cost_function.node_cost(egraph, class.id, node)
            }
        }

        let problem = problem_vars.minimise(cost);

        Self {
            egraph,
            problem,
            vars,
            max_order,
        }
    }

    /// Extract a single rooted term using the default solver from [`good_lp`](https://docs.rs/good_lp/),
    /// which is typically cbc.
    ///
    /// This is just a shortcut for [`LpExtractor::solve_multiple_using`].
    pub fn solve(self, root: Id) -> RecExpr<L> {
        self.solve_multiple_using(&[root], good_lp::default_solver)
            .0
    }

    /// Extract (potentially multiple) roots using the given
    /// [`good_lp::Solver`](https://docs.rs/good_lp/1.2.0/good_lp/solvers/trait.Solver.html).
    pub fn solve_multiple_using<S>(self, roots: &[Id], solver: S) -> (RecExpr<L>, Vec<Id>)
    where
        S: good_lp::Solver,
    {
        let egraph = self.egraph;
        let mut model = self.problem.using(solver);

        for (&id, class_vars) in &self.vars {
            let active: Expression = class_vars.active.into();
            let sum_nodes: Expression = class_vars.nodes.iter().sum();

            let class_order: Expression = class_vars.order.into();

            // choosing class implies choosing one of the nodes
            model.add_constraint(active.leq(sum_nodes));

            for (node, &node_var) in self.egraph[id].iter().zip(&class_vars.nodes) {
                let node_active: Expression = node_var.into();
                for child in node.children() {
                    let child = &egraph.find(*child);
                    // choosing a node implies choosing each child
                    model.add_constraint(node_active.clone().leq(self.vars[child].active));
                    // choosing a node also implies this node must be ordered before its children
                    let child_order: Expression = self.vars[child].order.into();
                    let left: Expression =
                        class_order.clone() + node_active.clone() * self.max_order + 1.0;
                    let right: Expression = child_order + self.vars[child].active * self.max_order;
                    model.add_constraint(left.leq(right));
                }
            }
        }

        for root in roots {
            let root = &self.vars[&egraph.find(*root)];
            model.add_constraint(Expression::from(root.active).eq(1));
            model.add_constraint(Expression::from(root.order).eq(0));
        }

        let solution = model.solve().unwrap();

        let mut active: Vec<(f64, Id, usize)> = vec![];
        for (&id, v) in &self.vars {
            let order = solution.value(v.order);
            if solution.value(v.active) > 0.0 {
                let node_idx = v
                    .nodes
                    .iter()
                    .position(|&n| solution.value(n) > 0.0)
                    .unwrap();
                active.push((order, id, node_idx))
            }
        }

        active.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap().reverse());

        let mut ids: HashMap<Id, Id> = HashMap::default();
        let nodes: Vec<L> = active
            .into_iter()
            .enumerate()
            .map(|(i, (_order, id, node_idx))| {
                ids.insert(id, Id::from(i));
                let node = egraph[id].nodes[node_idx].clone();
                node.map_children(|child| ids[&child])
            })
            .collect();

        let root_idxs = roots.iter().map(|root| ids[&egraph.find(*root)]).collect();

        (nodes.into(), root_idxs)
    }
}

#[cfg(test)]
mod tests {
    use crate::{SymbolLang as S, *};

    #[test]
    fn simple_lp_extract_two() {
        let mut egraph = EGraph::<S, ()>::default();
        let a = egraph.add(S::leaf("a"));
        let plus = egraph.add(S::new("+", vec![a, a]));
        let f = egraph.add(S::new("f", vec![plus]));
        let g = egraph.add(S::new("g", vec![plus]));
        let ext = LpExtractor::new(&egraph, AstSize);
        let (exp, ids) = ext.solve_multiple_using(&[f, g], good_lp::default_solver);
        assert_eq!(exp.as_ref().len(), 4);
        assert_eq!(ids.len(), 2);
        println!("{:?}", exp);
    }
}
