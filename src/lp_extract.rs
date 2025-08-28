use good_lp::{
    default_solver, variable, variables, Expression, Solution, SolutionStatus, Solver, SolverModel,
    Variable,
};
use std::time::Instant;

use crate::*;

/// A cost function to be used by an [`LpExtractor`].
#[cfg_attr(docsrs, doc(cfg(feature = "lp")))]
pub trait LpCostFunction<L: Language, N: Analysis<L>> {
    /// Returns the cost of the given e-node.
    ///
    /// This function may look at other parts of the e-graph to compute the cost
    /// of the given e-node.
    fn node_cost(&mut self, egraph: &EGraph<L, N>, eclass: Id, enode: &L) -> f64;
}

#[cfg_attr(docsrs, doc(cfg(feature = "lp")))]
impl<L: Language, N: Analysis<L>> LpCostFunction<L, N> for AstSize {
    fn node_cost(&mut self, _egraph: &EGraph<L, N>, _eclass: Id, _enode: &L) -> f64 {
        1.0
    }
}

/// A structure to perform extraction using integer linear programming.
///
/// This uses the [`good_lp`](https://docs.rs/good_lp) to support multiple solving
/// backends. The default backend is [`cbc`](https://projects.coin-or.org/Cbc).
/// You must have it installed on your machine or choose a different backend (see below).
/// You can install `cbc` using:
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
/// let g = egraph.add_expr(&"(g (g x))".parse().unwrap());
/// egraph.union(f, g);
/// egraph.rebuild();
///
/// let best = Extractor::new(&egraph, AstSize).find_best(f).1;
/// let lp_best = LpExtractor::new(&egraph, AstSize).solve(f);
///
/// // In regular extraction, cost is measures on the tree.
/// assert_eq!(best.to_string(), "(g (g x))");
///
/// // Using ILP only counts common sub-expressions once,
/// // so it can lead to a smaller DAG expression.
/// assert_eq!(lp_best.to_string(), "(f x x x)");
/// assert_eq!(lp_best.len(), 2);
/// ```
///
/// # Configuring the LP backend
///
/// Enable the corresponding `good_lp` feature in your own crate. For example,
/// in your `Cargo.toml`:
///
/// ```toml
/// [dependencies]
/// egg = { version = "0.10", features = ["lp"] }
/// good_lp = { version = "1", features = ["coin_cbc"] } # or highs, microlp, etc.
/// ```
///
/// See the (`good_lp` documentation)[https://docs.rs/good_lp/1/good_lp/solvers/index.html]
///
/// At run time, select the solver by calling [`Self::solve_with`] or [`Self::solve_multiple_with`]
/// and passing one of the enabled `good_lp` solver implementations.
///
///  - Example (CBC):
///   ```rust,ignore
///   # use egg::*;
///   use good_lp::coin_cbc;
///   # let egraph: &EGraph<SymbolLang, ()> = &EGraph::default();
///   # let root = Id::from(0usize);
///   let rec = LpExtractor::new(egraph, AstSize)
///     .solve_with(root, coin_cbc);
///   # let _ = rec;
///   ```
/// - Example (HiGHS):
///   ```rust,ignore
///   # use egg::*;
///   use good_lp::highs;
///   # let egraph: &EGraph<SymbolLang, ()> = &EGraph::default();
///   # let root = Id::from(0usize);
///   let rec = LpExtractor::new(egraph, AstSize)
///       .solve_with(root, highs);
///   # let _ = rec;
/// ```
///
#[cfg_attr(docsrs, doc(cfg(feature = "lp")))]
pub struct LpExtractor<'a, L: Language, N: Analysis<L>> {
    egraph: &'a EGraph<L, N>,
    // Precomputed per-node costs to avoid storing the cost function
    costs: HashMap<Id, Vec<f64>>, // for each class id, cost per node index
    // Nodes that would introduce cycles and must be disabled
    cyclic_nodes: HashSet<(Id, usize)>,
}

struct ClassVars {
    active: Variable,
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
        // Precompute costs per node and detect cyclic nodes once
        let mut cyclic_nodes: HashSet<(Id, usize)> = Default::default();
        find_cycles(egraph, |id, i| {
            cyclic_nodes.insert((id, i));
        });

        let mut costs: HashMap<Id, Vec<f64>> = HashMap::default();
        for class in egraph.classes() {
            let mut node_costs = Vec::with_capacity(class.nodes.len());
            for node in &class.nodes {
                node_costs.push(cost_function.node_cost(egraph, class.id, node));
            }
            costs.insert(class.id, node_costs);
        }

        Self {
            egraph,
            costs,
            cyclic_nodes,
        }
    }

    /// Extract a single rooted term.
    ///
    /// This is just a shortcut for [`LpExtractor::solve_multiple`].
    pub fn solve(&mut self, root: Id) -> RecExpr<L> {
        self.solve_multiple(&[root]).0
    }

    /// Extract a single rooted term with an explicit solver backend.
    pub fn solve_with<S: Solver>(&mut self, root: Id, solver: S) -> RecExpr<L> {
        self.solve_multiple_with(&[root], solver).0
    }

    /// Extract (potentially multiple) roots
    pub fn solve_multiple(&mut self, roots: &[Id]) -> (RecExpr<L>, Vec<Id>) {
        self.solve_multiple_with(roots, default_solver)
    }

    /// Like [`solve_multiple`], but lets the caller provide a `good_lp` solver backend.
    /// Example: `solve_multiple_with(roots, good_lp::highs)`.
    pub fn solve_multiple_with<S: Solver>(
        &mut self,
        roots: &[Id],
        solver: S,
    ) -> (RecExpr<L>, Vec<Id>) {
        let egraph = self.egraph;
        let mut num_vars: usize = 0;
        let mut num_cons: usize = 0;

        // Build variables per class
        let mut builder = variables!();
        let vars: HashMap<Id, ClassVars> = egraph
            .classes()
            .map(|class| {
                num_vars += 1;
                let active = builder.add(variable().binary());
                let nodes = class
                    .nodes
                    .iter()
                    .enumerate()
                    .map(|(i, _)| {
                        num_vars += 1;
                        if self.cyclic_nodes.contains(&(class.id, i)) {
                            // Force to 0 for cyclic nodes
                            builder.add(variable().binary().max(0).min(0))
                        } else {
                            builder.add(variable().binary())
                        }
                    })
                    .collect();
                (class.id, ClassVars { active, nodes })
            })
            .collect();

        // Objective: minimize sum(cost[node] * node_active)
        let mut objective: Expression = 0.0.into();
        for class in egraph.classes() {
            for (i, &node_var) in vars[&class.id].nodes.iter().enumerate() {
                let c = self.costs[&class.id][i];
                objective = objective + c * node_var;
            }
        }

        // Build model using the provided solver
        let mut model = builder.minimise(objective).using(solver);

        // Constraints:
        // - Exactly one chosen node per active class: sum(nodes) == active
        for (&id, class) in &vars {
            let sum_nodes: Expression = class
                .nodes
                .iter()
                .copied()
                .fold(0.0.into(), |acc, v| acc + v);
            num_cons += 1;
            model.add_constraint((sum_nodes - class.active).eq(0));

            // For each chosen node, all children classes must be active: node_active <= child_active
            for (i, node) in egraph[id].iter().enumerate() {
                let node_active = class.nodes[i];
                if self.cyclic_nodes.contains(&(id, i)) {
                    // Already fixed to 0 via bounds
                    continue;
                }
                for child in node.children() {
                    let child_active = vars[child].active;
                    num_cons += 1;
                    model.add_constraint((node_active - child_active).leq(0));
                }
            }
        }

        // Ensure specified roots are active
        for root in roots {
            let root = &egraph.find(*root);
            num_cons += 1;
            model.add_constraint(Expression::from(vars[root].active).geq(1));
        }

        log::info!("Model using {num_vars} variables and {num_cons} constraints");
        log::info!("Solving using {}", <S as Solver>::name(),);
        let start = Instant::now();
        let solution = model
            .solve()
            .expect("good_lp failed to solve the ILP problem");
        let duration = start.elapsed().as_secs_f64();
        log::info!("Solution found in {:.2}s", duration);
        match solution.status() {
            SolutionStatus::Optimal => {
                log::info!("Solution is optimal");
            }
            SolutionStatus::TimeLimit => {
                log::warn!("Solver timed out, solution may not be optimal.");
            }
            SolutionStatus::GapLimit => {
                log::info!("Solver reached gap limit, solution may not be optimal.");
            }
        };

        let mut todo: Vec<Id> = roots.iter().map(|id| self.egraph.find(*id)).collect();
        let mut expr = RecExpr::default();
        // converts e-class ids to e-node ids
        let mut ids: HashMap<Id, Id> = HashMap::default();

        while let Some(&id) = todo.last() {
            if ids.contains_key(&id) {
                todo.pop();
                continue;
            }
            let v = &vars[&id];
            assert!(solution.value(v.active) > 0.0);
            let node_idx = v
                .nodes
                .iter()
                .position(|&n| solution.value(n) > 0.0)
                .unwrap();
            let node = &self.egraph[id].nodes[node_idx];
            if node.all(|child| ids.contains_key(&child)) {
                let new_id = expr.add(node.clone().map_children(|i| ids[&self.egraph.find(i)]));
                ids.insert(id, new_id);
                todo.pop();
            } else {
                todo.extend_from_slice(node.children())
            }
        }

        let root_idxs = roots
            .iter()
            .map(|id| self.egraph.find(*id))
            .map(|root| ids[&root])
            .collect();

        assert!(expr.is_dag(), "LpExtract found a cyclic term!: {:?}", expr);
        (expr, root_idxs)
    }
}

fn find_cycles<L, N>(egraph: &EGraph<L, N>, mut f: impl FnMut(Id, usize))
where
    L: Language,
    N: Analysis<L>,
{
    enum Color {
        White,
        Gray,
        Black,
    }
    type Enter = bool;

    let mut color: HashMap<Id, Color> = egraph.classes().map(|c| (c.id, Color::White)).collect();
    let mut stack: Vec<(Enter, Id)> = egraph.classes().map(|c| (true, c.id)).collect();

    while let Some((enter, id)) = stack.pop() {
        if enter {
            *color.get_mut(&id).unwrap() = Color::Gray;
            stack.push((false, id));
            for (i, node) in egraph[id].iter().enumerate() {
                for child in node.children() {
                    match &color[child] {
                        Color::White => stack.push((true, *child)),
                        Color::Gray => f(id, i),
                        Color::Black => (),
                    }
                }
            }
        } else {
            *color.get_mut(&id).unwrap() = Color::Black;
        }
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

        let mut ext = LpExtractor::new(&egraph, AstSize);
        let (exp, ids) = ext.solve_multiple(&[f, g]);
        println!("{:?}", exp);
        println!("{}", exp);
        assert_eq!(exp.len(), 4);
        assert_eq!(ids.len(), 2);
    }

    #[test]
    fn extract_root_mismatch() {
        let mut egraph = EGraph::<S, ()>::default();
        let a = egraph.add(S::leaf("a"));
        let b = egraph.add(S::leaf("b"));
        let plus1 = egraph.add(S::new("+", vec![a, b]));
        let plus2 = egraph.add(S::new("+", vec![b, a]));
        egraph.union(plus1, plus2);

        let mut ext = LpExtractor::new(&egraph, AstSize);
        let (exp, ids) = ext.solve_multiple(&[plus2]);
        println!("{:?}", exp);
        println!("{}", exp);
        assert_eq!(exp.len(), 3);
        assert_eq!(ids.len(), 1);
    }
}
