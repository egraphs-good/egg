use good_lp::{
    Expression, Solution, SolutionStatus, Solver, SolverModel, Variable, default_solver,
    solvers::WithTimeLimit, variable, variables,
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
    /// Costs should be finite and nonnegative. Negative costs can cause the
    /// model to select classes unreachable from the roots, so its objective
    /// need not equal the cost of the returned expression.
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
/// The model chooses one e-node per active e-class and requires the chosen
/// edges to be acyclic. Alternatives are preserved even when the full e-graph
/// contains cycles. Only strongly connected components of the possible-edge
/// graph need additional rank constraints; acyclic components incur no rank
/// variables. Solving this exact selection problem can be expensive.
///
/// With finite nonnegative node costs and an optimal solver result, the model
/// minimizes the sum of costs over the selected DAG, counting each e-class
/// once. This is a class-consistent selection: different occurrences of an
/// e-class cannot choose different e-nodes. Time-limited solutions may be
/// suboptimal; numerical feasibility and optimality depend on the backend.
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
/// See the [`good_lp` documentation](https://docs.rs/good_lp/1/good_lp/solvers/index.html)
///
/// At run time, select the solver by calling [`Self::solve_with`], [`Self::solve_multiple_with`], [`Self::solve_with_timeout`], or [`Self::solve_multiple_with_timeout`]
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
///   ```
///
#[cfg_attr(docsrs, doc(cfg(feature = "lp")))]
pub struct LpExtractor<'a, L: Language, N: Analysis<L>> {
    egraph: &'a EGraph<L, N>,
    // Precomputed per-node costs to avoid storing the cost function
    costs: HashMap<Id, Vec<f64>>, // for each class id, cost per node index
    // Full possible-edge SCCs; cycles can only occur inside one component.
    components: HashMap<Id, (Id, usize)>,
}

struct ClassVars {
    active: Variable,
    rank: Option<Variable>,
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
        // Precompute costs per node.
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
            components: strongly_connected_components(egraph),
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

    /// Extract a single rooted term with an explicit solver backend and time limit.
    ///
    /// The returned term may be suboptimal. Panics if the backend fails to
    /// provide a decodable acyclic selection.
    pub fn solve_with_timeout<S: Solver>(&mut self, root: Id, solver: S, timeout: f64) -> RecExpr<L>
    where
        <S as Solver>::Model: WithTimeLimit,
    {
        self.solve_multiple_with_timeout(&[root], solver, timeout).0
    }

    /// Extract (potentially multiple) roots
    pub fn solve_multiple(&mut self, roots: &[Id]) -> (RecExpr<L>, Vec<Id>) {
        self.solve_multiple_with(roots, default_solver)
    }

    /// Builds the ILP model with variables and objective function.
    /// Returns the model builder (before timeout) and the variables map.
    fn build_ilp_model<S: Solver>(&mut self, solver: S) -> (S::Model, HashMap<Id, ClassVars>) {
        let egraph = self.egraph;
        let mut num_vars: usize = 0;

        // Build variables per class
        let mut builder = variables!();
        let vars: HashMap<Id, ClassVars> = egraph
            .classes()
            .map(|class| {
                num_vars += 1;
                let active = builder.add(variable().binary());
                let size = self.components[&class.id].1;
                let rank = if size > 1 {
                    num_vars += 1;
                    Some(builder.add(variable().min(0).max((size - 1) as f64)))
                } else {
                    None
                };
                let nodes = class
                    .nodes
                    .iter()
                    .map(|node| {
                        num_vars += 1;
                        // A direct self-loop cannot belong to an acyclic
                        // selection, regardless of the other node choices.
                        let bounds = if node.children().contains(&class.id) {
                            variable().binary().max(0)
                        } else {
                            variable().binary()
                        };
                        builder.add(bounds)
                    })
                    .collect();
                (
                    class.id,
                    ClassVars {
                        active,
                        rank,
                        nodes,
                    },
                )
            })
            .collect();

        // Objective: minimize sum(cost[node] * node_active)
        let mut objective: Expression = 0.0.into();
        for class in egraph.classes() {
            for (i, &node_var) in vars[&class.id].nodes.iter().enumerate() {
                let c = self.costs[&class.id][i];
                objective += c * node_var;
            }
        }

        // Build model using the provided solver
        let model = builder.minimise(objective).using(solver);

        log::info!("Model using {num_vars} variables");
        (model, vars)
    }

    /// Adds all constraints to the model.
    fn add_constraints<S: Solver>(
        &self,
        model: &mut S::Model,
        vars: &HashMap<Id, ClassVars>,
        roots: &[Id],
    ) {
        let egraph = self.egraph;
        let mut num_cons: usize = 0;

        // Constraints:
        // - Exactly one chosen node per active class: sum(nodes) == active
        for (&id, class) in vars {
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
                for child in node.children() {
                    let child_active = vars[child].active;
                    num_cons += 1;
                    model.add_constraint((node_active - child_active).leq(0));

                    // Cycles stay within an SCC of the full possible-edge
                    // graph. Cross-component edges need no rank constraint.
                    if let Some(rank) = class.rank {
                        let (component, size) = self.components[&id];
                        if component == self.components[child].0 {
                            // Every DAG on n classes has ranks in [0, n - 1].
                            // For an unselected edge, M = n makes this row
                            // vacuous at even the extreme ranks. Here n is the
                            // component size, preserving every acyclic choice.
                            let child_rank = vars[child].rank.unwrap();
                            let n = size as f64;
                            num_cons += 1;
                            model
                                .add_constraint((rank - child_rank - n * node_active).geq(1.0 - n));
                        }
                    }
                }
            }
        }

        // Ensure specified roots are active
        for root in roots {
            let root = &egraph.find(*root);
            num_cons += 1;
            model.add_constraint(Expression::from(vars[root].active).geq(1));
        }

        log::info!("Model using {num_cons} constraints");
    }

    /// Extracts the solution from the solved model.
    fn extract_solution(
        &self,
        solution: impl Solution,
        vars: &HashMap<Id, ClassVars>,
        roots: &[Id],
    ) -> (RecExpr<L>, Vec<Id>) {
        // The bool records whether a class's children have been visited.
        let mut todo: Vec<(Id, bool)> = roots
            .iter()
            .map(|id| (self.egraph.find(*id), false))
            .collect();
        let mut expr = RecExpr::default();
        // converts e-class ids to e-node ids
        let mut ids: HashMap<Id, Id> = HashMap::default();
        let mut visiting = HashSet::default();

        while let Some((id, children_visited)) = todo.pop() {
            if ids.contains_key(&id) {
                continue;
            }
            let v = &vars[&id];
            assert!(
                solution.value(v.active) > 0.5,
                "LpExtract found an inactive root or child"
            );
            let node_idx = v
                .nodes
                .iter()
                .position(|&n| solution.value(n) > 0.5)
                .expect("LpExtract found an active class without a selected node");
            let node = &self.egraph[id].nodes[node_idx];
            if children_visited {
                let new_id = expr.add(node.clone().map_children(|i| ids[&self.egraph.find(i)]));
                ids.insert(id, new_id);
                #[cfg(feature = "deterministic")]
                visiting.swap_remove(&id);
                #[cfg(not(feature = "deterministic"))]
                visiting.remove(&id);
            } else {
                // A feasible integer solution satisfies the rank constraints.
                // Check this while decoding as well, so a solver's numerical
                // tolerances cannot turn a selected cycle into an infinite loop.
                assert!(visiting.insert(id), "LpExtract found a cyclic selection");
                todo.push((id, true));
                todo.extend(node.children().iter().map(|child| (*child, false)));
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

    /// Like [`LpExtractor::solve_multiple`], but lets the caller provide a `good_lp` solver backend.
    /// Example: `solve_multiple_with(roots, good_lp::highs)`.
    pub fn solve_multiple_with<S: Solver>(
        &mut self,
        roots: &[Id],
        solver: S,
    ) -> (RecExpr<L>, Vec<Id>) {
        let (mut model, vars) = self.build_ilp_model(solver);
        self.add_constraints::<S>(&mut model, &vars, roots);

        log::info!("Solving using {}", <S as Solver>::name());
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

        self.extract_solution(solution, &vars, roots)
    }

    /// Like [`LpExtractor::solve_multiple_with`], but lets the caller provide a time limit for the 'good_lp' solver in seconds.
    /// Example: `solve_multiple_with_timeout(roots, good_lp::highs, 600.0)`.
    ///
    /// The returned terms may be suboptimal. Panics if the backend fails to
    /// provide a decodable acyclic selection.
    pub fn solve_multiple_with_timeout<S: Solver>(
        &mut self,
        roots: &[Id],
        solver: S,
        timeout: f64,
    ) -> (RecExpr<L>, Vec<Id>)
    where
        <S as Solver>::Model: WithTimeLimit,
    {
        let (model_build, vars) = self.build_ilp_model(solver);

        // Set timeout
        let mut model = model_build.with_time_limit(timeout);

        self.add_constraints::<S>(&mut model, &vars, roots);

        log::info!("Solving using {}", <S as Solver>::name());
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

        self.extract_solution(solution, &vars, roots)
    }
}

// Kosaraju's algorithm over all possible e-node edges. Unlike cycle breaking,
// this partition does not discard alternatives. Both passes use explicit
// stacks so deeply nested e-graphs do not overflow the call stack.
fn strongly_connected_components<L, N>(egraph: &EGraph<L, N>) -> HashMap<Id, (Id, usize)>
where
    L: Language,
    N: Analysis<L>,
{
    let mut reverse: HashMap<Id, Vec<Id>> = egraph
        .classes()
        .map(|class| (class.id, Vec::new()))
        .collect();
    for class in egraph.classes() {
        for node in &class.nodes {
            for child in node.children() {
                reverse.get_mut(child).unwrap().push(class.id);
            }
        }
    }

    let mut visited = HashSet::default();
    let mut finished = Vec::with_capacity(reverse.len());
    let mut stack = Vec::new();
    for class in egraph.classes() {
        stack.push((class.id, false));
        while let Some((id, exiting)) = stack.pop() {
            if exiting {
                finished.push(id);
            } else if visited.insert(id) {
                stack.push((id, true));
                for node in &egraph[id].nodes {
                    stack.extend(node.children().iter().map(|&child| (child, false)));
                }
            }
        }
    }

    visited.clear();
    let mut components = HashMap::default();
    let mut members = Vec::new();
    let mut todo = Vec::new();
    while let Some(root) = finished.pop() {
        if visited.contains(&root) {
            continue;
        }
        todo.push(root);
        while let Some(id) = todo.pop() {
            if visited.insert(id) {
                members.push(id);
                todo.extend_from_slice(&reverse[&id]);
            }
        }
        let size = members.len();
        for id in members.drain(..) {
            components.insert(id, (root, size));
        }
    }
    components
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;
    use crate::SymbolLang as S;

    fn assert_scc_partition(egraph: &EGraph<S, ()>, vertices: &[Id], edges: &[Vec<bool>]) {
        let n = vertices.len();
        let vertices: Vec<_> = vertices.iter().map(|&id| egraph.find(id)).collect();
        assert!(egraph.clean);
        assert_eq!(egraph.number_of_classes(), n);
        assert_eq!(vertices.iter().copied().collect::<HashSet<_>>().len(), n);

        // Check the actual rebuilt input, rather than trusting the generator:
        // hashconsing or congruence must not collapse the intended vertices.
        let mut actual_edges = vec![vec![false; n]; n];
        for (source, &id) in vertices.iter().enumerate() {
            assert_eq!(egraph[id].id, id);
            for node in &egraph[id].nodes {
                for &child in node.children() {
                    assert_eq!(egraph.find(child), child);
                    let target = vertices.iter().position(|&id| id == child).unwrap();
                    actual_edges[source][target] = true;
                }
            }
        }
        assert_eq!(actual_edges, edges);

        // An independent Floyd-Warshall oracle, with zero-length paths. It
        // shares neither DFS order nor reverse-edge construction with Kosaraju.
        let mut reachable = edges.to_vec();
        for (i, row) in reachable.iter_mut().enumerate() {
            row[i] = true;
        }
        for middle in 0..n {
            for source in 0..n {
                for target in 0..n {
                    reachable[source][target] |=
                        reachable[source][middle] && reachable[middle][target];
                }
            }
        }

        let components = strongly_connected_components(egraph);
        assert_eq!(components.len(), n);
        for (source, &id) in vertices.iter().enumerate() {
            let (representative, size) = components[&id];
            let representative_index = vertices
                .iter()
                .position(|&id| id == representative)
                .unwrap();
            assert!(reachable[source][representative_index]);
            assert!(reachable[representative_index][source]);
            assert_eq!(components[&representative], (representative, size));
            assert_eq!(
                size,
                (0..n)
                    .filter(|&target| reachable[source][target] && reachable[target][source])
                    .count()
            );
            for (target, &other) in vertices.iter().enumerate() {
                assert_eq!(
                    representative == components[&other].0,
                    reachable[source][target] && reachable[target][source],
                    "incorrect partition for vertices {source}, {target}, edges {edges:?}"
                );
            }
        }
    }

    #[test]
    fn scc_partition_matches_all_three_vertex_graphs() {
        // All 2^(3 * 3) directed graphs, including every self-loop choice.
        for mask in 0..1usize << 9 {
            let mut egraph = EGraph::default();
            let vertices: Vec<_> = (0..3)
                .map(|i| egraph.add(S::leaf(format!("vertex_{i}"))))
                .collect();
            let mut edges = vec![vec![false; 3]; 3];
            for source in 0..3 {
                for target in 0..3 {
                    if mask & (1 << (3 * source + target)) != 0 {
                        edges[source][target] = true;
                        let node = egraph.add(S::new(
                            format!("edge_{source}_{target}"),
                            vec![vertices[target]],
                        ));
                        egraph.union(vertices[source], node);
                    }
                }
            }
            egraph.rebuild();
            assert_scc_partition(&egraph, &vertices, &edges);
        }
    }

    #[test]
    fn scc_partition_handles_duplicate_edges_and_rebuilt_aliases() {
        // Two nontrivial SCCs point into a singleton with a self-loop. Each
        // edge occurs across distinct e-nodes and as repeated child positions.
        let edges = vec![
            vec![false, true, false, false, false],
            vec![true, false, true, false, false],
            vec![false, false, true, false, false],
            vec![false, false, true, false, true],
            vec![false, false, false, true, false],
        ];
        let mut egraph = EGraph::default();
        let vertices: Vec<_> = (0..edges.len())
            .map(|i| egraph.add(S::leaf(format!("vertex_{i}"))))
            .collect();
        let aliases: Vec<_> = (0..edges.len())
            .map(|i| egraph.add(S::leaf(format!("alias_{i}"))))
            .collect();
        for (source, row) in edges.iter().enumerate() {
            for (target, &present) in row.iter().enumerate() {
                if present {
                    let repeated = S::new(
                        format!("repeated_{source}_{target}"),
                        vec![vertices[target], aliases[target], aliases[target]],
                    );
                    let node = egraph.add(repeated.clone());
                    assert_eq!(egraph.add(repeated), node);
                    egraph.union(vertices[source], node);
                    let parallel = egraph.add(S::new(
                        format!("parallel_{source}_{target}"),
                        vec![vertices[target]],
                    ));
                    egraph.union(vertices[source], parallel);
                }
            }
        }
        for (&vertex, &alias) in vertices.iter().zip(&aliases) {
            egraph.union(vertex, alias);
        }
        assert!(egraph.classes().any(|class| {
            class
                .nodes
                .iter()
                .any(|node| node.children().iter().any(|&id| egraph.find(id) != id))
        }));
        egraph.rebuild();
        assert_scc_partition(&egraph, &vertices, &edges);
        assert_scc_partition(&egraph, &aliases, &edges);

        let components = strongly_connected_components(&egraph);
        for &id in vertices.iter().chain(&aliases) {
            if egraph.find(id) != id {
                assert!(!components.contains_key(&id));
            }
        }
        for (&vertex, row) in vertices.iter().zip(&edges) {
            assert_eq!(
                egraph[vertex]
                    .nodes
                    .iter()
                    .map(|node| node.children().len())
                    .sum::<usize>(),
                4 * row.iter().filter(|&&present| present).count()
            );
            for node in &egraph[vertex].nodes {
                if node.children().len() == 3 {
                    assert_eq!(node.children()[0], node.children()[1]);
                    assert_eq!(node.children()[1], node.children()[2]);
                }
            }
        }
    }

    #[test]
    fn scc_partition_of_an_empty_egraph_is_empty() {
        let mut egraph = EGraph::<S, ()>::default();
        egraph.rebuild();
        assert_scc_partition(&egraph, &[], &[]);
    }

    #[test]
    fn scc_deep_cycle_uses_both_iterative_passes() {
        // A single cycle forces both DFS passes to visit the full depth,
        // regardless of class iteration order. Keep leaves and edge operators
        // unique so rebuilding cannot shrink it through congruence.
        const N: usize = 20_000;
        let mut egraph = EGraph::<S, ()>::default();
        let vertices: Vec<_> = (0..N)
            .map(|i| egraph.add(S::leaf(format!("deep_vertex_{i}"))))
            .collect();
        for source in 0..N {
            let edge = egraph.add(S::new(
                format!("deep_edge_{source}"),
                vec![vertices[(source + 1) % N]],
            ));
            egraph.union(vertices[source], edge);
        }
        egraph.rebuild();
        assert_eq!(egraph.number_of_classes(), N);
        for source in 0..N {
            let children: Vec<_> = egraph[vertices[source]]
                .nodes
                .iter()
                .flat_map(|node| node.children().iter().copied())
                .collect();
            assert_eq!(children, vec![egraph.find(vertices[(source + 1) % N])]);
        }

        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(move || {
                let components = strongly_connected_components(&egraph);
                assert_eq!(components.len(), N);
                let representative = components[&egraph.find(vertices[0])].0;
                assert_eq!(components[&representative], (representative, N));
                for class in egraph.classes() {
                    assert_eq!(components[&class.id], (representative, N));
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    struct TestSolution {
        values: HashMap<Variable, f64>,
        status: SolutionStatus,
    }

    impl Solution for TestSolution {
        fn status(&self) -> SolutionStatus {
            self.status
        }

        fn value(&self, variable: Variable) -> f64 {
            self.values.get(&variable).copied().unwrap_or(0.0)
        }
    }

    fn cyclic_egraph() -> (EGraph<S, ()>, Id) {
        let mut egraph = EGraph::default();
        let a = egraph.add(S::leaf("a"));
        let loop_node = egraph.add(S::new("loop", vec![a]));
        egraph.union(a, loop_node);
        egraph.rebuild();
        let root = egraph.find(a);
        (egraph, root)
    }

    #[test]
    fn decoder_ignores_small_binary_residue() {
        let (egraph, root) = cyclic_egraph();
        let mut extractor = LpExtractor::new(&egraph, AstSize);
        let (_, vars) = extractor.build_ilp_model(good_lp::coin_cbc);
        let mut values = HashMap::default();
        values.insert(vars[&root].active, 1.0);
        for (node, &variable) in egraph[root].iter().zip(&vars[&root].nodes) {
            values.insert(variable, if node.is_leaf() { 1.0 } else { 1e-12 });
        }
        let solution = TestSolution {
            values,
            status: SolutionStatus::Optimal,
        };
        let (expression, roots) = extractor.extract_solution(solution, &vars, &[root]);
        assert_eq!(expression.to_string(), "a");
        assert_eq!(roots, vec![Id::from(0)]);
    }

    #[test]
    #[should_panic(expected = "LpExtract found a cyclic selection")]
    fn decoder_rejects_a_cyclic_incumbent() {
        let (egraph, root) = cyclic_egraph();
        let mut extractor = LpExtractor::new(&egraph, AstSize);
        let (_, vars) = extractor.build_ilp_model(good_lp::coin_cbc);
        let mut values = HashMap::default();
        values.insert(vars[&root].active, 1.0);
        for (node, &variable) in egraph[root].iter().zip(&vars[&root].nodes) {
            values.insert(variable, if node.is_leaf() { 0.0 } else { 1.0 });
        }
        let solution = TestSolution {
            values,
            status: SolutionStatus::TimeLimit,
        };
        extractor.extract_solution(solution, &vars, &[root]);
    }

    #[test]
    #[should_panic(expected = "LpExtract found an active class without a selected node")]
    fn decoder_rejects_missing_integer_incumbent() {
        let (egraph, root) = cyclic_egraph();
        let mut extractor = LpExtractor::new(&egraph, AstSize);
        let (_, vars) = extractor.build_ilp_model(good_lp::coin_cbc);
        let mut values = HashMap::default();
        values.insert(vars[&root].active, 1.0);
        let solution = TestSolution {
            values,
            status: SolutionStatus::TimeLimit,
        };
        extractor.extract_solution(solution, &vars, &[root]);
    }

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
    fn simple_lp_extract_two_timeout() {
        let mut egraph = EGraph::<S, ()>::default();
        let a = egraph.add(S::leaf("a"));
        let plus = egraph.add(S::new("+", vec![a, a]));
        let f = egraph.add(S::new("f", vec![plus]));
        let g = egraph.add(S::new("g", vec![plus]));

        let mut ext = LpExtractor::new(&egraph, AstSize);
        let (exp, ids) = ext.solve_multiple_with_timeout(&[f, g], good_lp::coin_cbc, 10.0);
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
