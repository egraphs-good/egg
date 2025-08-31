use crate::util::{HashMap, HashSet};
use crate::*;
use std::fmt::Debug;

/// A cost function to be used for DAG-based extraction.
pub trait DagCostFunction<L: Language> {
    /// The `Cost` type for DAG extraction. Must be comparable.
    type Cost: Ord + Debug + Clone;

    /// The total cost of a `DagExpr`.
    ///
    /// Typically, this is computed by summing the cost of each node.
    ///
    /// The `expr` is guaranteed to be a DAG and compact (shortlex-minimal).
    ///
    /// There is no specific order to the nodes. If the cost depends on
    /// ordering, the cost function is responsible for handling this by
    /// returning the minimum cost over all orderings.
    fn cost(&mut self, expr: &DagExpr<L>) -> Self::Cost;
}

/// A cost function that computes the total cost of a `DagExpr` by counting the number of nodes.
pub struct DagSize;

impl<L> DagCostFunction<L> for DagSize
where
    L: Language,
{
    type Cost = usize;

    fn cost(&mut self, expr: &DagExpr<L>) -> Self::Cost {
        expr.len()
    }
}

/// Candidate expression paired with its cost.
#[derive(Clone)]
struct Candidate<L: Language, C> {
    expr: DagExpr<L>,
    cost: C,
}

impl<L: Language, C: Ord> PartialEq for Candidate<L, C> {
    fn eq(&self, other: &Self) -> bool {
        self.cost == other.cost
    }
}

impl<L: Language, C: Ord> Eq for Candidate<L, C> {}

impl<L: Language, C: Ord> PartialOrd for Candidate<L, C> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<L: Language, C: Ord> Ord for Candidate<L, C> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.cost.cmp(&other.cost)
    }
}

/// Beam search extractor that approximately minimizes a [`CostFunction`] on the
/// resulting [`RecExpr`].
///
/// A [`BeamExtract`] keeps up to `beam` candidate DAGs for each e-class while it
/// explores combinations of child results. Larger beams consider more
/// alternatives and generally yield better results at the cost of additional
/// time and memory. In practice a small beam (around 5–10) is often sufficient,
/// and `beam = 1` degenerates to a greedy search.
///
/// The extractor is parameterized by a user-provided [`CostFunction`]. The
/// function assigns a cost to each candidate expression; candidates with lower
/// cost are preferred. Common choices include [`AstSize`] or other heuristics
/// tailored to the problem domain.
///
/// `BeamExtract` builds each candidate by appending nodes in a deterministic
/// order. It does **not** explore all possible node orderings in the resulting
/// [`RecExpr`]; if the cost depends on ordering, the provided cost function is
/// responsible for handling it.
pub struct BeamExtract<'a, CF, L: Language + Clone, N: Analysis<L>>
where
    CF: DagCostFunction<L>,
{
    egraph: &'a EGraph<L, N>,
    beam: usize,

    /// Memoized candidate expressions for each e-class.
    memo: HashMap<Id, Vec<Candidate<L, CF::Cost>>>,
    visiting: HashSet<Id>,
    cost_fn: CF,
}

impl<'a, CF, L, N> BeamExtract<'a, CF, L, N>
where
    CF: DagCostFunction<L>,
    L: Language + Clone,
    N: Analysis<L>,
{
    /// Create a new [`BeamExtract`] with the given beam width and cost
    /// function.
    pub fn new(egraph: &'a EGraph<L, N>, beam: usize, cost_fn: CF) -> Self {
        Self {
            egraph,
            beam: beam.max(1),
            memo: HashMap::default(),
            visiting: HashSet::default(),
            cost_fn,
        }
    }

    /// Extract a DAG rooted at `root`, approximately minimizing size.
    pub fn solve(&mut self, root: Id) -> DagExpr<L> {
        self.solve_multiple(&[root])
    }

    /// Extract (potentially) multiple roots.
    ///
    /// Returns a canonical [`DagExpr`] containing all extracted terms and their roots.
    pub fn solve_multiple(&mut self, roots: &[Id]) -> DagExpr<L> {
        self.extract_multiple(roots)
            .into_iter()
            .min()
            .expect("No solution found.")
            .expr
    }

    /// Returns a list of `DagExpr`s computing `roots`.
    ///
    /// Each `DagExpr` is a candidate expression for the corresponding root set.
    /// At most `beam` candidates are returned. The list is not globally sorted;
    /// we use an unstable selection to keep an arbitrary top-`beam` by cost.
    fn extract_multiple(&mut self, roots: &[Id]) -> Vec<Candidate<L, CF::Cost>> {
        let empty = DagExpr::new(Vec::new(), Vec::new());
        let mut partials: Vec<Candidate<L, CF::Cost>> = vec![Candidate {
            expr: empty.clone(),
            cost: self.cost_fn.cost(&empty),
        }];
        for &root in roots {
            // Compute/ensure memoized candidates first
            self.ensure_class(root);
            // Clone slice to a Vec to end the immutable borrow before costing
            let cands_vec: Vec<Candidate<L, CF::Cost>> = self.candidates_for(root).to_vec();
            if cands_vec.is_empty() {
                return vec![];
            }
            let mut new_partials: Vec<Candidate<L, CF::Cost>> = Vec::new();
            for part in &partials {
                // First compute merged expressions while only reading cands_vec
                let merged_exprs: Vec<DagExpr<L>> = cands_vec
                    .iter()
                    .map(|cand| part.expr.merge(&cand.expr))
                    .collect();
                // Then cost them after the borrow has ended
                for merged in merged_exprs {
                    let cost = self.cost_fn.cost(&merged);
                    new_partials.push(Candidate { expr: merged, cost });
                }
            }
            // Deduplicate by structural equality (nodes + roots), keeping the lowest-cost candidate.
            let mut map: HashMap<(Vec<L>, Vec<Id>), Candidate<L, CF::Cost>> = HashMap::default();
            for p in new_partials.into_iter() {
                let key = (p.expr.nodes.clone(), p.expr.roots.clone());
                match map.get(&key) {
                    Some(existing) if existing.cost <= p.cost => {}
                    _ => {
                        map.insert(key, p);
                    }
                }
            }
            let mut new_partials: Vec<Candidate<L, CF::Cost>> = map.into_values().collect();
            if new_partials.len() > self.beam {
                new_partials.select_nth_unstable(self.beam - 1);
                new_partials.truncate(self.beam);
            }
            partials = new_partials;
        }
        partials
    }

    /// Ensure candidates are computed and memoized for an e-class.
    fn ensure_class(&mut self, id: Id) {
        let id = self.egraph.find(id);
        if self.memo.contains_key(&id) {
            return;
        }
        if !self.visiting.insert(id) {
            // Cycle: memoize empty and return
            self.memo.entry(id).or_insert_with(Vec::new);
            return;
        }

        let mut all: Vec<Candidate<L, CF::Cost>> = Vec::new();
        for node in &self.egraph[id].nodes {
            let child_ids = node.children().to_vec();

            // Handle leaf node quickly
            if child_ids.is_empty() {
                let mut new_nodes = Vec::new();
                // leaf: just this node with no children; pushed alone
                new_nodes.push(node.clone());
                let new_root = Id::from(0usize);
                let dag = DagExpr::new(new_nodes, vec![new_root]);
                let cost = self.cost_fn.cost(&dag);
                all.push(Candidate { expr: dag, cost });
                continue;
            }

            // Ensure children candidates before borrowing them, then clone slices to end borrows
            let mut acc: Vec<Candidate<L, CF::Cost>> = {
                self.ensure_class(child_ids[0]);
                self.candidates_for(child_ids[0]).to_vec()
            };
            for &cid in &child_ids[1..] {
                self.ensure_class(cid);
                let next_vec: Vec<Candidate<L, CF::Cost>> = self.candidates_for(cid).to_vec();
                let mut merged_step: Vec<Candidate<L, CF::Cost>> = Vec::new();
                for a in &acc {
                    for b in &next_vec {
                        let merged = a.expr.merge(&b.expr);
                        // Defer costing to after all borrows are dropped
                        merged_step.push(Candidate {
                            expr: merged,
                            cost: self.cost_fn.cost(&DagExpr::default()), // placeholder, will be recomputed
                        });
                    }
                }
                acc = merged_step;
            }

            // Now append this node on top of each combined child DAG
            for child_cand in acc.into_iter().map(|mut c| {
                // Recompute cost correctly by rebuilding DAGs with this node
                let mut new_nodes = c.expr.nodes.clone();
                let mut new_node = node.clone();
                new_node.children_mut().copy_from_slice(&c.expr.roots);
                new_nodes.push(new_node);
                let new_root = Id::from(new_nodes.len() - 1);
                let dag = DagExpr::new(new_nodes, vec![new_root]);
                let cost = self.cost_fn.cost(&dag);
                Candidate { expr: dag, cost }
            }) {
                all.push(child_cand);
            }
        }
        self.visiting.remove(&id);

        // Deduplicate by canonical structural equality (nodes), keeping the lowest-cost candidate.
        // Note: After selection, ordering is not guaranteed to be sorted.
        let mut map: HashMap<Vec<L>, Candidate<L, CF::Cost>> = HashMap::default();
        for cand in all.into_iter() {
            let key = cand.expr.nodes.clone();
            match map.get(&key) {
                Some(existing) if existing.cost <= cand.cost => {}
                _ => {
                    map.insert(key, cand);
                }
            }
        }
        let mut all: Vec<Candidate<L, CF::Cost>> = map.into_values().collect();
        if all.len() > self.beam {
            all.select_nth_unstable(self.beam - 1);
            all.truncate(self.beam);
        }

        self.memo.insert(id, all);
    }

    /// Borrow the memoized candidates for an e-class as a slice.
    fn candidates_for(&self, id: Id) -> &[Candidate<L, CF::Cost>] {
        let id = self.egraph.find(id);
        self.memo.get(&id).map(|v| v.as_slice()).unwrap_or(&[])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn beam_extract_finds_small_dag() {
        let mut egraph = EGraph::<SymbolLang, ()>::default();
        let x = egraph.add(SymbolLang::leaf("x"));
        let f = egraph.add(SymbolLang::new("f", vec![x, x, x]));
        let gx = egraph.add(SymbolLang::new("g", vec![x]));
        let ggx = egraph.add(SymbolLang::new("g", vec![gx]));
        egraph.union(f, ggx);
        egraph.rebuild();

        let best_tree = Extractor::new(&egraph, AstSize).find_best(f).1;
        assert_eq!(best_tree.to_string(), "(g (g x))");

        let mut beamer = BeamExtract::new(&egraph, 5, DagSize);
        let dag = beamer.solve(f);
        let rec = dag.extract_root(dag.roots[0]);
        assert_eq!(rec.to_string(), "(f x x x)");
        assert_eq!(dag.len(), 2);
    }

    #[test]
    fn beam_extract_solve_multiple() {
        let mut egraph = EGraph::<SymbolLang, ()>::default();
        let x = egraph.add(SymbolLang::leaf("x"));
        let f = egraph.add(SymbolLang::new("f", vec![x, x]));
        let gx = egraph.add(SymbolLang::new("g", vec![x]));
        let h = egraph.add(SymbolLang::new("h", vec![gx, gx]));
        egraph.rebuild();

        let mut beamer = BeamExtract::new(&egraph, 5, DagSize);
        let dag = beamer.solve_multiple(&[f, h]);
        assert_eq!(dag.roots.len(), 2);

        let f_expr = dag.extract_root(dag.roots[0]);
        let h_expr = dag.extract_root(dag.roots[1]);
        assert_eq!(f_expr.to_string(), "(f x x)");
        assert_eq!(h_expr.to_string(), "(h (g x) (g x))");
        assert_eq!(dag.len(), 4);
    }
}
