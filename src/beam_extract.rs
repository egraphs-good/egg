use crate::util::{HashMap, HashSet};
use crate::*;
use std::fmt::Debug;

/// A cost function to be used for DAG-based extraction.
pub trait DagCostFunction<L: Language> {
    /// The `Cost` type for DAG extraction. Must be comparable.
    type Cost: Ord + Debug + Clone;

    /// The total cost of a `RecExpr`.
    ///
    /// Typically, this is computed by summing the cost of each node.
    ///
    /// The `expr` is guaranteed to be a DAG and compact.
    ///
    /// There is no specific order to the nodes. If the cost depends on
    /// ordering, the cost function is responsible for handling this by
    /// returning the minimum cost over all orderings.
    fn cost(&mut self, expr: &RecExpr<L>) -> Self::Cost;
}

/// A cost function that computes the total cost of a `RecExpr` by counting the number of nodes.
pub struct DagSize;

impl<L> DagCostFunction<L> for DagSize
where
    L: Language,
{
    type Cost = usize;

    fn cost(&mut self, expr: &RecExpr<L>) -> Self::Cost {
        expr.len()
    }
}

/// Candidate expression paired with its cost.
#[derive(Clone)]
struct Candidate<L: Language, C> {
    expr: RecExpr<L>,
    cost: C,
}

/// Internal builder state used during beam merging.
struct Partial<L: Language, C> {
    expr: RecExpr<L>,
    roots: Vec<Id>,
    cost: C,
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
    pub fn solve(&mut self, root: Id) -> RecExpr<L> {
        self.solve_multiple(&[root]).0
    }

    /// Extract (potentially) multiple roots.
    ///
    /// Returns a [`RecExpr`] containing all extracted terms and the
    /// corresponding root ids within that [`RecExpr`].
    pub fn solve_multiple(&mut self, roots: &[Id]) -> (RecExpr<L>, Vec<Id>) {
        let candidates = self.extract_multiple(roots);
        let best = candidates.into_iter().next().expect("No solution found.");
        (best.expr, best.roots)
    }

    /// Returns a list of `RecExpr`s computing `roots`.
    ///
    /// Each `RecExpr` is a candidate expression for the corresponding root.
    /// The list is sorted by increasing cost. At most `beam` candidates are returned.
    fn extract_multiple(&mut self, roots: &[Id]) -> Vec<Partial<L, CF::Cost>> {
        let mut partials: Vec<Partial<L, CF::Cost>> = vec![Partial {
            expr: RecExpr::default(),
            roots: vec![],
            cost: self.cost_fn.cost(&RecExpr::default()),
        }];
        for &root in roots {
            let cands = self.extract_class(root);
            if cands.is_empty() {
                return vec![];
            }
            let mut new_partials: Vec<Partial<L, CF::Cost>> = Vec::new();
            for part in &partials {
                for cand in &cands {
                    let mut expr = part.expr.clone();
                    let mut roots = part.roots.clone();
                    let root = expr.append_compact(&cand.expr);
                    roots.push(root);
                    // Compact (prune + dedup) and canonicalize while remapping all roots
                    let mut roots_ref = roots.clone();
                    let canon = expr.clone().minimize_with_roots(&mut roots_ref);
                    let cost = self.cost_fn.cost(&canon);
                    new_partials.push(Partial {
                        expr: canon,
                        roots: roots_ref,
                        cost,
                    });
                }
            }
            // Deduplicate by structural equality (expr + roots), keeping the lowest-cost candidate.
            let mut map: HashMap<(Vec<L>, Vec<Id>), Partial<L, CF::Cost>> = HashMap::default();
            for p in new_partials.into_iter() {
                let key = (p.expr.as_ref().to_vec(), p.roots.clone());
                match map.get(&key) {
                    Some(existing) if existing.cost <= p.cost => {}
                    _ => {
                        map.insert(key, p);
                    }
                }
            }
            let mut new_partials: Vec<Partial<L, CF::Cost>> = map.into_values().collect();
            new_partials.sort_by(|a, b| a.cost.cmp(&b.cost));
            new_partials.truncate(self.beam);
            partials = new_partials;
        }
        partials
    }

    /// Recursively collect candidate expressions for an e-class.
    fn extract_class(&mut self, id: Id) -> Vec<Candidate<L, CF::Cost>> {
        let id = self.egraph.find(id);
        if let Some(v) = self.memo.get(&id) {
            return v.clone();
        }
        if !self.visiting.insert(id) {
            return vec![]; // cycle
        }
        let mut all: Vec<Candidate<L, CF::Cost>> = Vec::new();
        for node in &self.egraph[id].nodes {
            let candidates = self.extract_multiple(node.children());
            for candidate in candidates {
                let mut expr = candidate.expr;
                let mut node = node.clone();
                node.children_mut().copy_from_slice(&candidate.roots);
                let root = expr.find_or_add(node);
                if root != expr.root() {
                    // Ensure the root is at the end.
                    expr = expr.extract(root);
                    // Q: Can this ever happen? If it does, can we discard this candidate?
                }
                // Compact (prune + dedup) and canonicalize expression so structurally identical DAGs compare equal
                let expr = expr.minimize();
                let cost = self.cost_fn.cost(&expr);
                all.push(Candidate { expr, cost });
            }
        }
        self.visiting.remove(&id);

        // Deduplicate by canonical structural equality (expr), keeping the lowest-cost candidate.
        let mut map: HashMap<Vec<L>, Candidate<L, CF::Cost>> = HashMap::default();
        for cand in all.into_iter() {
            let key = cand.expr.as_ref().to_vec();
            match map.get(&key) {
                Some(existing) if existing.cost <= cand.cost => {}
                _ => {
                    map.insert(key, cand);
                }
            }
        }
        let mut all: Vec<Candidate<L, CF::Cost>> = map.into_values().collect();
        all.sort_by(|a, b| a.cost.cmp(&b.cost));
        all.truncate(self.beam);

        self.memo.insert(id, all.clone());
        all
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
        assert_eq!(dag.to_string(), "(f x x x)");
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
        let (dag, roots) = beamer.solve_multiple(&[f, h]);
        assert_eq!(roots.len(), 2);

        let f_expr = dag[roots[0]].build_recexpr(|id| dag[id].clone());
        let h_expr = dag[roots[1]].build_recexpr(|id| dag[id].clone());
        assert_eq!(f_expr.to_string(), "(f x x)");
        assert_eq!(h_expr.to_string(), "(h (g x) (g x))");
        assert_eq!(dag.len(), 4);
    }
}
