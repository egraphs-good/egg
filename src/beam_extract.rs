use crate::util::{HashMap, HashSet};
use crate::*;
use std::cmp::Ordering;
use std::fmt::Debug;

/// A cost function to be used for DAG-based extraction.
pub trait DagCostFunction<L: Language> {
    /// The `Cost` type for DAG extraction. Must be comparable.
    type Cost: Ord + Debug + Clone;

    /// Compute the total cost of a [`DagExpr`].
    ///
    /// Typically this is computed by summing the cost of each node.
    ///
    /// The [`DagExpr`] is in the unique lexicographic minimal ordering
    /// for the DAG.
    ///
    /// If the cost depends on the specific topological ordering, the cost
    /// function is responsible for handling this by returning the minimum
    /// cost over all topological orderings.
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
#[derive(Clone, PartialEq, Eq, Debug)]
struct Candidate<L: Language, C: Ord> {
    expr: DagExpr<L>,
    cost: C,
}

impl<L: Language, C: Ord> PartialOrd for Candidate<L, C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<L: Language, C: Ord> Ord for Candidate<L, C> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.cost.cmp(&other.cost) {
            Ordering::Equal => self.expr.cmp(&other.expr),
            ord => ord,
        }
    }
}

/// A simple data structure to keep the top-k unique elements seen so far.
struct TopK<T: Ord> {
    k: usize,
    data: Vec<T>,
}

impl<T: Ord> TopK<T> {
    fn new(k: usize) -> Self {
        Self {
            k,
            data: Vec::with_capacity(k),
        }
    }

    fn push(&mut self, item: T) {
        match self.data.binary_search(&item) {
            Ok(_) => {} // Duplicate
            Err(index) if index < self.k => {
                if self.data.len() == self.k {
                    self.data.pop();
                }
                self.data.insert(index, item);
            }
            Err(_) => {} // Too large
        }
    }

    /// Consume and return the top-k elements as a sorted `Vec`.
    fn into_inner(self) -> Vec<T> {
        self.data
    }
}

/// Beam search extractor that approximately minimizes a [`DagCostFunction`] on the
/// resulting [`DagExpr`].
///
/// A [`BeamExtract`] keeps up to `beam` candidate DAGs for each e-class while it
/// explores combinations of child results. Larger beams consider more
/// alternatives and generally yield better results at the cost of additional
/// time and memory. In practice a small beam (around 5–10) is often sufficient,
/// and `beam = 1` degenerates to a greedy search.
///
/// The extractor is parameterized by a user-provided [`DagCostFunction`]. The
/// function assigns a cost to each candidate expression; candidates with lower
/// cost are preferred. Common choices include [`DagSize`] or other heuristics
/// tailored to the problem domain.
///
/// `BeamExtract` builds each candidate by appending nodes in a deterministic
/// order. It does **not** explore all possible node orderings in the resulting
/// [`DagExpr`]; if the cost depends on ordering, the provided cost function is
/// responsible for handling it by retuning the minimum over all orderings.
///
/// **Note**: `BeamExtract` requires that the language `L` has an ordering that
/// is preserved under a map that transforms each nodes child [`Id`]s by a
/// monotonicaly increasing function. This is true for `SymbolLang`, languages
/// defined using [`define_language!`] and most other languages.
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
            .next()
            .expect("No solution found.")
            .expr
    }

    /// Returns a list of [`DagExpr`]s computing `roots`.
    ///
    /// Each [`DagExpr`] is a candidate expression for the corresponding root set.
    /// At most `beam` candidates are returned. The list is sorted by increasing cost.
    ///
    /// Returns an empty list if no candidates could be constructed (e.g., due to cycles).
    fn extract_multiple(&mut self, roots: &[Id]) -> Vec<Candidate<L, CF::Cost>> {
        let mut partials = vec![Candidate {
            expr: DagExpr::default(),
            cost: self.cost_fn.cost(&DagExpr::default()),
        }];
        for &root in roots {
            // Grab candidates for the roots class
            // If we hit a cycle, the candidates list will be empty.
            let class = self.egraph.find(root);
            self.ensure_class(class);
            let candidates = self.memo.get(&class).map(Vec::as_slice).unwrap_or_default();

            // Generate permutation of all partials with all candidates.
            // (At most beam^2 new partials.)
            let mut new_partials = TopK::new(self.beam);
            for partial in partials.iter() {
                for candidate in candidates {
                    let expr = partial.expr.merge(&candidate.expr);
                    let cost = self.cost_fn.cost(&expr);
                    new_partials.push(Candidate { expr, cost });
                }
            }
            partials = new_partials.into_inner();
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
            // Cycle: skip memoization; allow other non-cyclic candidates to be found
            return;
        }

        // Combine all e-nodes with all candidates for their children.
        let mut all = TopK::new(self.beam);
        for node in &self.egraph[id].nodes {
            let candidates = self.extract_multiple(node.children());
            for candidate in candidates {
                let mut expr = candidate.expr;
                expr.add_root_node(node.clone());
                let cost = self.cost_fn.cost(&expr);
                all.push(Candidate { expr, cost });
            }
        }
        self.visiting.remove(&id);
        self.memo.insert(id, all.into_inner());
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
        let rec = dag.extract_root(dag.roots()[0]);
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
        assert_eq!(dag.roots().len(), 2);

        let f_expr = dag.extract_root(dag.roots()[0]);
        let h_expr = dag.extract_root(dag.roots()[1]);
        assert_eq!(f_expr.to_string(), "(f x x)");
        assert_eq!(h_expr.to_string(), "(h (g x) (g x))");
        assert_eq!(dag.len(), 4);
    }

    #[test]
    fn beam_extract_tie_breaks_by_expr_order() {
        // Make an e-class with two equal-cost leaves: x and y
        let mut egraph = EGraph::<SymbolLang, ()>::default();
        let x = egraph.add(SymbolLang::leaf("x"));
        let y = egraph.add(SymbolLang::leaf("y"));
        egraph.union(x, y);
        egraph.rebuild();

        // With equal costs, tie-break should be by expr order; "x" < "y"
        let mut beamer = BeamExtract::new(&egraph, 2, DagSize);
        let dag = beamer.solve(x);
        let rec = dag.extract_root(dag.roots()[0]);
        assert_eq!(rec.to_string(), "x");
        assert_eq!(dag.len(), 1);
    }

    #[test]
    fn beam_width_keeps_best_answer_same() {
        // Build an e-class with two alternatives:
        //   f(x x)  -> size 2 DAG (x, f)
        //   h(g(x) g(x)) -> size 3 DAG (x, g, h)
        let mut egraph = EGraph::<SymbolLang, ()>::default();
        let x = egraph.add(SymbolLang::leaf("x"));
        let fxx = egraph.add(SymbolLang::new("f", vec![x, x]));
        let gx = egraph.add(SymbolLang::new("g", vec![x]));
        let hgg = egraph.add(SymbolLang::new("h", vec![gx, gx]));
        egraph.union(fxx, hgg);
        egraph.rebuild();

        // Beam=1 and Beam=5 should both pick (f x x) as the best
        let mut b1 = BeamExtract::new(&egraph, 1, DagSize);
        let d1 = b1.solve(fxx);
        let r1 = d1.extract_root(d1.roots()[0]);
        assert_eq!(r1.to_string(), "(f x x)");
        assert_eq!(d1.len(), 2);

        let mut b5 = BeamExtract::new(&egraph, 5, DagSize);
        let d5 = b5.solve(fxx);
        let r5 = d5.extract_root(d5.roots()[0]);
        assert_eq!(r5.to_string(), "(f x x)");
        assert_eq!(d5.len(), 2);
    }

    #[test]
    fn beam_width_two_finds_better_solution() {
        // Minimal setup where beam=2 can choose a globally better pair by sharing.
        // Let s = g(g x) and t = g(g y).
        let mut egraph = EGraph::<SymbolLang, ()>::default();
        let x = egraph.add(SymbolLang::leaf("x"));
        let y = egraph.add(SymbolLang::leaf("y"));
        let gx = egraph.add(SymbolLang::new("g", vec![x]));
        let ggx = egraph.add(SymbolLang::new("g", vec![gx])); // s
        let gy = egraph.add(SymbolLang::new("g", vec![y]));
        let ggy = egraph.add(SymbolLang::new("g", vec![gy])); // t

        // Class A: a1 = f(t) (cheaper individually), a2 = f(g(s)) (more expensive individually)
        let a1 = egraph.add(SymbolLang::new("f", vec![ggy]));
        let gs = egraph.add(SymbolLang::new("g", vec![ggx]));
        let a2 = egraph.add(SymbolLang::new("f", vec![gs]));
        egraph.union(a1, a2);

        // Class B: b1 = h(t), b2 = h(s) (tie; b2 favored lexicographically due to x < y)
        let b1 = egraph.add(SymbolLang::new("h", vec![ggy]));
        let b2 = egraph.add(SymbolLang::new("h", vec![ggx]));
        egraph.union(b1, b2);

        egraph.rebuild();

        // With beam=1, A picks a1 (uses t) while B picks b2 (uses s) -> no sharing across roots.
        let mut ex1 = BeamExtract::new(&egraph, 1, DagSize);
        let dag1 = ex1.solve_multiple(&[a1, b1]);
        assert_eq!(dag1.len(), 8, "beam=1 should not share and be larger");

        // With beam=2, A can pick a2 (uses s) and B picks b2 (uses s) -> share s, smaller overall.
        let mut ex2 = BeamExtract::new(&egraph, 2, DagSize);
        let dag2 = ex2.solve_multiple(&[a1, b1]);
        assert_eq!(dag2.len(), 5, "beam=2 should share s and be smaller");
    }
}
