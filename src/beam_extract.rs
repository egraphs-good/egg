use crate::util::{HashMap, HashSet};
use crate::*;

/// Candidate expression paired with its cost.
#[derive(Clone)]
struct Candidate<L: Language, C> {
    expr: RecExpr<L>,
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
    CF: CostFunction<L>,
{
    egraph: &'a EGraph<L, N>,
    beam: usize,
    memo: HashMap<Id, Vec<Candidate<L, CF::Cost>>>,
    visiting: HashSet<Id>,
    cost_fn: CF,
}

impl<'a, CF, L, N> BeamExtract<'a, CF, L, N>
where
    CF: CostFunction<L>,
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
        let mut expr = RecExpr::default();
        let mut root_ids = Vec::with_capacity(roots.len());
        for &root in roots {
            let cands = self.extract_class(root);
            if let Some(c) = cands.into_iter().next() {
                let id = expr.append_dedup(&c.expr);
                root_ids.push(id);
            } else {
                return (RecExpr::default(), vec![]);
            }
        }
        (expr, root_ids)
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
            let mut child_cands: Vec<Vec<Candidate<L, CF::Cost>>> = Vec::new();
            let mut skip = false;
            for &child in node.children() {
                let cands = self.extract_class(child);
                if cands.is_empty() {
                    skip = true;
                    break;
                }
                child_cands.push(cands);
            }
            if skip {
                continue;
            }
            let mut c = self.combine_enode(node, &child_cands);
            all.append(&mut c);
        }
        self.visiting.remove(&id);
        all.sort_by(|a, b| a.cost.partial_cmp(&b.cost).unwrap());
        all.truncate(self.beam);
        self.memo.insert(id, all.clone());
        all
    }

    /// Merge child candidates under `enode`, keeping at most the configured
    /// beam width.
    fn combine_enode(
        &mut self,
        enode: &L,
        child_cands: &[Vec<Candidate<L, CF::Cost>>],
    ) -> Vec<Candidate<L, CF::Cost>> {
        struct Partial<L: Language> {
            expr: RecExpr<L>,
            roots: Vec<Id>,
        }
        let mut partials = vec![Partial {
            expr: RecExpr::default(),
            roots: vec![],
        }];
        for child_list in child_cands {
            let mut new_partials: Vec<Partial<L>> = Vec::new();
            for part in &partials {
                for cand in child_list {
                    let mut expr = part.expr.clone();
                    let root = expr.append_dedup(&cand.expr);
                    let mut roots = part.roots.clone();
                    roots.push(root);
                    new_partials.push(Partial { expr, roots });
                }
            }
            new_partials.sort_by_key(|p| p.expr.len());
            new_partials.truncate(self.beam);
            partials = new_partials;
        }
        let mut results: Vec<Candidate<L, CF::Cost>> = Vec::new();
        for part in partials {
            let mut expr = part.expr;
            let mut node = enode.clone();
            let mut roots_iter = part.roots.into_iter();
            node.update_children(|_| roots_iter.next().unwrap());
            expr.add(node);
            // `append_dedup` maintains compactness, so no additional
            // compaction is required here.
            let cost = self.cost_fn.cost_rec(&expr);
            results.push(Candidate { expr, cost });
        }
        results.sort_by(|a, b| a.cost.partial_cmp(&b.cost).unwrap());
        results.truncate(self.beam);
        results
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    /// Simple cost function that measures DAG size by counting nodes.
    #[derive(Debug)]
    struct DagSize;

    impl CostFunction<SymbolLang> for DagSize {
        type Cost = usize;
        fn cost<C>(&mut self, _enode: &SymbolLang, _costs: C) -> Self::Cost
        where
            C: FnMut(Id) -> Self::Cost,
        {
            1
        }
        fn cost_rec(&mut self, expr: &RecExpr<SymbolLang>) -> Self::Cost {
            expr.len()
        }
    }

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
