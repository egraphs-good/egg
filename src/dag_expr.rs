use std::cmp::Ordering::*;
use std::cmp::Reverse;
use std::collections::BinaryHeap;

use crate::hashmap_with_capacity;
use crate::{util::HashSet, Id, Language, RecExpr};

/// A DAG expression with multiple roots.
///
/// DagExpr pairs a compact, shortlex-minimal node list with a set of root Ids,
/// allowing you to represent forests or multi-rooted DAGs explicitly without
/// changing the RecExpr API.
///
/// Invariants (maintained by constructors and mutators):
/// 1) DAG: no back-edges (each node only points to lower indices)
/// 2) No duplicates: structurally equal nodes occur at most once
/// 3) Canonical: nodes are in shortlex-minimal topological order
/// 4) All nodes are reachable from the roots
///
/// This type provides focused conveniences around working with multiple roots:
/// - Construction and validation helpers
/// - Canonicalization/minimization that preserves and remaps roots
/// - Efficient merging of canonical DAGs while remapping/concatenating roots
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DagExpr<L> {
    nodes: Vec<L>,
    roots: Vec<Id>,
}

impl<L> Default for DagExpr<L> {
    fn default() -> Self {
        DagExpr {
            nodes: Vec::new(),
            roots: Vec::new(),
        }
    }
}

impl<L: Language> DagExpr<L> {
    /// Creates a new `DagExpr`, validating and canonicalizing to enforce invariants.
    ///
    /// This calls [`DagExpr::try_new`] and unwraps.
    pub fn new(nodes: Vec<L>, roots: Vec<Id>) -> Self {
        Self::try_new(nodes, roots).expect("DagExpr::new: invalid nodes/roots")
    }

    /// Creates a new `DagExpr`, validates nodes/roots, and canonicalizes to enforce invariants.
    ///
    /// Validation:
    /// - All child ids refer to lower indices (DAG property).
    /// - All roots are in-bounds.
    /// Canonicalization:
    /// - Calls [`DagExpr::minimize`] to prune unreachable nodes, dedup duplicates,
    ///   and produce shortlex-minimal topological order.
    pub fn try_new(nodes: Vec<L>, roots: Vec<Id>) -> Result<Self, String> {
        // Check root bounds early
        let n = nodes.len();
        if roots.iter().any(|&r| usize::from(r) >= n) {
            return Err("DagExpr::try_new: root out of bounds for nodes".into());
        }
        // Validate DAG property: each node's children < its index
        for (i, node) in nodes.iter().enumerate() {
            if !node.all(|c| usize::from(c) < i) {
                return Err(format!(
                    "DagExpr::try_new: non-DAG structure, node {} has a child >= itself",
                    i
                ));
            }
        }
        // Build, then canonicalize to enforce dedup + ordering invariants
        let dag = DagExpr { nodes, roots };
        Ok(dag.minimize())
    }

    /// Construct a canonical single-node DAG from a leaf node (no children).
    pub fn from_leaf(node: L) -> Self {
        assert!(
            node.children().is_empty(),
            "from_leaf: node must have no children"
        );
        let result = DagExpr {
            nodes: vec![node],
            roots: vec![Id::from(0usize)],
        };
        debug_assert!(result.is_valid());
        result
    }

    /// Returns the number of nodes in the underlying expression.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Returns true if the underlying expression has no nodes.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Returns a shared reference to the nodes.
    pub fn nodes(&self) -> &[L] {
        &self.nodes
    }

    /// Returns a shared reference to the roots.
    pub fn roots(&self) -> &[Id] {
        &self.roots
    }

    /// Given a Node with arity equal the current number of roots,
    /// adds it as a the new root node, consuming the current roots as its children.
    pub(crate) fn add_root_node(&mut self, mut node: L) {
        assert_eq!(node.children().len(), self.roots.len());
        node.children_mut().copy_from_slice(&self.roots);
        self.nodes.push(node);
        self.roots = vec![Id::from(self.nodes.len() - 1)];
        debug_assert!(self.is_valid());
    }

    /// Extract a RecExpr containing only the subgraph reachable from the given root id.
    pub fn extract_root(&self, root: Id) -> RecExpr<L> {
        let root_idx = usize::from(root);
        assert!(root_idx < self.nodes.len(), "root out of bounds");

        // Build a RecExpr by recursively constructing nodes reachable from root
        let n = self.nodes.len();
        let mut id_map: Vec<Option<Id>> = vec![None; n];
        let mut out: RecExpr<L> = RecExpr::default();

        fn build<L: Language>(
            i: usize,
            nodes: &[L],
            id_map: &mut [Option<Id>],
            out: &mut RecExpr<L>,
        ) -> Id {
            if let Some(id) = id_map[i] {
                return id;
            }
            let node = nodes[i]
                .clone()
                .map_children(|c| build(usize::from(c), nodes, id_map, out));
            let new_id = out.add(node);
            id_map[i] = Some(new_id);
            new_id
        }

        let _ = build(root_idx, &self.nodes, &mut id_map, &mut out);
        out
    }

    /// Merge `self` and `other` into a new canonical `DagExpr`.
    ///
    /// Precondition (ordering monotonicity):
    /// The `Ord` implementation for `L` must preserve relative order when all child `Id`s
    /// are remapped by the same strictly increasing function. Languages generated by
    /// `define_language!` and `SymbolLang` typically satisfy this because their `Ord`
    /// is structural (operator/arity, then lexicographic by children).
    ///
    /// This precondition enables a linear-time two-way merge, which is usually faster
    /// than concatenation followed by `minimize()`.
    ///
    /// Roots in the result are the concatenation of `self.roots` followed by `other.roots`,
    /// all remapped to ids in the merged DAG.
    pub fn merge(&self, other: &Self) -> Self {
        let mut new_nodes = Vec::with_capacity(self.len() + other.len());
        let mut intern = hashmap_with_capacity(self.len() + other.len());
        let mut self_map: Vec<Option<Id>> = vec![None; self.len()];
        let mut other_map: Vec<Option<Id>> = vec![None; other.len()];

        // Helper to intern a node and record its mapping
        let mut intern_id = |node: L, map: &mut Vec<Option<Id>>, idx: usize| -> Id {
            let id = *intern.entry(node).or_insert_with_key(|node| {
                new_nodes.push(node.clone());
                Id::from(new_nodes.len() - 1)
            });
            assert!(idx <= usize::from(id), "merge: index map not monotonic");
            map[idx] = Some(id);
            id
        };

        // Merge sort, mapping inputs as we go.
        let mut it_self = self.nodes.iter().enumerate();
        let mut it_other = other.nodes.iter().enumerate();
        let mut self_mapped = None;
        let mut other_mapped = None;
        loop {
            if self_mapped.is_none() {
                self_mapped = it_self.next().map(|(i, node)| {
                    let node = node
                        .clone()
                        .map_children(|cid| self_map[usize::from(cid)].unwrap());
                    (i, node)
                });
            }
            if other_mapped.is_none() {
                other_mapped = it_other.next().map(|(i, node)| {
                    let node = node
                        .clone()
                        .map_children(|cid| other_map[usize::from(cid)].unwrap());
                    (i, node)
                });
            }
            match (self_mapped.take(), other_mapped.take()) {
                (Some((is, ns)), Some((io, no))) => match ns.cmp(&no) {
                    Less => {
                        intern_id(ns, &mut self_map, is);
                        other_mapped = Some((io, no));
                    }
                    Greater => {
                        intern_id(no, &mut other_map, io);
                        self_mapped = Some((is, ns));
                    }
                    Equal => {
                        let id = intern_id(ns, &mut self_map, is);
                        other_map[io] = Some(id);
                    }
                },
                (Some((is, ns)), None) => {
                    intern_id(ns, &mut self_map, is);
                }
                (None, Some((io, no))) => {
                    intern_id(no, &mut other_map, io);
                }
                (None, None) => break,
            }
        }

        // All nodes from both inputs must be processed
        debug_assert!(self_map.iter().all(|m| m.is_some()));
        debug_assert!(other_map.iter().all(|m| m.is_some()));

        // Remap roots for both inputs and return merged DAG with concatenated roots
        let self_roots = self
            .roots
            .iter()
            .map(|&r| self_map[usize::from(r)].unwrap());
        let other_roots = other
            .roots
            .iter()
            .map(|&r| other_map[usize::from(r)].unwrap());
        let result = DagExpr {
            nodes: new_nodes,
            roots: self_roots.chain(other_roots).collect(),
        };
        debug_assert!(result.is_valid());
        result
    }

    /// Minimize/canonicalize this `DagExpr` while remapping all roots.
    ///
    /// This removes unreachable nodes (w.r.t. the current roots), deduplicates
    /// structurally equivalent nodes, and canonicalizes the topological order
    /// to a lexicographically minimal order. Roots are updated accordingly.
    fn minimize(&self) -> Self {
        // Compute reachability from the given roots
        let used = {
            let mut used = vec![false; self.nodes.len()];
            let mut stack: Vec<usize> = self.roots.iter().map(|&r| usize::from(r)).collect();
            while let Some(i) = stack.pop() {
                if used[i] {
                    continue;
                }
                used[i] = true;
                for &child in self.nodes[i].children() {
                    let c = usize::from(child);
                    if !used[c] {
                        stack.push(c);
                    }
                }
            }
            used
        };

        // Build parents adjacency and remaining child counts for reachable nodes
        let mut parents: Vec<Vec<usize>> = vec![Vec::new(); self.nodes.len()];
        let mut remaining: Vec<usize> = vec![usize::MAX; self.nodes.len()];
        for (i, n) in self.nodes.iter().enumerate().filter(|&(i, _)| used[i]) {
            remaining[i] = n.children().len();
            for &c in n.children() {
                assert!(used[usize::from(c)]);
                parents[usize::from(c)].push(i);
            }
        }

        // Min-heap of ready nodes keyed by remapped node (Reverse to get min-heap behavior).
        // Initially, all reachable leaves (remaining == 0) are ready.
        let mut heap: BinaryHeap<Reverse<(L, usize)>> = BinaryHeap::new();
        for (i, &rem) in remaining.iter().enumerate() {
            if rem == 0 {
                heap.push(Reverse((self.nodes[i].clone(), i)));
            }
        }

        // Process ready nodes in order until all reachable nodes are assigned.
        // In the process an interning map is built to deduplicate nodes.
        let mut id_map: Vec<Option<Id>> = vec![None; self.nodes.len()];
        let mut new_nodes = Vec::with_capacity(self.nodes.len());
        let mut intern = hashmap_with_capacity(self.nodes.len());
        let mut intern_node = |node: L| -> Id {
            *intern.entry(node).or_insert_with_key(|node| {
                new_nodes.push(node.clone());
                Id::from(new_nodes.len() - 1)
            })
        };
        while let Some(Reverse((node, i))) = heap.pop() {
            let id = intern_node(node);
            id_map[i] = Some(id);

            // Decrement parents; when a parent becomes ready, push its remapped node to the heap.
            for &p in &parents[i] {
                remaining[p] -= 1;
                if remaining[p] == 0 {
                    let mapped = self.nodes[p]
                        .clone()
                        .map_children(|cid| id_map[usize::from(cid)].unwrap());
                    heap.push(Reverse((mapped, p)));
                }
            }
        }

        // Remap roots to new ids and replace nodes
        debug_assert!(id_map
            .iter()
            .enumerate()
            .all(|(i, m)| !used[i] || m.is_some()));
        let result = DagExpr {
            nodes: new_nodes,
            roots: self
                .roots
                .iter()
                .map(|&r| id_map[usize::from(r)].unwrap())
                .collect(),
        };
        debug_assert!(result.is_valid());
        result
    }

    /// Check if this `DagExpr` has all invariants.
    fn is_valid(&self) -> bool {
        let mut used = vec![false; self.nodes.len()];
        for r in &self.roots {
            let ri = usize::from(*r);
            if ri >= self.nodes.len() {
                // Root out of bounds
                return false;
            }
            used[ri] = true;
        }
        let mut seen = HashSet::with_capacity_and_hasher(self.nodes.len(), Default::default());
        for (i, node) in self.nodes.iter().enumerate() {
            if !seen.insert(node) {
                // Duplicate node
                return false;
            }
            let mut topo_order = false;
            for &c in node.children() {
                let ci = usize::from(c);
                if ci >= i {
                    // Not a DAG or child out of bounds
                    return false;
                }
                used[ci] = true;
                topo_order |= ci + 1 == i; // Has immediate predecessor as child
            }
            if !topo_order && i > 0 && node <= &self.nodes[i - 1] {
                // Not in lexicographical order
                return false;
            }
        }
        if !used.iter().all(|&u| u) {
            // Some nodes are unreachable
            return false;
        }
        true
    }
}

impl<L: Language> From<&RecExpr<L>> for DagExpr<L> {
    fn from(expr: &RecExpr<L>) -> Self {
        DagExpr {
            nodes: expr.iter().cloned().collect(),
            roots: vec![expr.root()],
        }
        .minimize()
    }
}

impl<L: Language> From<RecExpr<L>> for DagExpr<L> {
    fn from(expr: RecExpr<L>) -> Self {
        DagExpr::from(&expr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SymbolLang;

    #[test]
    fn is_minimal_rejects_non_adjacent_duplicate() {
        // Non-adjacent duplicate should now be rejected by is_minimal.
        // nodes: [x, f(x), x], roots: [f(x), x]
        let dag = DagExpr {
            nodes: vec![
                SymbolLang::leaf("x"),
                SymbolLang::new("f", vec![Id::from(0usize)]),
                SymbolLang::leaf("x"), // duplicate of node 0, non-adjacent
            ],
            roots: vec![Id::from(1usize), Id::from(2usize)],
        };

        // With duplicate checking, this should be rejected.
        assert!(
            !dag.is_valid(),
            "is_minimal must reject non-adjacent duplicates"
        );

        // Canonicalization deduplicates, so nodes must change (length drops from 3 to 2).
        let canon = dag.clone().minimize();
        assert!(
            canon.nodes().len() < dag.nodes().len(),
            "minimize should deduplicate duplicate nodes"
        );
    }

    #[test]
    fn minimize_produces_canonical_dag() {
        // Build a non-canonical nodes list: duplicate g(f x), root at h
        let mut nodes: Vec<SymbolLang> = Vec::new();
        let x = Id::from(0usize);
        nodes.push(SymbolLang::leaf("x")); // 0
        let f_x = Id::from(1usize);
        nodes.push(SymbolLang::new("f", vec![x])); // 1
        nodes.push(SymbolLang::new("g", vec![f_x])); // 2 (g (f x))
        nodes.push(SymbolLang::new("g", vec![f_x])); // 3 duplicate g (f x)
        nodes.push(SymbolLang::new("h", vec![Id::from(2), Id::from(3)])); // 4 h(g(f x), g(f x))

        let dag = DagExpr::new(nodes, vec![Id::from(4)]);
        assert_eq!(dag.nodes.len(), 4, "should dedup duplicate g(f x)");
        // Check pretty-print by rebuilding from root
        let rec = dag.extract_root(dag.roots[0]);
        assert_eq!(rec.to_string(), "(h (g (f x)) (g (f x)))");
        // Positive canonical case: result of DagExpr::new should be minimal
        assert!(dag.is_valid());
    }

    #[test]
    fn merge_dedups_and_concatenates_roots() {
        // left: (l (g (f x)))
        let left: RecExpr<SymbolLang> = "(l (g (f x)))".parse().unwrap();
        let dag_left: DagExpr<SymbolLang> = DagExpr::from(left);

        // right: (r (g (f x)))
        let right: RecExpr<SymbolLang> = "(r (g (f x)))".parse().unwrap();
        let dag_right: DagExpr<SymbolLang> = DagExpr::from(right);

        // merge, expecting shared subtrees to dedup and roots to concatenate
        let merged = dag_left.merge(&dag_right);

        assert_eq!(merged.roots.len(), 2);
        let left_rec = merged.extract_root(merged.roots[0]);
        let right_rec = merged.extract_root(merged.roots[1]);

        assert_eq!(left_rec.to_string(), "(l (g (f x)))");
        assert_eq!(right_rec.to_string(), "(r (g (f x)))");
        // nodes should be x, f x, g(f x), l(...), r(...)
        assert_eq!(merged.nodes.len(), 5);
    }

    #[test]
    fn merge_multiple_roots() {
        // Build two separate dag exprs sharing substructure (g (f x))
        let a: RecExpr<SymbolLang> = "(l (g (f x)))".parse().unwrap();
        let b: RecExpr<SymbolLang> = "(r (g (f x)))".parse().unwrap();

        let dag_a = DagExpr::from(a);
        let dag_b = DagExpr::from(b);

        let merged = dag_a.merge(&dag_b);
        assert_eq!(merged.roots.len(), 2);

        // Validate both roots reconstruct correctly
        let left_rec = merged.extract_root(merged.roots[0]);
        let right_rec = merged.extract_root(merged.roots[1]);

        assert_eq!(left_rec.to_string(), "(l (g (f x)))");
        assert_eq!(right_rec.to_string(), "(r (g (f x)))");
        assert!(merged.nodes.len() >= 5);
    }

    #[test]
    fn extract_root_returns_exact_subgraph() {
        // Build DAG with two roots (f x x) and (h (g x) (g x))
        let fx: RecExpr<SymbolLang> = "(f x x)".parse().unwrap();
        let hgx: RecExpr<SymbolLang> = "(h (g x) (g x))".parse().unwrap();

        let dag_fx = DagExpr::from(fx);
        let dag_hgx = DagExpr::from(hgx);
        let dag = dag_fx.merge(&dag_hgx);

        let r1_rec = dag.extract_root(dag.roots[0]);
        let r2_rec = dag.extract_root(dag.roots[1]);

        assert_eq!(r1_rec.to_string(), "(f x x)");
        assert_eq!(r2_rec.to_string(), "(h (g x) (g x))");
    }
}
