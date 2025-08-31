use std::cmp::Reverse;
use std::collections::BinaryHeap;

use crate::{util::IndexMap, Id, Language, RecExpr};

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
///
/// This type provides focused conveniences around working with multiple roots:
/// - Construction and validation helpers
/// - Canonicalization/minimization that preserves and remaps roots
/// - Efficient merging of canonical DAGs while remapping/concatenating roots
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DagExpr<L> {
    pub nodes: Vec<L>,
    pub roots: Vec<Id>,
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

    /// Returns the number of nodes in the underlying expression.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Returns true if the underlying expression has no nodes.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Returns a shared reference to the roots.
    pub fn roots(&self) -> &[Id] {
        &self.roots
    }

    /// Adds a new root id (must already be a valid id in `nodes`).
    pub fn push_root(&mut self, root: Id) {
        debug_assert!(
            usize::from(root) < self.nodes.len(),
            "DagExpr::push_root: root out of bounds"
        );
        self.roots.push(root);
    }

    /// Merge `other` (assumed canonical) into this canonical `DagExpr`, preserving shortlex order.
    ///
    /// - `self` and `other` must both be canonical (shortlex minimal DAGs).
    /// - This will rebuild `self.nodes` to the merged, canonical DAG.
    /// - `self.roots` are remapped in place to the new ids in the merged DAG.
    /// - Returns the new id of `other`'s (single) root within the merged DAG.
    pub fn merge(&self, other: &Self) -> Self {
        let n_self = self.len();
        let n_other = other.len();

        // Merged nodes and interner for deduplication
        let mut new_nodes: Vec<L> = Vec::with_capacity(n_self + n_other);
        let mut intern: IndexMap<L, Id> = IndexMap::default();

        // Old-id -> new-id mappings for both inputs
        let mut self_map: Vec<Option<Id>> = vec![None; n_self];
        let mut other_map: Vec<Option<Id>> = vec![None; n_other];

        // Enumerating iterators over both inputs
        let mut it_self = self.nodes.iter().cloned().enumerate().peekable();
        let mut it_other = other.nodes.iter().cloned().enumerate().peekable();

        use std::cmp::Ordering::*;
        loop {
            match (it_self.peek(), it_other.peek()) {
                (Some((is, ns)), Some((io, no))) => {
                    let is = *is;
                    let io = *io;

                    let a = ns
                        .clone()
                        .map_children(|cid| self_map[usize::from(cid)].unwrap());
                    let b = no
                        .clone()
                        .map_children(|cid| other_map[usize::from(cid)].unwrap());

                    match a.cmp(&b) {
                        Less => {
                            let id = match intern.get(&a) {
                                Some(&id) => id,
                                None => {
                                    let id = Id::from(new_nodes.len());
                                    intern.insert(a.clone(), id);
                                    new_nodes.push(a);
                                    id
                                }
                            };
                            self_map[is] = Some(id);
                            it_self.next();
                        }
                        Greater => {
                            let id = match intern.get(&b) {
                                Some(&id) => id,
                                None => {
                                    let id = Id::from(new_nodes.len());
                                    intern.insert(b.clone(), id);
                                    new_nodes.push(b);
                                    id
                                }
                            };
                            other_map[io] = Some(id);
                            it_other.next();
                        }
                        Equal => {
                            let id = match intern.get(&a) {
                                Some(&id) => id,
                                None => {
                                    let id = Id::from(new_nodes.len());
                                    intern.insert(a.clone(), id);
                                    new_nodes.push(a);
                                    id
                                }
                            };
                            self_map[is] = Some(id);
                            other_map[io] = Some(id);
                            it_self.next();
                            it_other.next();
                        }
                    }
                }
                (Some((is, ns)), None) => {
                    let is = *is;
                    let a = {
                        let node = ns.clone();
                        debug_assert!(
                            node.children()
                                .iter()
                                .all(|&c| self_map[usize::from(c)].is_some()),
                            "Self node at {} not ready; DAG invariant violated",
                            is
                        );
                        node.map_children(|cid| self_map[usize::from(cid)].unwrap())
                    };
                    let id = match intern.get(&a) {
                        Some(&id) => id,
                        None => {
                            let id = Id::from(new_nodes.len());
                            intern.insert(a.clone(), id);
                            new_nodes.push(a);
                            id
                        }
                    };
                    self_map[is] = Some(id);
                    it_self.next();
                }
                (None, Some((io, no))) => {
                    let io = *io;
                    let b = {
                        let node = no.clone();
                        debug_assert!(
                            node.children()
                                .iter()
                                .all(|&c| other_map[usize::from(c)].is_some()),
                            "Other node at {} not ready; DAG invariant violated",
                            io
                        );
                        node.map_children(|cid| other_map[usize::from(cid)].unwrap())
                    };
                    let id = match intern.get(&b) {
                        Some(&id) => id,
                        None => {
                            let id = Id::from(new_nodes.len());
                            intern.insert(b.clone(), id);
                            new_nodes.push(b);
                            id
                        }
                    };
                    other_map[io] = Some(id);
                    it_other.next();
                }
                (None, None) => break,
            }
        }

        // All nodes from both inputs must be processed
        debug_assert!(self_map.iter().all(|m| m.is_some()));
        debug_assert!(other_map.iter().all(|m| m.is_some()));

        // Remap roots for both inputs and return merged DAG with concatenated roots
        let mut roots: Vec<Id> = Vec::with_capacity(self.roots.len() + other.roots.len());
        for &r in &self.roots {
            roots.push(self_map[usize::from(r)].unwrap());
        }
        for &r in &other.roots {
            roots.push(other_map[usize::from(r)].unwrap());
        }

        DagExpr {
            nodes: new_nodes,
            roots,
        }
    }

    /// Extract a RecExpr containing only the subgraph reachable from the given root id.
    pub fn extract_root(&self, root: Id) -> RecExpr<L>
    where
        L: Clone,
    {
        let root_idx = usize::from(root);
        assert!(root_idx < self.nodes.len(), "root out of bounds");

        // Build a RecExpr by recursively constructing nodes reachable from root
        let n = self.nodes.len();
        let mut id_map: Vec<Option<Id>> = vec![None; n];
        let mut out: RecExpr<L> = RecExpr::default();

        fn build<L: Language + Clone>(
            i: usize,
            nodes: &[L],
            id_map: &mut [Option<Id>],
            out: &mut RecExpr<L>,
        ) -> Id {
            if let Some(id) = id_map[i] {
                return id;
            }
            let mapped_children: Vec<Id> = nodes[i]
                .children()
                .iter()
                .map(|&c| build(usize::from(c), nodes, id_map, out))
                .collect();

            let mut node = nodes[i].clone();
            for (slot, &mid) in node.children_mut().iter_mut().zip(mapped_children.iter()) {
                *slot = mid;
            }
            let new_id = out.add(node);
            id_map[i] = Some(new_id);
            new_id
        }

        let _ = build(root_idx, &self.nodes, &mut id_map, &mut out);
        out
    }

    /// Minimize/canonicalize this `DagExpr` while remapping all roots.
    ///
    /// This removes unreachable nodes (w.r.t. the current roots), deduplicates
    /// structurally equivalent nodes, and canonicalizes the topological order
    /// to a lexicographically minimal order. Roots are updated accordingly.
    fn minimize(mut self) -> Self {
        let n = self.len();
        if n == 0 {
            return self;
        }

        // Compute reachability from the given roots

        let used = {
            let mut used = vec![false; n];
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

        // Build reverse edges (parents) in a compressed adjacency form.
        // We only include reachable nodes.
        // The parents of node i are parent_index[parents_start[i]..parents_start[i+1]]
        let (parents_start, parents_index) = {
            let mut parents_start: Vec<usize> = vec![0; n + 1];
            for i in 0..n {
                if !used[i] {
                    continue;
                }
                for &c in self.nodes[i].children() {
                    let ci = usize::from(c);
                    if used[ci] {
                        parents_start[ci + 1] += 1;
                    }
                }
            }
            // Convert from counts to offsets.
            for i in 0..n {
                parents_start[i + 1] += parents_start[i];
            }

            let mut parents_index: Vec<usize> = vec![0; *parents_start.last().unwrap()];
            let mut cursor = parents_start.clone();
            for i in 0..n {
                if !used[i] {
                    continue;
                }
                for &c in self.nodes[i].children() {
                    let ci = usize::from(c);
                    if used[ci] {
                        let pos = &mut cursor[ci];
                        parents_index[*pos] = i;
                        *pos += 1;
                    }
                }
            }
            (parents_start, parents_index)
        };

        // Use a remaining count to track when parents become ready.
        // Unused nodes have remaining == usize::MAX so they are never ready.
        let mut remaining: Vec<usize> = self
            .nodes
            .iter()
            .enumerate()
            .map(|(i, n)| {
                if used[i] {
                    n.children().len()
                } else {
                    usize::MAX
                }
            })
            .collect();

        // Min-heap of ready nodes keyed by remapped node (Reverse to get min-heap behavior).
        // Initially, all reachable leaves (remaining == 0) are ready.
        let mut heap: BinaryHeap<Reverse<(L, usize)>> = BinaryHeap::new();
        heap.extend(
            remaining
                .iter()
                .enumerate()
                .filter(|(_i, &c)| c == 0)
                .map(|(i, _c)| (Reverse((self.nodes[i].clone(), i)))),
        );

        // Process ready nodes in order until all reachable nodes are assigned.
        let mut id_map: Vec<Option<Id>> = vec![None; n];
        let mut new_nodes: Vec<L> = Vec::new();
        while let Some(Reverse((node, i))) = heap.pop() {
            // All duplicate nodes will be popped consecutively, so dedup against last.
            if new_nodes.last() != Some(&node) {
                new_nodes.push(node);
            }

            // Update the id_map with the new id.
            id_map[i] = Some(Id::from(new_nodes.len() - 1));

            // Decrement parents; when a parent becomes ready, push its remapped node.
            for &p in &parents_index[parents_start[i]..parents_start[i + 1]] {
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
        for r in self.roots.iter_mut() {
            *r = id_map[usize::from(*r)].unwrap();
        }
        self.nodes = new_nodes;
        self
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
