# Exact SCC-local rank constraints for LP e-graph extraction

This artifact proves the abstract rank portion of the proposed fix for
[`egraphs-good/egg#207`](https://github.com/egraphs-good/egg/issues/207),
including the SCC-local refinement used by `src/lp_extract.rs`.
It was developed against egg base commit
`73975c9819efb4af2f3c6c1b44fa53f8c5742574`.
The proof does not import or verify the Rust implementation or CBC.

## Model and exact partition assumptions

`Class` is any finite type of canonical eclasses. `Node` is any type of
possible e-nodes. Each node has an owning class, a child predicate and a
Boolean selection. `PossibleEdge parent child` means that some node of
`parent` contains `child`; `SelectedEdge parent child` additionally requires
that node to be selected. `selected_subrelation_possible` proves that the
selected relation is a subrelation of the full possible-edge relation.

Component labels have decidable equality. The type of labels need not be
finite or inhabited: unused labels have empty fibers. A component's size is
exactly the cardinality of its class subtype, not a supplied size estimate.
`ExactSCCPartition` specifies the intended partition:

```text
component(a) = component(b)
  iff
there is a possibly empty possible-edge path a -> b
and there is a possibly empty possible-edge path b -> a.
```

The main theorem needs only the weaker `CyclePartition` condition:

```text
possible(a,b) and a nonempty possible-edge path b -> a
  imply component(a) = component(b).
```

`exact_scc_partition_is_cycle_partition` checks that exact SCC labels satisfy
this sufficient condition. Conservatively merging SCCs is also sound; a
partition splitting an actual cycle does not satisfy the assumption.
No assumption that the selected graph is acyclic is used to validate a
partition. The partition is for all possible edges, including alternatives
that are not selected and direct self-loops.

## Production encoding and checked conclusion

For every component of size `m > 1`, introduce a continuous real rank for
each class with `0 <= rank(v) <= m - 1`. For each possible e-node child whose
owner and child belong to that component, impose the exact row orientation
used by the Rust code:

```text
rank(owner(node)) - rank(child) - m * selected(node) >= 1 - m
```

There are no cross-component rank rows. Components of size zero or one have
no rank variables or rank rows. Separately, every node containing its own
owning class as a child is fixed to selection zero (`SelfLoopsDisabled`).
`SCCRanks` models only ranks for fibers with size greater than one: the
formal result does not hide singleton rank variables in the witness.

`exact_scc_encoding_sound_and_complete` proves, for every Boolean selection
and every exact SCC partition:

```text
selected-edge relation has no nonempty directed closed walk
  iff
direct self-loop nodes are disabled and there exist SCC-local bounded
real ranks satisfying every intra-component conditional row.
```

`scc_encoding_sound_and_complete` proves the same equivalence under the
weaker sufficient `CyclePartition` assumption. Both directions are checked:
all acyclic selections are preserved, and all selections admitted by these
constraints are acyclic. This covers sharing, multiple roots, disconnected
components, direct self-loops, and the empty class type. Child multiplicity
is irrelevant: repeated occurrences impose identical inequalities.

The proof is factored into these checked bridges:

1. `returning_path_internal` and `acyclic_iff_internal`: every selected
   closed walk stays within components, so dropping cross-component rank
   rows does not lose cycle exclusion.
2. `acyclic_iff_components`: global selected acyclicity is equivalent to
   acyclicity on every finite component subtype.
3. `bounded_rank_exists`, instantiated on each subtype: counting strict
   reachable descendants gives ranks in `[0, m - 1]`, with a drop of at
   least one on every selected edge.
4. `component_row_iff`: the production row is equivalent to requiring this
   drop only when the node is selected. For selection zero, `M = m` makes
   the row redundant even at the extreme permitted ranks.
5. `singleton_component_has_no_edges`: after directly self-looping nodes
   are disabled, a component with at most one class has no selected
   internal edge, so it needs no rank variables.

The earlier global `encoding_sound_and_complete` theorem is retained as a
building block and independent result. It uses `n = card Class` and ranks
on every class; it is not a description of the optimized production model.

## Objective and expression scope

No rank theorem assumes anything about costs. The one-node-per-active-class,
child-activation, and root-activation constraints are separate parts of the
Rust model. Completeness concerns class-consistent selections, not arbitrary
finite terms using different representatives of the same eclass at different
occurrences.

`objective_subset_le` proves separately that deleting a subset of selected
nodes cannot increase an additive objective if every node cost is
nonnegative. The caller must establish that pruning preserves roots and
closure under children. The proof does not formalize that pruning bridge,
a complete optimization theorem, or a theorem about all possible `RecExpr`s.
Negative costs can reward disconnected selections omitted by reconstruction,
so rooted-output optimality needs the documented nonnegative-cost assumption
or a separate policy/model.

## Replay

Pins:

- Lean `leanprover/lean4:v4.30.0-rc2`, compiler commit
  `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
- Mathlib `9977002c3c9492b622fb469b0d18acc7e73aed3e`

`lean-toolchain`, `lakefile.toml` and `lake-manifest.json` record the compiler
and dependency pins. Install elan from its official distribution, then:

```sh
cd doc/proofs/lp_rank
# Optional when the default user cache directory is not writable:
export XDG_CACHE_HOME="$PWD/.lake/cache"
elan toolchain install leanprover/lean4:v4.30.0-rc2
lake update
lake exe cache get
bash replay.sh
```

An existing dependency project at the same pins can also be used:

```sh
bash replay.sh /path/to/prepared-mathlib-project
```

The optional project supplies the compiler/import environment only; proof
source and `build.log` remain in this artifact directory. It is not edited.
`replay.sh` checks both pins and the source, records its SHA256, requires
both main-theorem axiom reports, and rejects unfinished-proof warnings or
any reported axiom beyond the three standard logical axioms below. The
axiom reports cover the SCC bridge, production-row equivalence, singleton
case, both SCC main theorems, and the original global/objective theorems.
The accepted proofs use only Lean's standard `propext`, `Classical.choice`
and `Quot.sound` axioms, with no new axioms or unfinished proofs.

## Implementation and numerical boundaries

The theorem concerns exact real arithmetic and exact Boolean selections.
It assumes a finite canonical-class model, the stated possible-edge
relation, and the stated component partition. It does not verify:

- Rust canonicalization, full-possible-edge graph construction, iterative
  Kosaraju implementation, component labels, or reported component sizes
- The translation from Rust variables and rows into this mathematical model
- `good_lp`, CBC, floating-point conversions, feasibility/integrality
  tolerances, solver status, timeout incumbents, or optimality guarantees
- Expression decoding, root-reachable pruning, or reconstruction

Those bridges require implementation review and executable tests. A passing
Lean replay is evidence for this exact abstract encoding, not formal
verification of the Rust extractor or CBC.
