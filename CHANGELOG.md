# Changes

## [Unreleased] - ReleaseDate

## [0.10.0] - 2024-12-31
- Removed existence explanations from egg (the `explain_existance` function). This feature was buggy and not well supported. Supporting it fully required many changes, and it is incompatible with analysis. See #332 for more details.
- Change the API of `make` to have mutable access to the e-graph for some [advanced uses cases](https://github.com/egraphs-good/egg/pull/277).
- Fix an e-matching performance regression introduced in [this commit](https://github.com/egraphs-good/egg/commit/ae8af8815231e4aba1b78962f8c07ce837ee1c0e#diff-1d06da761111802c793c6e5ca704bfa0d6336d0becf87fddff02d81548a838ab).
- Use `quanta` instead of `instant` crate to provide timing information. This can provide a huge speedup if you have lots of rules, since it avoids some syscalls.

## [0.9.5] - 2023-06-29
- Fixed a few edge cases in proof size optimization that caused egg to crash.

## [0.9.4] - 2023-05-23
- [#253] Improved rebuilding algorithm using a queue.
- [#259] Fixed another overflow bug in proof size optimization.
- Various typo fixes (Thanks @nlewycky)

## [0.9.3] - 2023-02-06

### Added
- [#215](https://github.com/egraphs-good/egg/pull/215) Added a better intersection algorithms on two egraphs based on "Join Algorithms for the Theory of Uninterpreted Functions". The old intersection algorithm was not complete on the terms in both egraphs, but the new one is. Unfortunately, the new algorithm is quadratic.

### Changed
- [#230](https://github.com/egraphs-good/egg/pull/230) Fixed a performance bug in `get_string_with_let` that caused printing let-bound proofs to be extremely inefficient.


## [0.9.2] - 2022-12-15

### Added

- [#210](https://github.com/egraphs-good/egg/pull/210) Fix crashes in proof generation due to proof size calculations overflowing.

## [0.9.1] - 2022-09-22

### Added

- [#186](https://github.com/egraphs-good/egg/pull/186) Added proof minimization (enabled by default), a greedy algorithm to find smaller proofs
  - with and `without_explanation_length_optimization` for turning this on and off
  - `copy_without_unions` for copying an egraph but without any equality information
  - `id_to_expr` for getting an expression corresponding to a particular enode's id
- [#197](https://github.com/egraphs-good/egg/pull/197) Added `search_with_limit`, so that matching also stops when it hits scheduling limits.

### Changed

- Changed the `pre_union` hook to support explanations
  - now provides the `Id` of the two specific enodes that are merged,  not canonical ids.
  - It also provides the reason for the merge in the form of a `Justification`.

## [0.9.0] - 2022-06-12

### Added
- Added a way to update analysis data and have it propagate through the e-graph

### Changed
- Improved documentation
- Updated dependencies
- `union` is now allowed when explanations are on

## [0.8.1] - 2022-05-04

### Changed
- Improved documentation for features.

## [0.8.0] - 2022-04-28

### Added
- ([#128](https://github.com/egraphs-good/egg/pull/128)) Add an ILP-based extractor.
- ([#168](https://github.com/egraphs-good/egg/pull/168)) Added MultiPatterns.

### Changed
- ([#165](https://github.com/egraphs-good/egg/pull/165)) Unions now happen "instantly", restoring the pre-0.7 behavior. 
- The tested MSRV is now 1.60.0.
- Several small documentation enhancements.
- ([#162](https://github.com/egraphs-good/egg/pull/162), [#163](https://github.com/egraphs-good/egg/pull/163))
  Extracted the `Symbol` logic into the [`symbol_table`](https://crates.io/crates/symbol_table) crate.

## [0.7.1] - 2021-12-14

This patch fixes a pretty bad e-matching bug introduced in 0.7.0. Please upgrade!

### Fixed
- (#143) Non-linear patterns e-match correctly again
- (#141) Loosen requirement on FromOp::Error

## [0.7.0] - 2021-11-23

It's a been a long time since a release! 
There's a lot in this one, hopefully I can cut releases more frequently in the future,
 because there are definitely more features coming :)

### Added
- The egraph now has an `EGraph::with_explanations_enabled` mode that allows for
  explaining why two terms are equivalent in the egraph.
  In explanations mode, all unions must be done through `union_instantiations` in order
  to justify the union.
  Calling `explain_equivalence` returns an `Explanation`
  which has both a `FlatExplanation` form and a
  `TreeExplanation` form.
  See #115 and #119 for more details.
- The `BackoffScheduler` is now more flexible.
- `EGraph::pre_union` allows inspection of unions, which can be useful for debugging.
- The dot printer is now more flexible.

### Changed

- `Analysis::merge` now gets a `&mut self`, so it can store data on the `Analysis` itself.
- `Analysis::merge` has a different signature.
- Pattern compilation and execution is faster, especially when there are ground terms involved.
- All unions are now delayed until rebuilding, so `EGraph::rebuild` be called to observe effects.
- The `apply_one` function on appliers *now needs to perform unions*.
- The congruence closure algorithm now keeps the egraph congruent before
  doing any analysis (calling `make`). It does this by interleaving rebuilding
  and doing analysis.
- `EGraph::add_expr` now proceeds linearly through the given `RecExpr`, which
  should be faster and include _all_ e-nodes from the expression.
- `Rewrite` now has public `searcher` and `applier` fields and no `long_name`.
- ([#61](https://github.com/egraphs-good/egg/pull/61))
  Rebuilding is much improved!
  The new algorithm's congruence closure part is closer to
  [Downey, Sethi, Tarjan](https://dl.acm.org/doi/pdf/10.1145/322217.322228),
  and the analysis data propagation is more precise with respect to merging.
  Overall, the algorithm is simpler, easier to reason about, and more than twice as fast!
- ([#86](https://github.com/egraphs-good/egg/pull/86))
  `Language::display_op` has been removed. Languages should implement `Display`
  to display the operator instead. `define_language!` now implements `Display`
  accordingly.
- `Language::from_op_str` has been replaced by a new `FromOp` trait.
  `define_language!` implements this trait automatically.

## [0.6.0] - 2020-07-16

### Added
- `Id` is now a struct not a type alias. This should help prevent some bugs.
- `Runner` hooks allow you to modify the `Runner` each iteration and stop early if you want.
- Added a way to lookup an e-node without adding it.
- `define_language!` now support variants with data _and_ children.
- Added a tutorial in the documentation!

### Fixed
- Fixed a bug when making `Pattern`s from `RecExpr`s.
- Improved the `RecExpr` API.

## [0.5.0] - 2020-06-22

### Added
- `egg` now provides `Symbol`s, a simple interned string that users can (and
  should) use in their `Language`s.
- `egg` will now warn you when you try to use `Rewrite`s with the same name.
- Rewrite creation will now fail if the searcher doesn't bind the right variables.
- The `rewrite!` macro supports bidirectional rewrites now.
- `define_language!` now supports variable numbers of children with `Box<[Id]>`.

### Fixed
- The `rewrite!` macro builds conditional rewrites in the correct order now.

## [0.4.1] - 2020-05-26

### Added
- Added various Debug and Display impls.

### Fixed
- Fixed the way applications were counted by the Runner.

## [0.4.0] - 2020-05-21

### Added
- The rebuilding algorithm is now _precise_ meaning it avoid a lot of
  unnecessary work. This leads to across the board speedup by up to 2x.
- `Language` elements are now much more compact, leading to speed ups across the board.

### Changed
- Replaced `Metadata` with `Analysis`, which can hold egraph-global data as well
  as per-eclass data.
- **Fix:**
  An eclass's metadata will now get updated by
  congruence.
  ([commit](https://github.com/egraphs-good/egg/commit/0de75c9c9b0a80adb67fb78cc98cce3da383621a))
- The `BackoffScheduler` will now fast-forward if all rules are banned.
  ([commit](https://github.com/egraphs-good/egg/commit/dd172ef77279e28448d0bf8147e0171a8175228d))
- Improve benchmark reporting
  ([commit](https://github.com/egraphs-good/egg/commit/ca2ea5e239feda7eb6971942e119075f55f869ab))
- The egraph now skips irrelevant eclasses while searching for a ~40% search speed up.
  ([PR](https://github.com/egraphs-good/egg/pull/21))

## [0.3.0] - 2020-02-27

### Added
- `Runner` can now be configured with user-defined `RewriteScheduler`s
  and `IterationData`.

### Changed
- Reworked the `Runner` API. It's now a generic struct instead of a
  trait.
- Patterns are now compiled into a small virtual machine bytecode inspired
  by [this paper](https://link.springer.com/chapter/10.1007/978-3-540-73595-3_13).
  This gets about a 40% speed up.

## [0.2.0] - 2020-02-19

### Added

- A dumb little benchmarking system called `egg_bench` that can help
  benchmark tests.
- String interning for `Var`s (née `QuestionMarkName`s).
  This speeds up things by ~35%.
- Add a configurable time limit to `SimpleRunner`

### Changed

- Renamed `WildMap` to `Subst`, `QuestionMarkName` to `Var`.

### Removed

- Multi-matching patterns (ex: `?a...`).
  They were a hack and undocumented.
  If we can come up with better way to do it, then we can put them back.

## [0.1.2] - 2020-02-14

This release completes the documentation
(at least every public item is documented).

### Changed
- Replaced `Pattern::{from_expr, to_expr}` with `From` and `TryFrom`
  implementations.

## [0.1.1] - 2020-02-13

### Added
- A lot of documentation

### Changed
- The graphviz visualization now looks a lot better; enode argument
  come out from the "correct" position based on which argument they
  are.

## [0.1.0] - 2020-02-11

This is egg's first real release!

Hard to make a changelog on the first release, since basically
everything has changed!
But hopefully things will be a little more stable from here on out
since the API is a lot nicer.

<!-- next-url -->
[Unreleased]: https://github.com/egraphs-good/egg/compare/v0.10.0...HEAD
[0.10.0]: https://github.com/egraphs-good/egg/compare/v0.9.5...v0.10.0
[0.9.5]: https://github.com/egraphs-good/egg/compare/v0.9.4...v0.9.5
[0.9.4]: https://github.com/egraphs-good/egg/compare/v0.9.3...v0.9.4
[0.9.3]: https://github.com/egraphs-good/egg/compare/v0.9.2...v0.9.3
[0.9.2]: https://github.com/egraphs-good/egg/compare/v0.9.1...v0.9.2
[0.9.1]: https://github.com/egraphs-good/egg/compare/v0.9.0...v0.9.1
[0.9.0]: https://github.com/egraphs-good/egg/compare/v0.8.1...v0.9.0
[0.8.1]: https://github.com/egraphs-good/egg/compare/v0.8.0...v0.8.1
[0.8.0]: https://github.com/egraphs-good/egg/compare/v0.7.1...v0.8.0
[0.7.1]: https://github.com/egraphs-good/egg/compare/v0.7.0...v0.7.1
[0.7.0]: https://github.com/egraphs-good/egg/compare/v0.6.0...v0.7.0
[0.6.0]: https://github.com/egraphs-good/egg/compare/v0.5.0...v0.6.0
[0.5.0]: https://github.com/egraphs-good/egg/compare/v0.4.1...v0.5.0
[0.4.1]: https://github.com/egraphs-good/egg/compare/v0.4.0...v0.4.1
[0.4.0]: https://github.com/egraphs-good/egg/compare/v0.3.0...v0.4.0
[0.3.0]: https://github.com/egraphs-good/egg/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/egraphs-good/egg/compare/v0.1.2...v0.2.0
[0.1.2]: https://github.com/egraphs-good/egg/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/egraphs-good/egg/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/egraphs-good/egg/tree/v0.1.0
