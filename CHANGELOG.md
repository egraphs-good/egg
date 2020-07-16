# Changes

<!-- next-header -->

## [Unreleased] - ReleaseDate

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
  ([commit](https://github.com/mwillsey/egg/commit/0de75c9c9b0a80adb67fb78cc98cce3da383621a))
- The `BackoffScheduler` will now fast-forward if all rules are banned.
  ([commit](https://github.com/mwillsey/egg/commit/dd172ef77279e28448d0bf8147e0171a8175228d))
- Improve benchmark reporting
  ([commit](https://github.com/mwillsey/egg/commit/ca2ea5e239feda7eb6971942e119075f55f869ab))
- The egraph now skips irrelevant eclasses while searching for a ~40% search speed up.  
  ([PR](https://github.com/mwillsey/egg/pull/21))

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
[Unreleased]: https://github.com/mwillsey/egg/compare/v0.6.0...HEAD
[0.6.0]: https://github.com/mwillsey/egg/compare/v0.5.0...v0.6.0
[0.5.0]: https://github.com/mwillsey/egg/compare/v0.4.1...v0.5.0
[0.4.1]: https://github.com/mwillsey/egg/compare/v0.4.0...v0.4.1
[0.4.0]: https://github.com/mwillsey/egg/compare/v0.3.0...v0.4.0
[0.3.0]: https://github.com/mwillsey/egg/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/mwillsey/egg/compare/v0.1.2...v0.2.0
[0.1.2]: https://github.com/mwillsey/egg/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/mwillsey/egg/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/mwillsey/egg/tree/v0.1.0
