# Changes

<!-- next-header -->

## [Unreleased] - ReleaseDate

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
[Unreleased]: https://github.com/mwillsey/egg/compare/v0.2.0...HEAD
[0.2.0]: https://github.com/mwillsey/egg/compare/v0.1.2...v0.2.0
[0.1.2]: https://github.com/mwillsey/egg/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/mwillsey/egg/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/mwillsey/egg/tree/v0.1.0
