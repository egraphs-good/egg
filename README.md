# <img src="doc/egg.svg" alt="egg logo" height="40" align="left"> egg: egraphs good

[![Build Status](https://github.com/mwillsey/egg/workflows/Build%20and%20Test/badge.svg?branch=master)](https://github.com/mwillsey/egg/actions)
[![Crates.io](https://img.shields.io/crates/v/egg.svg)](https://crates.io/crates/egg)
[![Docs.rs](https://docs.rs/egg/badge.svg)](https://docs.rs/egg/)

Check out the [web demo](https://mwillsey.com/stuff/egg) for some quick egraph action.

## Using egg

Add `egg` to your `Cargo.toml` like this:
```toml
[dependencies]
egg = "0.6.0"
```

## Developing

It's written in [Rust](https://www.rust-lang.org/).
Typically, you install Rust using [`rustup`](https://www.rust-lang.org/tools/install).

Run `cargo doc --open` to build and open the documentation in a browser.

Before committing/pushing, make sure to run `make`, which runs all the tests and lints that CI will.

### Tests

You will need [`graphviz`](https://www.graphviz.org/download/) to run the tests.
Running `cargo test` will run the tests.
Some tests may time out; try `cargo test --release` if that happens.

There are a couple interesting tests in the `tests` directory:

- `prop.rs` implements propositional logic and proves some simple
  theorems.
- `math.rs` implements real arithmetic, with a little bit of symbolic differentiation.
- `lambda.rs` implements a small lambda calculus, using `egg` as a partial evaluator.
