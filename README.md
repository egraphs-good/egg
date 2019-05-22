# egg: egraphs good

[![Build Status](https://travis-ci.com/mwillsey/egg.svg?branch=master)](https://travis-ci.com/mwillsey/egg)

Check out the [web demo](https://mwillsey.com/stuff/egg).

## Developing

It's written in [Rust](https://www.rust-lang.org/).
Typically, you install Rust using [`rustup`](https://www.rust-lang.org/tools/install).

Run `cargo doc --open` to build and open the documentation in a browser.

Before committing/pushing, make sure to run `./check.sh`, which runs
all the tests and lints that Travis will.

### Tests

Running `cargo tests` will run the tests.

There are a couple interesting tests in the `tests` directory:

- `prop.rs` implements propositional logic and proves some simple
  theorems.
- `math.rs` implements real arithmetic, with rewrite rules and a test
  case taken from [Herbie](https://github.com/uwplse/herbie).
