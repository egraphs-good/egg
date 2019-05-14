# egg: egraphs good

[![Build Status](https://travis-ci.com/mwillsey/egg.svg?branch=master)](https://travis-ci.com/mwillsey/egg)

## Developing

It's written in [Rust](https://www.rust-lang.org/).
Typically, you install Rust using [`rustup`](https://www.rust-lang.org/tools/install).

Run `cargo doc --open` to build and open the documentation in a browser.

### Tests

Running `cargo tests` will run the tests.

There are a couple interesting tests in the `tests` directory:

- `prop.rs` implements propositional logic and proves some simple
  theorems.
- `math.rs` implements real arithmetic, with rewrite rules and a test
  case taken from [Herbie](https://github.com/uwplse/herbie).
