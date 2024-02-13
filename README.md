# <img src="doc/egg.svg" alt="egg logo" height="40" align="left"> egg: egraphs good

[![Crates.io](https://img.shields.io/crates/v/egg.svg)](https://crates.io/crates/egg)
[![Released Docs.rs](https://img.shields.io/crates/v/egg?color=blue&label=docs)](https://docs.rs/egg/)
[![Main branch docs](https://img.shields.io/badge/docs-main-blue)](https://egraphs-good.github.io/egg/egg/)
[![Zulip](https://img.shields.io/badge/zulip-join%20chat-blue)](https://egraphs.zulipchat.com)

> Also check out the [egglog](https://github.com/egraphs-good/egglog) 
 system that provides an alternative approach to 
 equality saturation based on Datalog.
 It features a language-based design, incremental execution, and composable analyses.
 See also the [paper](//mwillsey.com/papers/egglog) and the [egglog web demo](https://egraphs-good.github.io/egglog).

Are you using egg?
Please cite using the BibTeX below and
 add your project to the `egg`
 [website](https://github.com/egraphs-good/egraphs-good.github.io)!

<details class="bibtex">
    <summary>BibTeX</summary>
    <code><pre>@article{2021-egg,
  author = {Willsey, Max and Nandi, Chandrakana and Wang, Yisu Remy and Flatt, Oliver and Tatlock, Zachary and Panchekha, Pavel},
  title = {egg: Fast and Extensible Equality Saturation},
  year = {2021},
  issue_date = {January 2021},
  publisher = {Association for Computing Machinery},
  address = {New York, NY, USA},
  volume = {5},
  number = {POPL},
  url = {https://doi.org/10.1145/3434304},
  doi = {10.1145/3434304},
  abstract = {An e-graph efficiently represents a congruence relation over many expressions. Although they were originally developed in the late 1970s for use in automated theorem provers, a more recent technique known as equality saturation repurposes e-graphs to implement state-of-the-art, rewrite-driven compiler optimizations and program synthesizers. However, e-graphs remain unspecialized for this newer use case. Equality saturation workloads exhibit distinct characteristics and often require ad-hoc e-graph extensions to incorporate transformations beyond purely syntactic rewrites.  This work contributes two techniques that make e-graphs fast and extensible, specializing them to equality saturation. A new amortized invariant restoration technique called rebuilding takes advantage of equality saturation's distinct workload, providing asymptotic speedups over current techniques in practice. A general mechanism called e-class analyses integrates domain-specific analyses into the e-graph, reducing the need for ad hoc manipulation.  We implemented these techniques in a new open-source library called egg. Our case studies on three previously published applications of equality saturation highlight how egg's performance and flexibility enable state-of-the-art results across diverse domains.},
  journal = {Proc. ACM Program. Lang.},
  month = jan,
  articleno = {23},
  numpages = {29},
  keywords = {equality saturation, e-graphs}
}
</pre></code>
</details>

Check out the [egg web demo](https://egraphs-good.github.io/egg-web-demo) for some quick e-graph action!

## Using egg

Add `egg` to your `Cargo.toml` like this:
```toml
[dependencies]
egg = "0.9.5"
```

Make sure to compile with `--release` if you are measuring performance!

## Developing

It's written in [Rust](https://www.rust-lang.org/).
Typically, you install Rust using [`rustup`](https://www.rust-lang.org/tools/install).

Run `cargo doc --open` to build and open the documentation in a browser.

Before committing/pushing, make sure to run `make`, 
 which runs all the tests and lints that CI will (including those under feature flags).
This requires the [`cbc`](https://projects.coin-or.org/Cbc) solver
 due to the `lp` feature.

### Tests

Running `cargo test` will run the tests.
Some tests may time out; try `cargo test --release` if that happens.

There are a couple interesting tests in the `tests` directory:

- `prop.rs` implements propositional logic and proves some simple
  theorems.
- `math.rs` implements real arithmetic, with a little bit of symbolic differentiation.
- `lambda.rs` implements a small lambda calculus, using `egg` as a partial evaluator.


### Benchmarking

To get a simple csv of the runtime of each test, you set the environment variable
`EGG_BENCH_CSV` to something to append a row per test to a csv.

Example:
```bash
EGG_BENCH_CSV=math.csv cargo test --test math --release -- --nocapture --test --test-threads=1
```

