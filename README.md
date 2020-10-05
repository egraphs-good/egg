# <img src="doc/egg.svg" alt="egg logo" height="40" align="left"> egg: POPL '21 Artifact Evaluation

`egg` is an e-graph library presented in the POPL paper "Fast and Extensible Equality Saturation".
The anonimized name of the library for submission was "Lego".

`egg` is available online in the following ways:

- Source code at [Github](https://github.com/egraphs-good/egg).
- Rust package at [crates.io](https://crates.io/crates/egg).
- Documentation (including [tutorial](https://docs.rs/egg/*/egg/tutorials/index.html)) 
  at [docs.rs](https://docs.rs/egg/) generated from this repository.

This branch of the repository is based off the `0.6.0` release of `egg`, and
this includes additional documentation and scripts needed to reproduce the
claims in the POPL '21 paper.

What follows is documentation specific to artifact evaluation; for more general
usages, please visit one of the above links.

## Installing

If you are using the virtual machine provided to the AEC, 
  you may navigate to `~/egg` in the terminal and skip this section.
  
Otherwise, install the following dependencies and then clone and navigate to this repo:

- [Rust](https://www.rust-lang.org/) 
- `graphviz`
- Python 3 with the `matplotlib`, `numpy`, and `scipy` libraries

## Relevant project layout

Not all the files/folders in this repository are relevant for artifact evalation, 
since this is the actual folder layout for the `egg` project.

Here are the important parts:

- `README.md` is this document.
- `src` contains the source code for `egg`, as well as the unit tests.
- `tests` contains the integration tests, referred to as the "test suite" in the POPL paper.
  There are three test suites.
  - `prop.rs` implements propositional logic and proves some simple
    theorems. These tests are very small, and are not included in the benchmark set.
  - `math.rs` implements "real" arithmetic, with a little bit of symbolic differentiation.
  - `lambda.rs` implements a small lambda calculus, using `egg` as a partial evaluator.
    A slightly-edited version of this source code was presented in the POPL paper.
- `eval` contains the scripts to be run for artifact evaluation.
  These are not present in the main branch of the `egg` repo.
- `data` will contain the output of the eval scripts. 
  This directory is not present initially, it is created by the eval scripts.
  You may delete it at any time and re-run the eval scripts.
    
## Kicking the tires

You can build and run `egg`s test suite by typing `cargo test --release` inside
the `egg` directory.
`cargo` is Rust's build system, and
  the `--release` flag tells Rust to build with optimizations;
  these are necessary to prevent some tests from timing out.

You should see a bunch of passing tests, ending with the documentation tests running 
(all of the code snippets and examples in the [docs](https://docs.rs/egg/) are checked this way).
The final line should look like:

```
test result: ok. 27 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
```

Great, ok now everything is working, let's validate some claims.

## Running the artifact

Running the scripts in the `eval` folder will reproduce the artifact. From the `egg` directory:

```sh
# run the tests as a sanity check
$ cargo test --release

# generate the data by running the egg test suite
# the data goes in the data/ directory
# see bench.sh for more info
$ ./eval/bench.sh

# process the data, generating plots in the data/ directory
# this additionally prints out some summary data
$ ./eval/plot.py
```

## Claims

The core empirical claims made in the paper are all presented in the plots on page 11.

#### Figure 5: Rebuilding is faster than traditional congruence maintenance

Figure 5 shows that our method 
("Rebuilding once per iteration", also just called rebuilding, deferred rebuilding, or "normal" in the plot code)
is faster than the traditional method ("Rebuilding every merge", also called "upward merging").
The measured value is time spent in congruence restoration, as that is the
only part of the greater equality saturation algorithm that is different between the two methods. 

Each point on the plot is a test from the test suite run two times: 
  the x-value is the congruence time using the traditional method,
  and the y-value is the congruence time using our rebuilding method.

Figure 5 should be reproduced at `data/fig5a-speedup.pdf` and `data/fig5b-speedup-log.pdf`.
The takeaway from this figure is the overall shape of the two plots:
  the linear scale simply shows our method is much faster at restoring congruence,
  and the log scale suggests that the multiplicative speedup increases.
The `./eval/plot.py` script will additionally print the overall speedups included the Figure 5 caption. 
  
#### Figure 6: The speedup grows as more rewrites are applied

Figure 6 investigates the claim of super-linear speedup more closely.
Here, easy individual test is plotted as a line.
For each test, equality saturation takes many iterations, applying many rewrites. 
A point on a line shows the relative speedup (of congruence phase of the algorithm)
  of our rebuilding technique vs the traditional approach
  after applying a certain number of rewrites.
For example, consider the right-most dot in the Figure 6 plot (light-blue).
That dot says the test terminated after applying roughly 10^6 rewrites,
  and our technique offered a cumulative 10x speedup over upward-merging.
Tracing that line to the left shows that as the algorithm progresses (and more rewrites are applied),
  the multiplicative speedup grows.
    
Figure 6 should be reproduced at `data/fig6-speedup-iter.pdf`.
The takeaway is the overall shape: the more rewrites that must be applied, the
  greater the speedup from our rebuilding technique.
  
#### Figure 7: Number of calls to `repair` correlates with performance

Our rebuilding technique reduces the number of calls to the `repair` method
(defined in Figure 3) compared to the traditional approach.
Figure 7 aims to show that this metric, 
  the number of calls to `repair`, 
  is a good proxy for overall congruence performance.
  
Figure 7 should be reproduced at `data/fig7-repairs.pdf`.
The plot should visually appear linear. 
Because of the log-log scale, we use Spearman correlation to show that the number of `repair`s 
does indeed correlate with congruence time.
In the paper, Spearman correlation yields r = 0.98 with a p-value of 3.6e-47.
The `./eval/plot.py` will print the result of Spearman correlation.

### Herbie

https://github.com/uwplse/herbie/pull/272
