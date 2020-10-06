# <img src="doc/egg.svg" alt="egg logo" height="40" align="left"> egg: POPL '21 Artifact Evaluation

`egg` is an e-graph library presented in the POPL paper "Fast and Extensible Equality Saturation".
The anonimized name of the library for submission was "Lego".
This is the artifact submitted for [artifact evaluation](https://popl21.sigplan.org/track/POPL-2021-Artifact-Evaluation).

`egg` is available online in the following ways:

- Source code at [Github](https://github.com/egraphs-good/egg).
- Rust package at [crates.io](https://crates.io/crates/egg).
- Documentation (including [tutorial](https://docs.rs/egg/*/egg/tutorials/index.html))
  at [docs.rs](https://docs.rs/egg/) generated from this repository.

[This branch](https://github.com/egraphs-good/egg/tree/popl21)
of the repository is based off the `0.6.0` release of `egg`, and
this includes additional documentation and scripts needed to reproduce the
claims in the POPL '21 paper.

What follows is documentation specific to the "functional" portion of artifact evaluation;
for more general usage, including the "available" or "reusable" criteria,
please visit one of the above links.

## Installing on your own machine

These are these instructions to get started on your own machine.
If you'd like to use a pre-made virtual machine, see the next section.

Evaluating the core artifact requires relatively few dependencies:

- [Rust](https://www.rust-lang.org/)
- `graphviz`
- Python 3 with the `matplotlib`, `numpy`, and `scipy` libraries

Make sure to clone this branch of the repository:
``` sh
$ git clone --branch popl21 https://github.com/egraphs-good/egg
```

## Using the provided virtual machine

You may also use
[this virtual machine](https://drive.google.com/file/d/19OMFirhrwmz4nPx-FZiMu-T8Psk9tVl8)
to view the artifact.
The VM is shipped as a VirtualBox appliance (`.ova` file).
First, [download](https://www.virtualbox.org/wiki/Downloads) VirtualBox 6 for your host machine.
From VirtualBox, you can then import the appliance with `File > Import Appliance`.
Make sure the VM settings are valid for your hardware (check memory, CPU cores etc. in `Settings > System`). 

The VM is running Ubuntu 20.04, the user is `aec`, and the password is `aec`.
All necessary dependencies have already been installed,
  and programs have been pre-compiled.
This repository is already present at `~/egg`; navigate there in the terminal to proceed.
You can perform a `git pull` from that directory to grab the latest verion of this document.

## Relevant project layout

Not all the files/folders in this repository are relevant for artifact evaluation,
since this is the actual folder layout for the `egg` project.

Here are the important parts:

- `README.md` is this document.
- `src` contains the source code for `egg`, as well as the unit tests.
- `tests` contains the integration tests, referred to as the "test suite" in the POPL paper.
  These tests generate the data in Figures 5, 6, and 7.
  - `prop.rs` implements propositional logic and proves some simple
    theorems. These tests are very small, and are not included in the benchmark set run by `bench.sh`.
  - `math.rs` implements "real" arithmetic, with some symbolic differentiation.
  - `lambda.rs` implements a small lambda calculus, using `egg` as a partial evaluator.
    A slightly-edited version of this source code was presented in the POPL paper (Fig. 9 and 10).
- `eval` contains the scripts to be run for artifact evaluation.
  These are not present in the main branch of the `egg` repo.
- `data` contains the output of the eval scripts.
  This is already populated with data generated on a Ryzen 9 3900X CPU.
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

Running the scripts in the `eval` folder will reproduce the artifact.
From the `egg` directory:

```sh
# run the tests as a sanity check
# this may have to compile egg first
# expected time: < 1 min
$ cargo test --release

# generate the data by running the egg test suite
# if there is data already there, this will fail; run `rm -r data/` to proceed
# the data goes in the data/ directory, see bench.sh for more info
# expected time: ~2 hours
$ ./eval/bench.sh

# process the data, generating plots in the data/ directory
# this additionally prints out some summary data
# expected time: < 5 sec
$ ./eval/plot.py

# view the results
$ xdg-open data/
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
Here, each individual test is plotted as a line.
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

#### Section 2.3: Z3 comparison

In Section 2.3, we claim that `egg` is faster that `Z3` on a certain kind of
theorem proving task derived from another research project, TASO (SOSP '19).

To replicate this, you will additionally need `z3`, `protobuf`, and their Python 3
libraries (all pre-installed in the VM).
From the `egg` directory, these steps can replicate the results:

``` sh
# enter the directory containing this part of the eval
$ cd eval/z3-taso-compare

# run the z3-backed verification procedure
# this was pulled straight from the TASO implementation
# make sure to time it, as the performance isn't recorded anywhere
# expected time: 10-30 sec
$ time ./verify.py graph_subst.pb

# now run the egg-backed verification procedure in "batched" mode
# you can un-batch it on line 6 of eval/z3-taso-compare/src/main.rs
# Rust may have to compile first, the tool will print the overall runtime
# expected time: ~1 sec
$ cargo run --release taso_rules.txt
```


### Herbie and other case studies

Replication of the case studies would require extensive source-level
  modifications to projects other than `egg`,
and thus are outside the scope of this artifact.

In the abstract and intro of the POPL submission,
  we claim a 3000x speedup over an older implementation of e-graphs inside
  [Herbie](http://herbie.uwplse.org/).
As part of the camera ready revisions, we will contain discussion of this point into
  Section 6.1 (Case Studies) to better contextualize those speedups.

While this artifact does not include the code to reproduce the Herbie results,
  the logs are in Herbie's nightly reporting system.
Each one of these reports corresponds to a bar in Figure 11, from left to right.
The relevant metric is `simplify` in green:

- initial Racket implementation,
  [83.7 hours](http://herbie.uwplse.org/reports/1593517043:debbie:old-regraph:8ccfdff1f7/timeline.html)
- Racket + batching,
  [49.4 min](http://herbie.uwplse.org/reports/1593526873:debbie:old-regraph:8ccfdff1f7/timeline.html)
- Latest Racket implementation, including batching and rebuilding,
  [22.4 min](http://herbie.uwplse.org/reports/1593539656:debbie:old-regraph:8ccfdff1f7/timeline.html)
- Using `egg`,
  [1.4 min](http://herbie.uwplse.org/reports/1593541610:debbie:old-regraph:8ccfdff1f7/timeline.html)
  (scroll down, `simplify` is not on top)
