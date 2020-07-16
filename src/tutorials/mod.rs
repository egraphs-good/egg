// -*- mode: markdown;  markdown-fontify-code-block-default-mode: rustic-mode; -*-
/*!
 
# A Guide-level Explanation of `egg`

`egg` is a e-graph library optimized for equality saturation.
Using these techniques, one can pretty easily build an optimizer or synthesizer for a language.

This tutorial is targeted at readers who may not have seen e-graphs, equality saturation, or Rust.
If you already know some of that stuff, you may just want to skim or skip those chapters.

This is intended to be guide-level introduction using examples to build intuition.
For more detail, check out the [API documentation](../index.html), 
which the tutorials will link to frequently.
Most of the code examples here are typechecked and run, so you may copy-paste them to get started.

There is also a [paper](https://arxiv.org/abs/2004.03082)
describing `egg` and if are keen to read more about its technical novelties.

The tutorials are a work-in-progress with more to be added soon.

*/

pub mod _01_background;
pub mod _02_getting_started;
