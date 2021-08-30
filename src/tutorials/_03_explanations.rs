// -*- mode: markdown;  markdown-fontify-code-block-default-mode: rustic-mode; evil-shift-width: 2; -*-
/*!

# Explanations

It's often useful to know exactly why two terms are equivalent in
  the egraph.
For example, if you are trying to debug incorrect rules,
  it would be useful to have a trace of rewrites showing how an example
  given bad equivalence was found.
`egg` uses an algorithm adapted from 
  [Proof-Producing Congruence Closure](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.76.1716&rep=rep1&type=pdf)
  in order to generate such [`Explanation`]s between two given terms.

Consider this program, which prints a [`FlatExplanation`] showing how
  `0` can be proven equal to `1`:
```
use egg::{*, rewrite as rw};
let rules: &[Rewrite<SymbolLang, ()>] = &[
    rw!("div-one"; "?x" => "(/ ?x 1)"),
    rw!("unsafe-invert-division"; "(/ ?a ?b)" => "(/ 1 (/ ?b ?a))"),
    rw!("simplify-frac"; "(/ ?a (/ ?b ?c))" => "(/ (* ?a ?c) (* (/ ?b ?c) ?c))"),
    rw!("cancel-denominator"; "(* (/ ?a ?b) ?b)" => "?a"),
    rw!("times-zero"; "(* ?a 0)" => "0"),
];

let start = "0".parse().unwrap();
let end = "1".parse().unwrap();
let mut runner = Runner::default().with_explanations_enabled().with_expr(&start).run(rules);

println!("{}", runner.explain_equivalence(&start, &end).get_flat_string());
```
The output of the program is a series of s-expressions annotated
  with the rewrite being performed:
```text
0
(Rewrite<= times-zero (* (/ 1 0) 0))
(Rewrite=> cancel-denominator 1)
```
At each step, the part of the term being rewritten is annotated
  with the rule being applied.
`Rewrite=>` indicates that the previous term is rewritten to the current term
  and `Rewrite<=` indicates that the current term is rewritten to the previous term.

## [`Tree


[`EGraph`]: super::super::EGraph
[`Runner`]: super::super::Runner
[`Explanation`]: super::super::Explanation
[`with_explanations_enabled`]: super::super::Runner::with_explanations_enabled

*/
