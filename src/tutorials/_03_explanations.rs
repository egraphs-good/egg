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
  `(/ (* (/ 2 3) (/ 3 2)) 1)` can be simplified to `1`:
```
use egg::{*, rewrite as rw};
let rules: &[Rewrite<SymbolLang, ()>] = &[
    rw!("div-one"; "?x" => "(/ ?x 1)"),
    rw!("unsafe-invert-division"; "(/ ?a ?b)" => "(/ 1 (/ ?b ?a))"),
    rw!("simplify-frac"; "(/ ?a (/ ?b ?c))" => "(/ (* ?a ?c) (* (/ ?b ?c) ?c))"),
    rw!("cancel-denominator"; "(* (/ ?a ?b) ?b)" => "?a"),
    rw!("times-zero"; "(* ?a 0)" => "0"),
];

let start = "(/ (* (/ 2 3) (/ 3 2)) 1)".parse().unwrap();
let end = "1".parse().unwrap();
let mut runner = Runner::default().with_explanations_enabled().with_expr(&start).run(rules);

println!("{}", runner.explain_equivalence(&start, &end).get_flat_string());
```

The output of the program is a series of s-expressions annotated
  with the rewrite being performed:
```text
(/ (* (/ 2 3) (/ 3 2)) 1)
(Rewrite<= div-one (* (/ 2 3) (/ 3 2)))
(* (Rewrite=> unsafe-invert-division (/ 1 (/ 3 2))) (/ 3 2))
(Rewrite=> cancel-denominator 1)
```
At each step, the part of the term being rewritten is annotated
  with the rule being applied.
Each term besides the first term has exactly one rewrite annotation.
`Rewrite=>` indicates that the previous term is rewritten to the current term
  and `Rewrite<=` indicates that the current term is rewritten to the previous term.

It turns out that these rules can easily lead to undesirable results in the egraph.
For example, with just `0` as the starting term, the egraph finds that `0` is equivalent
  to `1` within a few iterations.
Here's the flattened explanation that `egg` generates:
```text
0
(Rewrite<= times-zero (* (/ 1 0) 0))
(Rewrite=> cancel-denominator 1)
```

This tells you how the egraph got from `0` to `1`, but it's not clear why.
In fact, normally the rules `times-zero` and `cancel-denominator` are perfectly
  reasonable.
However, in the presence of a division by zero, they lead to arbitrary unions in the egraph.
So the true problem is the presense of the term `(/ 1 0)`.
For these kinds of questions, `egg` provides the `explain_existance` function which can be used to get an explanation
  of why a term exists in the egraph in the first place.


# Explanation Trees

So far we have looked at the [`FlatExplanation`] represenation of explanations because
  they are the most human-readable.
But explanations can also be used for automatic testing or translation validation of egraph results,
  so the flat representation is not always necessary.
In fact, the flattened representation misses the opportunity to share parts of the explanation
  among several different terms.
Egraphs tend to generate explanations with a large amount of duplication of explanations
  from one term to another, making explanation-sharing very important.
To solve this problem, `egg` provides the [`TreeExplanation`] representation.

Here's an example [`TreeExplanation`] in string form:
```text
(+ 1 (- a (* (- 2 1) a)))
 (+
    1
    (Explanation
      (- a (* (- 2 1) a))
      (-
        a
        (Explanation
          (* (- 2 1) a)
          (* (Explanation (- 2 1) (Rewrite=> constant_fold 1)) a)
          (Rewrite=> comm-mul (* a 1))
          (Rewrite<= mul-one a)))
      (Rewrite=> cancel-sub 0)))
 (Rewrite=> constant_fold 1)
```

The big difference between [`FlatExplanation`] and [`TreeExplanation`] is that now
  children of terms can contain explanations themselves.
So a [`TreeTerm`] can have have each of their children be rewritten from an initial term
  to a final term, making the representation more compact.
In addition, the string format supports let bindings in order to allow sharing of explantions:

```text
(let
  (v_0 (- 2 1))
  (let
    (v_1 (- 2 (Explanation v_0 (Rewrite=> constant_fold 1))))
    (Explanation
      (* (- 2 (- 2 1)) (- 2 (- 2 1)))
      (*
        (Explanation (- 2 (- 2 1)) v_1 (Rewrite=> constant_fold 1))
        (Explanation (- 2 (- 2 1)) v_1 (Rewrite=> constant_fold 1)))
      (Rewrite=> constant_fold 1))))
```
As you can see, the let binding allows for sharing the term `v_1`.
There are other duplicate expressions that could be let bound, but are not because
  `egg` only binds shared sub-terms found during the explanation generation process.

Besides the string forms, [`TreeExplanation`] and [`FlatExplanation`] encode the same information
  as Rust objects.
For proof sharing, each `Rc<TreeTerm>` in the [`TreeExplanation`] can be checked for pointer
  equality with other terms.


[`EGraph`]: super::super::EGraph
[`Runner`]: super::super::Runner
[`Explanation`]: super::super::Explanation
[`TreeExplanation`]: super::super::TreeExplanation
[`FlatExplanation`]: super::super::FlatExplanation
[`TreeTerm`]: super::super::TreeTerm
[`with_explanations_enabled`]: super::super::Runner::with_explanations_enabled

*/
