// -*- mode: markdown;  markdown-fontify-code-block-default-mode: rustic-mode; evil-shift-width: 2; -*-
/*!

# Concepts: e-graphs and equality saturation

<style> em { display: inline-block } </style>

An _e-graph_ is a data structure that powers the _equality saturation_
optimization technique.

Both e-graphs
(Gregory Nelson's [PhD Thesis](https://courses.cs.washington.edu/courses/cse599f/06sp/papers/NelsonThesis.pdf), 1980)
and equality saturation
([Tate et. al., 2009](https://arxiv.org/abs/1012.1802))
were invented before.
`egg` aims to make them easy, extensible, and efficient.

This tutorial will approach these concepts at a high level.
More detail can be found in our [paper].

## Why any of this?

When building pretty much any tool relating to programming languages,
  you'll typically be working with _terms_ from your language
  (we will use the words _term_, _expression_, and _program_ interchangeably).
You may be trying to:
- Convert a term to a "better", equivalent term (optimization);
- Build a term from scratch according to a specification (synthesis);
- Or show that two terms are equivalent (verification).

_Term rewriting_ is common technique for working with terms
  toward any of these goals.
You start with a term _t_ and a set of rewrites,
  each of which take the form _l → r_.
For each rewrite,
you try to match the pattern _l_ against the term _t_,
  generating a substitution _σ_ at some subterm,
  and then you apply that substitution to the right-hand pattern _r_
  and replace the matching subterm.

For example, consider the term 42 × (7 + 7) and the rewrite _x + x → 2 × x_:
- The left-hand side would match at the subterm 7 + 7,
  generating the substitution _σ_ = {_x_: 7}.
- Applying the substitution gives _r[σ] =_ 2 × 7.
  (_r[σ]_ means apply the substitution _σ_ to _r_)
- Replacing the matched subterm 7 + 7 with _r[σ] =_ 2 × 7 gives the result: 42 × (2 × 7).

One issue with term rewriting
  (and other programming language techniques that involve manipulating terms)
  is the matter of choice.
Rewriting is _destructive_,
  meaning that once you do a rewrite, the initial term is gone.
If you have many rewrites to choose from,
  picking one is like choosing a fork in the road:
  going back and choosing another way is expensive or impossible,
  so you're committed to the path you've chosen.
Furthermore, picking the right rewrite at the right time is very difficult in general;
  sometimes, a choice that seems good locally may be wrong globally.

As an example, a C optimizer would like to rewrite `a * 2` to the cheaper `a << 1`.
But what about `(a * 2) / 2`?
A greedy, local approach will take a "wrong turn" resulting in `(a << 1) / 2`,
  which is better than the input expression
  but hides the fact that we could have canceled the multiplication and division.

There are some techniques to mitigate this
  (backtracking and [value-numbering](https://en.wikipedia.org/wiki/Value_numbering)),
  but fundamentally, the only way around it is to take _all choices at the same time_.
But rewriting is destructive,
  so applying _n_ rewrites to a term results in _n_ terms,
  and then applying _n_ rewrites to each of those _n_ terms yields _n_<sup>2</sup> more terms,
  and so on.
If you want to explore _m_ "layers" deep in this tree,
  you'll have to store _n_<sup><i>m</i></sup> terms,
  which is prohibitively expensive.

E-graphs can solve this representation problem.
When rewriting a bunch of terms,
  the results are often structurally similar.
E-graphs can store large sets of similar expressions very compactly.
Using e-graphs,
  you can apply many rewrites simultaneously without a
  multiplicative growth in space.
Equality saturation is a technique to do this kind of rewriting for program
  optimization.

## What's an e-graph?

An _e-graph_ ([/'igraf/][sound]) is a data structure to maintain
  an [equivalence relation]
  (really a [congruence relation], see the [next section](#invariants-and-rebuilding))
  over expressions.
An e-graph is a set of equivalence classes (_e-classes_),
each of which contains equivalent _e-nodes_.
An e-node is an operator with children, but instead of
children being other operators or values, the children are e-classes.
In `egg`, these are represented by the [`EGraph`], [`EClass`], and
[`Language`] (e-nodes) types.

Even small e-graphs can represent a large number of expressions, exponential in
the number of e-nodes.
This compactness is what makes e-graphs a compelling data structure.
We can define what it means for _represent_ (or _contain_) a term as follows:

- An e-graph represents a term if any of its e-classes do.
- An e-class represents a term if any of its e-nodes do.
- An e-node `f(n1, n2, ...)` represents a term `f(t1, t2, ...)` if e-node `ni` represents term `ti`.

Here are some e-graphs.
We picture e-classes as dotted boxes surrounding the equivalent e-nodes.
Note that edges go from e-nodes to e-classes (not to other e-nodes),
  since e-nodes have e-classes as children.
Don't worry about how they are made just yet, we'll get to rewriting soon.

<figure>
<img src="data:image/png;base64,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">
<figcaption style="text-align: center">
  An e-graph as it undergoes a series of rewrites. Gray indicates what didn't change from the previous image.
</figcaption>
</figure>

An e-graph can be queried for patterns through a procedure called _e-matching_
  (matching up to equivalence),
  which searches the e-graph for e-classes that represent terms that match a given pattern.
`egg`'s e-matching
  (inspired by
  [De Moura and Bjørner](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.800.2292&rep=rep1&type=pdf#page=193))
  is done by the [`Searcher`]  and [`Pattern`] APIs.
There are two core operations that modify the e-graph:
  [`add`] which adds e-nodes to the e-graph, and
  [`union`] which merges two e-classes.

These operations can be combined to do rewriting over the e-graph.
Critically, this rewriting process is only additive,
  meaning that the _e-graph never forgets_ old versions of terms.
Additionally, rewrites add entire _classes_ of terms at a time.
To perform a rewrite _l → r_ over an e-graph,
  you first search _l_ in the e-graph, yielding pairs of (_c_, _σ_),
  where _c_ is the matching e-class and _σ_ is the substitution.
Then, you `add` the term _r[σ]_ to the e-graph
  and `union` it with the matching e-class _c_.

Let's put it all together with an example referring to the four e-graphs in the
  image above.

1. The initial e-graph represents the term _(a × 2) / 2_.
   Since each e-class only has one e-node,
     the e-graph is basically an abstract syntax tree
    with sharing (the 2 is not duplicated).
2. Applying the rewrite _x × 2 → x << 1_
   has recorded the fact that _a × 2 = a << 1_
     without forgetting about _a × 2_.
   Note how the newly added _a << 1_ refers to the existing "_a_" e-node,
   and the "<<" e-node has been unioned into the same e-class
   as the equivalent "×" e-node where the pattern _x × 2_ matched.
3. Applying rewrite _(x × y) / z → x × (y / z)_ realizes that division
    associates with multiplication.
   This rewrite is critical to discovering the cancellation of 2s that we are looking for,
     and it still works despite the fact that we applied the "wrong" rewrite previously.
4. Applying rewrites _x / x → 1_ and _1 × x → x_ doesn't add any new e-nodes,
     since all the e-nodes were already present in the e-graph.
   The result only unions e-classes,
     meaning that e-graph actually got _smaller_ from applying these rewrites,
     even though it now represents more terms.
   In fact, observe that that the top-right "×" e-node's left child is _itself_;
     this cycle means the e-class represents the _infinite_ (!) set of terms
     _a_, _a × 1_, _a × 1 × 1_, and so on.

## Invariants and Rebuilding

An e-graph has two core operations that modify the e-graph:
[`add`] which adds e-nodes to the e-graph, and
[`union`] which merges two e-classes.
These operations maintains two key (related) invariants:

1. **Congruence**

   An e-graph maintains not just an [equivalence relation] over
   expressions, but a [congruence relation].
   Congruence basically states that if _x_ is equivalent to _y_,
     _f(x)_ must be equivalent to _f(y)_.
   So as the user calls [`union`], many e-classes other than the given
   two may need to merge to maintain congruence.

   For example, suppose terms _a + x_ and _a + y_ are represented in
   e-classes 1 and 2, respectively.
   At some later point, _x_ and _y_ become
   equivalent (perhaps the user called [`union`] on their containing
   e-classes).
   E-classes 1 and 2 must merge, because now the two "+"
   operators have equivalent arguments, making them equivalent.

2. **Uniqueness of e-nodes**

   There do not exist two distinct e-nodes with the same operators and equivalent
   children in the e-class, either in the same e-class or different e-classes.
   This is maintained in part by the hashconsing performed by [`add`],
   and by deduplication performed by [`union`] and [`rebuild`].

`egg` takes a delayed approach to maintaining these invariants.
Specifically, the effects of calling [`union`] (or applying a rewrite,
which calls [`union`]) may not be reflected immediately.
To restore the e-graph invariants and make these effects visible, the
user *must* call the [`rebuild`] method.

`egg`'s choice here allows for a higher performance implementation
Maintaining the congruence relation complicates the core e-graph data
structure and requires an expensive traversal through the e-graph on
every [`union`].
`egg` chooses to relax these invariants for better performance, only
restoring the invariants on a call to [`rebuild`].
The [paper] on `egg` goes into greater detail on why this design choice makes
  things faster.
See the [`rebuild`] documentation for more information on
  what it does and when you have to call it.
Note also that [`Runner`]s take care of this for you, calling
  [`rebuild`] between rewrite iterations.

## Equality Saturation


Equality saturation
  ([Tate et. al., 2009](https://arxiv.org/abs/1012.1802))
  is a technique for program optimization.
`egg` implements a variant of equality saturation in the [`Runner`] API that
  looks like the following pseudocode:

```ignore
fn equality_saturation(expr: Expression, rewrites: Vec<Rewrite>) -> Expression {
    let mut egraph = make_initial_egraph(expr);

    while !egraph.is_saturated_or_timeout() {
        let mut matches = vec![];

        // read-only phase, invariants are preserved
        for rw in rewrites {
            for (subst, eclass) in egraph.search(rw.lhs) {
                matches.push((rw, subst, eclass));
            }
        }

        // write-only phase, temporarily break invariants
        for (rw, subst, eclass) in matches {
            eclass2 = egraph.add(rw.rhs.subst(subst));
            egraph.union(eclass, eclass2);
        }

        // restore the invariants once per iteration
        egraph.rebuild();
    }

    return egraph.extract_best();
}
```

Most of this was covered above, but we need to define two new terms:

- _Saturation_ occurs when an e-graph detects that rewrites no longer add new information.
  Consider the commutative rewrite _x + y → y + x_.
  After applying it once, the second time adds no new information
    since the e-graph didn't forget about the initial _x + y_ terms.
  If all the rewrites are in this state, we say the e-graph is _saturated_,
    meaning that the e-graph encodes all possible equivalences derivable from
    the given rewrites.
- _Extraction_ is a procedure for picking a single represented from an e-class
  that is optimal according to some cost function.
  `egg`'s [`Extractor`]s provide this functionality.

Put together,
  equality saturation explores all possible variants of a
  program that can be derived from a set of rewrites,
  and then it extracts the best one.
This solves the problem of choice describes above,
  as equality saturation essentially applies every rewrite every iteration,
  using the e-graph to avoid exponential explosion.

It sounds a little too good to be true,
  and while it definitely has its caveats,
  `egg` addresses many of the shortcomings from this approach,
  making it feasible to apply on real-world problems.
We've already discussed how rebuilding makes `egg`'s e-graphs fast,
  and later tutorials will discuss how [`Analysis`] makes this approach flexible
  and able to handle more than just syntactic rewriting.

[`Searcher`]: ../../trait.Searcher.html
[`Pattern`]: ../../struct.Pattern.html
[`EGraph`]: ../../struct.EGraph.html
[`EClass`]: ../../struct.EClass.html
[`Rewrite`]: ../../struct.Rewrite.html
[`Runner`]: ../../struct.Runner.html
[`Extractor`]: ../../struct.Extractor.html
[`Language`]: ../../trait.Language.html
[`Analysis`]: ../../trait.Analysis.html
[`Id`]: ../../type.Id.html
[`add`]: ../../struct.EGraph.html#method.add
[`union`]: ../../struct.EGraph.html#method.union
[`rebuild`]: ../../struct.EGraph.html#method.rebuild
[equivalence relation]: https://en.wikipedia.org/wiki/Equivalence_relation
[congruence relation]: https://en.wikipedia.org/wiki/Congruence_relation
[dot]: ../../struct.Dot.html
[extract]: ../../struct.Extractor.html
[sound]: https://itinerarium.github.io/phoneme-synthesis/?w=/'igraf/
[paper]: https://arxiv.org/abs/2004.03082

*/
