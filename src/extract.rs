use std::cmp::Ordering;
use std::fmt::Debug;

use crate::{EClass, EGraph, ENode, Id, Language, RecExpr};

use indexmap::IndexMap;

pub struct Extractor<'a, CF: CostFunction<L>, L: Language, M> {
    cost_function: CF,
    costs: IndexMap<Id, CF::Cost>,
    egraph: &'a EGraph<L, M>,
}

/** A cost function that can be used by an [`Extractor`]

To extract an expression from an [`EGraph`], the [`Extractor`]
requires a cost function to performs its greedy search.
`egg` provides the simple [`AstSize`] and [`AstDepth`] cost functions.

The example below illustrates a silly but realistic example of
implementing a cost function that is essentially AST size weighted by
the operator:
```
use egg::{*, recexpr as r};

type Lang = &'static str;

struct SillyCostFn;
impl CostFunction<Lang> for SillyCostFn {
    type Cost = f64;
    // you're passed in an ENode whose children are costs instead of eclass ids
    fn cost(&mut self, enode: &ENode<Lang, Self::Cost>) -> Self::Cost {
        let op_cost = match enode.op {
            "foo" => 100.0,
            "bar" => 0.7,
            _ => 1.0
        };
        op_cost + enode.children.iter().sum::<f64>()
    }
}

let e: RecExpr<Lang> = r!("+", r!("foo"), r!("bar"), r!("baz"));
assert_eq!(SillyCostFn.cost_rec(&e), 102.7);
assert_eq!(AstSize.cost_rec(&e), 4);
assert_eq!(AstDepth.cost_rec(&e), 2);
```

[`AstSize`]: struct.AstSize.html
[`AstDepth`]: struct.AstDepth.html
[`Extractor`]: struct.Extractor.html
[`EGraph`]: struct.EGraph.html
[`ENode`]: struct.ENode.html
[`cost`]: trait.CostFunction.html#tymethod.cost
[`cost_rec`]: trait.CostFunction.html#tymethod.cost_rec
**/
pub trait CostFunction<L: Language> {
    /// The `Cost` type. It only requires `PartialOrd` so you can use
    /// floating point types, but failed comparisons (`NaN`s) will
    /// result in a panic.
    type Cost: PartialOrd + Debug + Clone;

    /// For this to work properly, your cost function should be
    /// _monotonic_, i.e. [`cost`] should return a `Cost` greater than
    /// any of the child costs of the given [`ENode`].
    fn cost(&mut self, enode: &ENode<L, Self::Cost>) -> Self::Cost;
    fn cost_rec(&mut self, enode: &RecExpr<L>) -> Self::Cost {
        let child_cost = enode.as_ref().map_children(|e| self.cost_rec(&e));
        self.cost(&child_cost)
    }
}

/** A simple [`CostFunction`] that counts total ast size.

```
use egg::{*, recexpr as r};

let e: RecExpr<&str> = r!("+", r!("foo"), r!("bar"), r!("baz"));
assert_eq!(AstSize.cost_rec(&e), 4);
```

[`CostFunction`]: trait.CostFunction.html
**/
pub struct AstSize;
impl<L: Language> CostFunction<L> for AstSize {
    type Cost = usize;
    fn cost(&mut self, enode: &ENode<L, Self::Cost>) -> Self::Cost {
        1 + enode.children.iter().copied().sum::<usize>()
    }
}

/** A simple [`CostFunction`] that counts maximum ast depth.

```
use egg::{*, recexpr as r};

let e: RecExpr<&str> = r!("+", r!("foo"), r!("bar"), r!("baz"));
assert_eq!(AstDepth.cost_rec(&e), 2);
```

[`CostFunction`]: trait.CostFunction.html
**/
pub struct AstDepth;
impl<L: Language> CostFunction<L> for AstDepth {
    type Cost = usize;
    fn cost(&mut self, enode: &ENode<L, Self::Cost>) -> Self::Cost {
        1 + enode.children.iter().copied().max().unwrap_or(0)
    }
}

fn cmp<T: PartialOrd>(a: &Option<T>, b: &Option<T>) -> Ordering {
    // None is high
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Greater,
        (Some(_), None) => Ordering::Less,
        (Some(a), Some(b)) => a.partial_cmp(&b).unwrap(),
    }
}

impl<'a, CF, L, M> Extractor<'a, CF, L, M>
where
    CF: CostFunction<L>,
    L: Language,
{
    pub fn new(egraph: &'a EGraph<L, M>, cost_function: CF) -> Self {
        let costs = IndexMap::default();
        let mut extractor = Extractor {
            costs,
            egraph,
            cost_function,
        };
        extractor.find_costs();

        extractor
    }

    pub fn find_best(&mut self, eclass: Id) -> (CF::Cost, RecExpr<L>) {
        let expr = self.find_best_expr(eclass);
        let cost = self.cost_function.cost_rec(&expr);
        (cost, expr)
    }

    fn find_best_expr(&mut self, eclass: Id) -> RecExpr<L> {
        let eclass = self.egraph.find(eclass);

        let best_node = self.egraph[eclass]
            .iter()
            .min_by(|a, b| {
                let a = self.node_total_cost(a);
                let b = self.node_total_cost(b);
                cmp(&a, &b)
            })
            .expect("eclass shouldn't be empty");

        best_node
            .clone()
            .map_children(|child| self.find_best_expr(child))
            .into()
    }

    fn node_total_cost(&mut self, node: &ENode<L>) -> Option<CF::Cost> {
        let expr = node
            .map_children_result(|id| self.costs.get(&id).cloned().ok_or(()))
            .ok()?;
        Some(self.cost_function.cost(&expr))
    }

    fn find_costs(&mut self) {
        let mut did_something = true;
        while did_something {
            did_something = false;

            for class in self.egraph.classes() {
                let pass = self.make_pass(class);
                match (self.costs.get(&class.id), pass) {
                    (None, Some(cost)) => {
                        self.costs.insert(class.id, cost);
                        did_something = true;
                    }
                    (Some(old), Some(new)) if new < *old => {
                        self.costs.insert(class.id, new);
                        did_something = true;
                    }
                    _ => (),
                }
            }
        }
    }

    fn make_pass(&mut self, eclass: &EClass<L, M>) -> Option<CF::Cost> {
        eclass
            .iter()
            .map(|n| self.node_total_cost(n))
            .min_by(cmp)
            .unwrap()
    }
}
