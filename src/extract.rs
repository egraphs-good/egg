use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::Debug;

use crate::{EClass, EGraph, ENode, Id, Language, RecExpr};

/** Extracting a single [`RecExpr`] from an [`EGraph`].

```
use egg::*;

define_language! {
    enum SimpleLanguage {
        Num(i32),
        Add = "+",
        Mul = "*",
    }
}

let rules: &[Rewrite<SimpleLanguage, ()>] = &[
    rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
    rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),

    rewrite!("add-0"; "(+ ?a 0)" => "?a"),
    rewrite!("mul-0"; "(* ?a 0)" => "0"),
    rewrite!("mul-1"; "(* ?a 1)" => "?a"),
];

let start = "(+ 0 (* 1 10))".parse().unwrap();
let runner = Runner::new().with_expr(&start).run(&rules);
let (egraph, root) = (runner.egraph, runner.roots[0]);

let mut extractor = Extractor::new(&egraph, AstSize);
let (best_cost, best) = extractor.find_best(root);
assert_eq!(best_cost, 1);
assert_eq!(best, "10".parse().unwrap());
```

[`RecExpr`]: struct.RecExpr.html
[`EGraph`]: struct.EGraph.html
**/
pub struct Extractor<'a, CF: CostFunction<L>, L: Language> {
    cost_function: CF,
    costs: HashMap<Id, CF::Cost>,
    egraph: &'a EGraph<L>,
}

/** A cost function that can be used by an [`Extractor`].

To extract an expression from an [`EGraph`], the [`Extractor`]
requires a cost function to performs its greedy search.
`egg` provides the simple [`AstSize`] and [`AstDepth`] cost functions.

The example below illustrates a silly but realistic example of
implementing a cost function that is essentially AST size weighted by
the operator:
```
use egg::{*, recexpr as r};

type Lang = String;

struct SillyCostFn;
impl CostFunction<Lang> for SillyCostFn {
    type Cost = f64;
    // you're passed in an ENode whose children are costs instead of eclass ids
    fn cost(&mut self, enode: &ENode<Lang, Self::Cost>) -> Self::Cost {
        let op_cost = match enode.op.as_ref() {
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
**/
pub trait CostFunction<L: Language> {
    /// The `Cost` type. It only requires `PartialOrd` so you can use
    /// floating point types, but failed comparisons (`NaN`s) will
    /// result in a panic.
    type Cost: PartialOrd + Debug + Clone;

    /// Calculates the cost of an [`ENode`] whose children are `Cost`s.
    ///
    /// For this to work properly, your cost function should be
    /// _monotonic_, i.e. `cost` should return a `Cost` greater than
    /// any of the child costs of the given [`ENode`].
    ///
    /// [`ENode`]: struct.ENode.html
    fn cost(&mut self, enode: &L::ENode, costs: &HashMap<Id, Self::Cost>) -> Self::Cost;

    /// Calculates the total cost of a [`RecExpr`].
    ///
    /// As provided, this just recursively calls `cost` all the way
    /// down the [`RecExpr`].
    ///
    /// [`RecExpr`]: struct.RecExpr.html
    fn cost_rec(&mut self, expr: &RecExpr<L::ENode>) -> Self::Cost {
        let mut costs = HashMap::default();
        for (i, node) in expr.as_ref().iter().enumerate() {
            let cost = self.cost(node, &costs);
            costs.insert(i as Id, cost);
        }
        let last_id = expr.as_ref().len() as Id - 1;
        costs[&last_id].clone()
    }
}

/** A simple [`CostFunction`] that counts total ast size.

```
use egg::{*, recexpr as r};

let e: RecExpr<String> = r!("+", r!("foo"), r!("bar"), r!("baz"));
assert_eq!(AstSize.cost_rec(&e), 4);
```

[`CostFunction`]: trait.CostFunction.html
**/
pub struct AstSize;
impl<L: Language> CostFunction<L> for AstSize {
    type Cost = usize;
    fn cost(&mut self, enode: &L::ENode, costs: &HashMap<Id, Self::Cost>) -> Self::Cost {
        let mut cost = 1;
        enode.for_each(|id| cost += costs[&id]);
        cost
        // 1 + enode.children().iter().map(|id| costs[id]).sum::<usize>()
    }
}

/** A simple [`CostFunction`] that counts maximum ast depth.

```
use egg::{*, recexpr as r};

let e: RecExpr<String> = r!("+", r!("foo"), r!("bar"), r!("baz"));
assert_eq!(AstDepth.cost_rec(&e), 2);
```

[`CostFunction`]: trait.CostFunction.html
**/
pub struct AstDepth;
impl<L: Language> CostFunction<L> for AstDepth {
    type Cost = usize;
    fn cost(&mut self, enode: &L::ENode, costs: &HashMap<Id, Self::Cost>) -> Self::Cost {
        let mut max = 0;
        enode.for_each(|id| max = max.max(costs[&id]));
        max + 1
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

impl<'a, CF, L> Extractor<'a, CF, L>
where
    CF: CostFunction<L>,
    L: Language,
{
    /// Create a new `Extractor` given an `EGraph` and a
    /// `CostFunction`.
    ///
    /// The extraction does all the work on creation, so this function
    /// performs the greedy search for cheapest representative of each
    /// eclass.
    pub fn new(egraph: &'a EGraph<L>, cost_function: CF) -> Self {
        let costs = HashMap::default();
        let mut extractor = Extractor {
            costs,
            egraph,
            cost_function,
        };
        extractor.find_costs();

        extractor
    }

    /// Find the cheapest (lowest cost) represented `RecExpr` in the
    /// given eclass.
    pub fn find_best(&mut self, eclass: Id) -> (CF::Cost, RecExpr<L::ENode>) {
        let mut expr = RecExpr::default();
        self.find_best_rec(&mut expr, eclass);
        let cost = self.cost_function.cost_rec(&expr);
        (cost, expr)
    }

    fn find_best_rec(&mut self, expr: &mut RecExpr<L::ENode>, eclass: Id) -> Id {
        let eclass = self.egraph.find(eclass);

        let best_node = self.egraph[eclass]
            .iter()
            .min_by(|a, b| {
                let a = self.node_total_cost(a);
                let b = self.node_total_cost(b);
                cmp(&a, &b)
            })
            .expect("eclass shouldn't be empty");

        let node = best_node
            .clone()
            .map_children(|child| self.find_best_rec(expr, child));
        expr.add(node)
    }

    fn node_total_cost(&mut self, node: &L::ENode) -> Option<CF::Cost> {
        if node.all(|id| self.costs.contains_key(&id)) {
            Some(self.cost_function.cost(&node, &self.costs))
        } else {
            None
        }
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

    fn make_pass(&mut self, eclass: &EClass<L>) -> Option<CF::Cost> {
        eclass
            .iter()
            .map(|n| self.node_total_cost(n))
            .min_by(cmp)
            .unwrap_or_else(|| panic!("Can't extract, eclass is empty: {:#?}", eclass))
    }
}
