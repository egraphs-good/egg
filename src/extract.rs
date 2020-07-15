use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::Debug;

use crate::{Analysis, EClass, EGraph, Id, Language, RecExpr};

/** Extracting a single [`RecExpr`] from an [`EGraph`].

```
use egg::*;

define_language! {
    enum SimpleLanguage {
        Num(i32),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
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
let runner = Runner::default().with_expr(&start).run(rules);
let (egraph, root) = (runner.egraph, runner.roots[0]);

let mut extractor = Extractor::new(&egraph, AstSize);
let (best_cost, best) = extractor.find_best(root);
assert_eq!(best_cost, 1);
assert_eq!(best, "10".parse().unwrap());
```

[`RecExpr`]: struct.RecExpr.html
[`EGraph`]: struct.EGraph.html
**/
pub struct Extractor<'a, CF: CostFunction<L>, L: Language, N: Analysis<L>> {
    cost_function: CF,
    costs: HashMap<Id, (CF::Cost, L)>,
    egraph: &'a EGraph<L, N>,
}

/** A cost function that can be used by an [`Extractor`].

To extract an expression from an [`EGraph`], the [`Extractor`]
requires a cost function to performs its greedy search.
`egg` provides the simple [`AstSize`] and [`AstDepth`] cost functions.

The example below illustrates a silly but realistic example of
implementing a cost function that is essentially AST size weighted by
the operator:
```
# use egg::*;
struct SillyCostFn;
impl CostFunction<SymbolLang> for SillyCostFn {
    type Cost = f64;
    fn cost<C>(&mut self, enode: &SymbolLang, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
        let op_cost = match enode.op.as_str() {
            "foo" => 100.0,
            "bar" => 0.7,
            _ => 1.0
        };
        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

let e: RecExpr<SymbolLang> = "(do_it foo bar baz)".parse().unwrap();
assert_eq!(SillyCostFn.cost_rec(&e), 102.7);
assert_eq!(AstSize.cost_rec(&e), 4);
assert_eq!(AstDepth.cost_rec(&e), 2);
```

[`AstSize`]: struct.AstSize.html
[`AstDepth`]: struct.AstDepth.html
[`Extractor`]: struct.Extractor.html
[`EGraph`]: struct.EGraph.html
**/
pub trait CostFunction<L: Language> {
    /// The `Cost` type. It only requires `PartialOrd` so you can use
    /// floating point types, but failed comparisons (`NaN`s) will
    /// result in a panic.
    type Cost: PartialOrd + Debug + Clone;

    /// Calculates the cost of an enode whose children are `Cost`s.
    ///
    /// For this to work properly, your cost function should be
    /// _monotonic_, i.e. `cost` should return a `Cost` greater than
    /// any of the child costs of the given enode.
    fn cost<C>(&mut self, enode: &L, costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost;

    /// Calculates the total cost of a [`RecExpr`].
    ///
    /// As provided, this just recursively calls `cost` all the way
    /// down the [`RecExpr`].
    ///
    /// [`RecExpr`]: struct.RecExpr.html
    fn cost_rec(&mut self, expr: &RecExpr<L>) -> Self::Cost {
        let mut costs: HashMap<Id, Self::Cost> = HashMap::default();
        for (i, node) in expr.as_ref().iter().enumerate() {
            let cost = self.cost(node, |i| costs[&i].clone());
            costs.insert(Id::from(i), cost);
        }
        let last_id = Id::from(expr.as_ref().len() - 1);
        costs[&last_id].clone()
    }
}

/** A simple [`CostFunction`] that counts total ast size.

```
# use egg::*;
let e: RecExpr<SymbolLang> = "(do_it foo bar baz)".parse().unwrap();
assert_eq!(AstSize.cost_rec(&e), 4);
```

[`CostFunction`]: trait.CostFunction.html
**/
pub struct AstSize;
impl<L: Language> CostFunction<L> for AstSize {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &L, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        enode.fold(1, |sum, id| sum + costs(id))
    }
}

/** A simple [`CostFunction`] that counts maximum ast depth.

```
# use egg::*;
let e: RecExpr<SymbolLang> = "(do_it foo bar baz)".parse().unwrap();
assert_eq!(AstDepth.cost_rec(&e), 2);
```

[`CostFunction`]: trait.CostFunction.html
**/
pub struct AstDepth;
impl<L: Language> CostFunction<L> for AstDepth {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &L, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        1 + enode.fold(0, |max, id| max.max(costs(id)))
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

impl<'a, CF, L, N> Extractor<'a, CF, L, N>
where
    CF: CostFunction<L>,
    L: Language,
    N: Analysis<L>,
{
    /// Create a new `Extractor` given an `EGraph` and a
    /// `CostFunction`.
    ///
    /// The extraction does all the work on creation, so this function
    /// performs the greedy search for cheapest representative of each
    /// eclass.
    pub fn new(egraph: &'a EGraph<L, N>, cost_function: CF) -> Self {
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
    pub fn find_best(&mut self, eclass: Id) -> (CF::Cost, RecExpr<L>) {
        let mut expr = RecExpr::default();
        let (_, cost) = self.find_best_rec(&mut expr, eclass);
        (cost, expr)
    }

    fn find_best_rec(&mut self, expr: &mut RecExpr<L>, eclass: Id) -> (Id, CF::Cost) {
        let id = self.egraph.find(eclass);
        let (best_cost, best_node) = match self.costs.get(&id) {
            Some(result) => result.clone(),
            None => panic!("Failed to extract from eclass {}", id),
        };

        let node = best_node.map_children(|child| self.find_best_rec(expr, child).0);
        (expr.add(node), best_cost)
    }

    fn node_total_cost(&mut self, node: &L) -> Option<CF::Cost> {
        let eg = &self.egraph;
        let has_cost = |&id| self.costs.contains_key(&eg.find(id));
        if node.children().iter().all(has_cost) {
            let costs = &self.costs;
            let cost_f = |id| costs[&eg.find(id)].0.clone();
            Some(self.cost_function.cost(&node, cost_f))
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
                    (None, Some(new)) => {
                        self.costs.insert(class.id, new);
                        did_something = true;
                    }
                    (Some(old), Some(new)) if new.0 < old.0 => {
                        self.costs.insert(class.id, new);
                        did_something = true;
                    }
                    _ => (),
                }
            }
        }

        for class in self.egraph.classes() {
            if !self.costs.contains_key(&class.id) {
                log::warn!(
                    "Failed to compute cost for eclass {}: {:?}",
                    class.id,
                    class.nodes
                )
            }
        }
    }

    fn make_pass(&mut self, eclass: &EClass<L, N::Data>) -> Option<(CF::Cost, L)> {
        let (cost, node) = eclass
            .iter()
            .map(|n| (self.node_total_cost(n), n))
            .min_by(|a, b| cmp(&a.0, &b.0))
            .unwrap_or_else(|| panic!("Can't extract, eclass is empty: {:#?}", eclass));
        cost.map(|c| (c, node.clone()))
    }
}
