use std::cmp::Ordering;
use std::fmt::Debug;

use crate::util::{hashmap_with_capacity, HashMap};
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

**/
#[derive(Debug)]
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

If you'd like to access the [`Analysis`] data or anything else in the e-graph,
you can put a reference to the e-graph in your [`CostFunction`]:

```
# use egg::*;
# type MyAnalysis = ();
struct EGraphCostFn<'a> {
    egraph: &'a EGraph<SymbolLang, MyAnalysis>,
}

impl<'a> CostFunction<SymbolLang> for EGraphCostFn<'a> {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &SymbolLang, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
        // use self.egraph however you want here
        println!("the egraph has {} classes", self.egraph.number_of_classes());
        return 1
    }
}

let mut egraph = EGraph::<SymbolLang, MyAnalysis>::default();
let id = egraph.add_expr(&"(foo bar)".parse().unwrap());
let cost_func = EGraphCostFn { egraph: &egraph };
let mut extractor = Extractor::new(&egraph, cost_func);
let _ = extractor.find_best(id);
```

Note that a particular e-class might occur in an expression multiple times.
This means that pathological, but nevertheless realistic cases
might overflow `usize` if you implement a cost function like [`AstSize`],
even if the actual [`RecExpr`] fits compactly in memory.
You might want to use [`saturating_add`](u64::saturating_add) to
ensure your cost function is still monotonic in this situation.
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
    fn cost_rec(&mut self, expr: &RecExpr<L>) -> Self::Cost {
        let nodes = expr.as_ref();
        let mut costs = hashmap_with_capacity::<Id, Self::Cost>(nodes.len());
        for (i, node) in nodes.iter().enumerate() {
            let cost = self.cost(node, |i| costs[&i].clone());
            costs.insert(Id::from(i), cost);
        }
        let last_id = Id::from(expr.as_ref().len() - 1);
        costs[&last_id].clone()
    }
}

/** A simple [`CostFunction`] that counts total AST size.

```
# use egg::*;
let e: RecExpr<SymbolLang> = "(do_it foo bar baz)".parse().unwrap();
assert_eq!(AstSize.cost_rec(&e), 4);
```

**/
#[derive(Debug)]
pub struct AstSize;
impl<L: Language> CostFunction<L> for AstSize {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &L, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        enode.fold(1, |sum, id| sum.saturating_add(costs(id)))
    }
}

/** A simple [`CostFunction`] that counts maximum AST depth.

```
# use egg::*;
let e: RecExpr<SymbolLang> = "(do_it foo bar baz)".parse().unwrap();
assert_eq!(AstDepth.cost_rec(&e), 2);
```

**/
#[derive(Debug)]
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
        (Some(a), Some(b)) => a.partial_cmp(b).unwrap(),
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
    pub fn find_best(&self, eclass: Id) -> (CF::Cost, RecExpr<L>) {
        let (cost, root) = self.costs[&self.egraph.find(eclass)].clone();
        let expr = root.build_recexpr(|id| self.find_best_node(id).clone());
        (cost, expr)
    }

    /// Find the cheapest e-node in the given e-class.
    pub fn find_best_node(&self, eclass: Id) -> &L {
        &self.costs[&self.egraph.find(eclass)].1
    }

    /// Find the cost of the term that would be extracted from this e-class.
    pub fn find_best_cost(&self, eclass: Id) -> CF::Cost {
        let (cost, _) = &self.costs[&self.egraph.find(eclass)];
        cost.clone()
    }

    fn node_total_cost(&mut self, node: &L) -> Option<CF::Cost> {
        let eg = &self.egraph;
        let has_cost = |id| self.costs.contains_key(&eg.find(id));
        if node.all(has_cost) {
            let costs = &self.costs;
            let cost_f = |id| costs[&eg.find(id)].0.clone();
            Some(self.cost_function.cost(node, cost_f))
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

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn ast_size_overflow() {
        let rules: &[Rewrite<SymbolLang, ()>] =
            &[rewrite!("explode"; "(meow ?a)" => "(meow (meow ?a ?a))")];

        let start = "(meow 42)".parse().unwrap();
        let runner = Runner::default()
            .with_iter_limit(100)
            .with_expr(&start)
            .run(rules);

        let extractor = Extractor::new(&runner.egraph, AstSize);
        let (_, best_expr) = extractor.find_best(runner.roots[0]);
        assert_eq!(best_expr, start);
    }
}
