use egg::{rewrite as rw, *};
use std::collections::HashSet;

define_language! {
    enum Lambda {
        Bool(bool),
        Num(i32),

        "var" = Var(Id),

        "+" = Add([Id; 2]),
        "=" = Eq([Id; 2]),

        "app" = App([Id; 2]),
        "lam" = Lambda([Id; 2]),
        "let" = Let([Id; 3]),
        "fix" = Fix([Id; 2]),

        "if" = If([Id; 3]),

        "subst" = Subst([Id; 3]),
        Symbol(egg::Symbol),
    }
}

impl Lambda {
    fn num(&self) -> Option<i32> {
        match self {
            Lambda::Num(n) => Some(*n),
            _ => None,
        }
    }
}

type EGraph = egg::EGraph<Lambda, LambdaAnalysis>;

#[derive(Default)]
struct LambdaAnalysis;

#[derive(Debug)]
struct Data {
    free: HashSet<Id>,
    constant: Option<Lambda>,
}

fn eval(egraph: &EGraph, enode: &Lambda) -> Option<Lambda> {
    let x = |i: &Id| egraph[*i].data.constant.clone();
    match enode {
        Lambda::Num(_) | Lambda::Bool(_) => Some(enode.clone()),
        Lambda::Add([a, b]) => Some(Lambda::Num(x(a)?.num()? + x(b)?.num()?)),
        Lambda::Eq([a, b]) => Some(Lambda::Bool(x(a)? == x(b)?)),
        _ => None,
    }
}

impl Analysis<Lambda> for LambdaAnalysis {
    type Data = Data;
    fn merge(&self, to: &mut Data, from: Data) -> bool {
        let before_len = to.free.len();
        // to.free.extend(from.free);
        to.free.retain(|i| from.free.contains(i));
        let did_change = before_len != to.free.len();
        if to.constant.is_none() && from.constant.is_some() {
            to.constant = from.constant;
            true
        } else {
            did_change
        }
    }

    fn make(egraph: &EGraph, enode: &Lambda) -> Data {
        let f = |i: &Id| egraph[*i].data.free.iter().cloned();
        let mut free = HashSet::default();
        match enode {
            Lambda::Var(v) => {
                free.insert(*v);
            }
            Lambda::Let([v, a, b]) | Lambda::Subst([a, v, b]) => {
                free.extend(f(b));
                free.remove(v);
                free.extend(f(a));
            }
            Lambda::Lambda([v, a]) | Lambda::Fix([v, a]) => {
                free.extend(f(a));
                free.remove(v);
            }
            _ => enode.for_each(|c| free.extend(&egraph[c].data.free)),
        }
        let constant = eval(egraph, enode);
        Data { constant, free }
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data.constant.clone() {
            let const_id = egraph.add(c);
            egraph.union(id, const_id);
        }
    }
}

fn is_not_same_var(v1: &'static str, v2: &'static str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let v1 = v1.parse().unwrap();
    let v2 = v2.parse().unwrap();
    move |egraph, _, subst| egraph.find(subst[v1]) != egraph.find(subst[v2])
}

fn is_const(v1: &'static str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let v1 = v1.parse().unwrap();
    move |egraph, _, subst| egraph[subst[v1]].data.constant.is_some()
}

fn rules() -> Vec<Rewrite<Lambda, LambdaAnalysis>> {
    vec![
        // open term rules
        rw!("if-true";  "(if  true ?then ?else)" => "?then"),
        rw!("if-false"; "(if false ?then ?else)" => "?else"),
        rw!("if-elim"; "(if (= (var ?x) ?e) ?then ?else)" => "?else"
            if ConditionEqual::parse("(subst ?e ?x ?then)", "(subst ?e ?x ?else)")),
        rw!("add-comm";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rw!("add-assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("eq-comm";   "(= ?a ?b)"        => "(= ?b ?a)"),
        // subst rules
        rw!("fix";     "(fix ?v ?e)"             => "(subst (fix ?v ?e) ?v ?e)"),
        rw!("beta";    "(app (lam ?v ?body) ?e)" => "(subst ?e ?v ?body)"),
        rw!("let-lam"; "(let ?v ?e ?body)"       => "(app (lam ?v ?body) ?e)"),
        rw!("lam-let"; "(app (lam ?v ?body) ?e)" => "(let ?v ?e ?body)"),
        rw!("subst-app";  "(subst ?e ?v (app ?a ?b))" => "(app (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw!("subst-add";  "(subst ?e ?v (+ ?a ?b))"   => "(+ (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw!("subst-eq";   "(subst ?e ?v (= ?a ?b))"   => "(= (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw!("subst-const";
            "(subst ?e ?v ?c)" => "?c" if is_const("?c")),
        rw!("subst-if";
            "(subst ?e ?v (if ?cond ?then ?else))" =>
            "(if (subst ?e ?v ?cond) (subst ?e ?v ?then) (subst ?e ?v ?else))"
        ),
        rw!("subst-var-same"; "(subst ?e ?v1 (var ?v1))" => "?e"),
        rw!("subst-var-diff"; "(subst ?e ?v1 (var ?v2))" => "(var ?v2)"
            if is_not_same_var("?v1", "?v2")),
        rw!("subst-lam-same"; "(subst ?e ?v1 (lam ?v1 ?body))" => "(lam ?v1 ?body)"),
        rw!("subst-lam-diff";
            "(subst ?e ?v1 (lam ?v2 ?body))" =>
            { CaptureAvoid::new(
                "(lam ?v2 (subst ?e ?v1 ?body))",
                "(lam ?fresh (subst ?e ?v1 (subst (var ?fresh) ?v2 ?body)))") }
            if is_not_same_var("?v1", "?v2")),
        rw!("subst-fix-same"; "(subst ?e ?v1 (fix ?v1 ?body))" => "(fix ?v1 ?body)"),
        rw!("subst-fix-diff";
            "(subst ?e ?v1 (fix ?v2 ?body))" =>
            { CaptureAvoid::new(
                "(fix ?v2 (subst ?e ?v1 ?body))",
                "(fix ?fresh (subst ?e ?v1 (subst (var ?fresh) ?v2 ?body)))") }
            if is_not_same_var("?v1", "?v2")),
    ]
}

struct CaptureAvoid {
    fresh: Var,
    v2: Var,
    e: Var,
    if_not_free: Pattern<Lambda>,
    if_free: Pattern<Lambda>,
}

impl CaptureAvoid {
    fn new(if_not_free: &str, if_free: &str) -> Self {
        Self {
            fresh: "?fresh".parse().unwrap(),
            v2: "?v2".parse().unwrap(),
            e: "?e".parse().unwrap(),
            if_not_free: if_not_free.parse().unwrap(),
            if_free: if_free.parse().unwrap(),
        }
    }
}

impl Applier<Lambda, LambdaAnalysis> for CaptureAvoid {
    fn apply_one(&self, egraph: &mut EGraph, eclass: Id, subst: &Subst) -> Vec<Id> {
        let e = subst[self.e];
        let v2 = subst[self.v2];
        let v2_free_in_e = egraph[e].data.free.contains(&v2);
        if v2_free_in_e {
            let mut subst = subst.clone();
            let sym = Lambda::Symbol(format!("_{}", eclass).into());
            subst.insert(self.fresh, egraph.add(sym));
            self.if_free.apply_one(egraph, eclass, &subst)
        } else {
            self.if_not_free.apply_one(egraph, eclass, &subst)
        }
    }
}

egg::test_fn! {
    lambda_under, rules(),
    "(lam x (+ 4
               (app (lam y (var y))
                    4)))"
    =>
    "(lam x (+ 4 (subst 4 y (var y))))",
    "(lam x (+ 4 4))",
    "(lam x 8))",
}

egg::test_fn! {
    lambda_if_elim, rules(),
    "(if (= (var a) (var b))
         (+ (var a) (var a))
         (+ (var a) (var b)))"
    =>
    "(+ (var a) (var b))"
}

egg::test_fn! {
    lambda_let_simple, rules(),
    "(let x 0
     (let y 1
     (+ (var x) (var y))))"
    =>
    "(let ?y 1
     (+ 0 (var ?y)))",
    "(+ 0 1)",
    "1",
}

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    lambda_capture, rules(),
    "(subst 1 x (lam x (var x)))" => "(lam x 1)"
}

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    lambda_capture_free, rules(),
    "(subst (+ (var x) (var x)) y (lam x (var y)))" => "(lam x (+ (var x) (var x)))"
}

egg::test_fn! {
    lambda_compose, rules(),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let add1 (lam y (+ (var y) 1))
     (app (app (var compose) (var add1)) (var add1))))"
    =>
    "(lam ?x (+ 1
                (app (lam ?y (+ 1 (var ?y)))
                     (var ?x))))",
    "(lam ?x (+ (var ?x) 2))"
}

egg::test_fn! {
    lambda_if_simple, rules(),
    "(if (= 1 1) 7 9)" => "7"
}

egg::test_fn! {
    lambda_compose_many, rules(),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let add1 (lam y (+ (var y) 1))
     (app (app (var compose) (var add1))
          (app (app (var compose) (var add1))
               (app (app (var compose) (var add1))
                    (app (app (var compose) (var add1))
                         (app (app (var compose) (var add1))
                              (app (app (var compose) (var add1))
                                   (var add1)))))))))"
    =>
    "(lam ?x (+ (var ?x) 7))"
}

egg::test_fn! {
    lambda_function_repeat, rules(),
    runner = Runner::default()
        .with_time_limit(std::time::Duration::from_secs(20))
        .with_node_limit(100_000)
        .with_iter_limit(60),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let repeat (fix repeat (lam fun (lam n
        (if (= (var n) 0)
            (lam i (var i))
            (app (app (var compose) (var fun))
                 (app (app (var repeat)
                           (var fun))
                      (+ (var n) -1)))))))
     (let add1 (lam y (+ (var y) 1))
     (app (app (var repeat)
               (var add1))
          2))))"
    =>
    "(lam ?x (+ (var ?x) 2))"
}

egg::test_fn! {
    lambda_if, rules(),
    "(let zeroone (lam x
        (if (= (var x) 0)
            0
            1))
        (+ (app (var zeroone) 0)
        (app (var zeroone) 10)))"
    =>
    "(+
        (if false 0 1)
        (if true 0 1))",
    "(+ 1 0)",
    "1",
}

egg::test_fn! {
    lambda_fib, rules(),
    runner = Runner::default().with_iter_limit(60),
    "(let fib (fix fib (lam n
        (if (= (var n) 0)
            0
        (if (= (var n) 1)
            1
        (+ (app (var fib)
                (+ (var n) -1))
            (app (var fib)
                (+ (var n) -2)))))))
        (app (var fib) 4))"
    => "3"
}
