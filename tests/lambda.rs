use egg::{rewrite as rw, *};

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

type EGraph = egg::EGraph<Lambda, ConstantFold>;

#[derive(Default)]
struct ConstantFold;
impl Analysis<Lambda> for ConstantFold {
    type Data = Option<Lambda>;
    fn merge(&self, to: &mut Self::Data, from: Self::Data) -> bool {
        merge_if_different(to, to.clone().or(from))
    }

    fn make(egraph: &EGraph, enode: &Lambda) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.clone();
        match enode {
            Lambda::Num(_) | Lambda::Bool(_) => Some(enode.clone()),
            Lambda::Add([a, b]) => Some(Lambda::Num(x(a)?.num()? + x(b)?.num()?)),
            Lambda::Eq([a, b]) => Some(Lambda::Bool(x(a)? == x(b)?)),
            _ => None,
        }
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data.clone() {
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
    move |egraph, _, subst| egraph[subst[v1]].data.is_some()
}

fn rules() -> Vec<Rewrite<Lambda, ConstantFold>> {
    vec![
        // open term rules
        rw!("if-true";  "(if  true ?then ?else)" => "?then"),
        rw!("if-false"; "(if false ?then ?else)" => "?else"),
        rw!("if-elim1"; "(if (= (var ?x) (var ?y)) ?then ?else)" => "?else" if {
            let thn: Pattern<_> = "(subst (var ?x) ?y ?then)".parse().unwrap();
            let els: Pattern<_> = "(subst (var ?x) ?y ?else)".parse().unwrap();
            ConditionEqual(thn, els)
        }),
        rw!("if-elim2"; "(if (= (var ?x) (var ?y)) ?then ?else)" => "?else" if {
            let thn: Pattern<_> = "(subst (var ?y) ?x ?then)".parse().unwrap();
            let els: Pattern<_> = "(subst (var ?y) ?x ?else)".parse().unwrap();
            ConditionEqual(thn, els)
        }),
        rw!("add-comm";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rw!("add-assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
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
            "(lam ?v2 (subst ?e ?v1 ?body))"
            if is_not_same_var("?v1", "?v2")),
    ]
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
    "(let y 1
     (+ 0 (var y)))",
    "(+ 0 1)",
    "1",
}

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    lambda_capture, rules(),
    "(subst 1 x (lam x (var x)))" => "(lam x 1)"
}

egg::test_fn! {
    lambda_compose, rules(),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let add1 (lam y (+ (var y) 1))
     (app (app (var compose) (var add1)) (var add1))))"
    =>
    "(lam x (+ 1
               (app (lam y (+ 1 (var y)))
                    (var x))))",
    "(lam x (+ (var x) 2))"
}

egg::test_fn! {
    lambda_if_simple, rules(),
    "(if (= 1 1) 7 9)" => "7"
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
