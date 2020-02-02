use egg::{rewrite as rw, *};

type EGraph = egg::EGraph<Lang, Meta>;

define_language! {
    enum Lang {
        Bool(bool),
        Num(i32),

        Int = "int",
        Var = "var",

        Add = "+",
        Eq = "=",

        App = "app",
        Lambda = "lam",
        Let = "let",
        Fix = "fix",

        If = "if",

        Subst = "subst",
        String(String),
    }
}

fn rules() -> Vec<Rewrite<Lang, Meta>> {
    vec![
        // open term rules

        // NOTE I can't write a false rule here
        rw!("if-true";  "(if (bool  true) ?then ?else)" => "?then"),
        rw!("if-false"; "(if (bool false) ?then ?else)" => "?else"),
        rw!("add-int"; "(+ (int ?a) (int ?b)))" => "(int (+ ?a ?b))"),
        rw!("eq-int";  "(= (int ?a) (int ?b)))" => "(bool (= ?a ?b))"),
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
        rw!("subst-int";  "(subst ?e ?v (int ?i))"    => "(int ?i)"),
        rw!("subst-bool"; "(subst ?e ?v (bool ?b))"   => "(bool ?b)"),
        rw!("subst-if";
            "(subst ?e ?v (if ?cond ?then ?else))" =>
            "(if (subst ?e ?v ?cond) (subst ?e ?v ?then) (subst ?e ?v ?else))"
        ),
        // NOTE variable substitution has to be done by a dynamic
        // pattern, because it knows that if the two variables aren't
        // equal by name, they never will be because names are
        // unique. Egg doesn't have a way for you to write inequality
        // contraints
        rw!("var-subst";
            "(subst ?e ?v1 (var ?v2))" =>
            { VarSubst {
                e: "?e".parse().unwrap(),
                v1: "?v1".parse().unwrap(),
                v2: "?v2".parse().unwrap(),
                body: None,
            } }
        ),
        rw!("var-subst";
            "(subst ?e ?v1 (lam ?v2 ?body))" =>
            { VarSubst {
                e: "?e".parse().unwrap(),
                v1: "?v1".parse().unwrap(),
                v2: "?v2".parse().unwrap(),
                body: Some("?body".parse().unwrap()),
            } }
        ),
    ]
}

#[derive(Debug)]
struct VarSubst {
    e: QuestionMarkName,
    v1: QuestionMarkName,
    v2: QuestionMarkName,
    body: Option<QuestionMarkName>,
}

impl Applier<Lang, Meta> for VarSubst {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let v1 = map[&self.v1][0];
        let v2 = map[&self.v2][0];
        let e = map[&self.e][0];

        let res = if let Some(body) = &self.body {
            let body = map[body][0];
            // substituting in a lambda
            if v1 == v2 {
                egraph.add(ENode::new(Lang::Lambda, vec![v2, body]))
            } else {
                let sub_body = egraph.add(ENode::new(Lang::Subst, vec![e, v1, body]));
                egraph.add(ENode::new(Lang::Lambda, vec![v2, sub_body.id]))
            }
        } else {
            // substituting for a variable
            if v1 == v2 {
                AddResult {
                    was_there: true,
                    id: e,
                }
            } else {
                egraph.add(ENode::new(Lang::Var, vec![v2]))
            }
        };

        vec![res]
    }
}

#[derive(Debug, Clone)]
struct Meta {
    constant: Option<Lang>,
}

impl Metadata<Lang> for Meta {
    type Error = std::convert::Infallible;
    fn merge(&self, other: &Self) -> Self {
        Meta {
            constant: self.constant.clone().or_else(|| other.constant.clone()),
        }
    }

    fn make(expr: ENode<Lang, &Self>) -> Self {
        use Lang::*;
        let get = |i: usize| expr.children.get(i).and_then(|m| m.constant.clone());
        let constant = match (&expr.op, get(0), get(1)) {
            (Num(i), _, _) => Some(Num(*i)),
            (Add, Some(Num(i1)), Some(Num(i2))) => Some(Num(i1 + i2)),
            (Eq, Some(Num(i1)), Some(Num(i2))) => Some(Bool(i1 == i2)),
            _ => None,
        };
        Meta { constant }
    }

    fn modify(eclass: &mut EClass<Lang, Self>) {
        if let Some(c) = eclass.metadata.constant.clone() {
            eclass.nodes.push(ENode::leaf(c));
        }
    }
}

fn prove_something(start: &str, goals: &[&str]) {
    let _ = env_logger::builder().is_test(true).try_init();

    let start_expr = start.parse().unwrap();
    println!("Start ({}): {}", AstSize.cost_rec(&start_expr), start);

    let goal_exprs: Vec<_> = goals.iter().map(|g| g.parse().unwrap()).collect();

    let (egraph, report) = SimpleRunner::default()
        .with_iter_limit(500)
        .with_node_limit(5_000)
        .run_expr(start_expr.clone(), &rules());

    let (cost, best) = Extractor::new(&egraph, AstSize).find_best(report.initial_expr_eclass);
    println!("End ({}): {}", cost, best.pretty(80));

    for (i, (goal_expr, goal_str)) in goal_exprs.iter().zip(goals).enumerate() {
        println!("Trying to prove goal {}: {}", i, goal_str);
        let equivs = egraph.equivs(&start_expr, &goal_expr);
        if equivs.is_empty() {
            panic!("Couldn't prove goal {}: {}", i, goal_str);
        }
    }
}

#[test]
fn lambda_under() {
    prove_something(
        "(lam x (+ (int 4)
                   (app (lam y (var y))
                        (int 4))))",
        &[
            "(lam x (+ (int 4) (subst (int 4) y (var y))))",
            "(lam x (+ (int 4) (int 4)))",
            "(lam x (int 8)))",
        ],
    );
}

#[test]
fn lambda_let_simple() {
    prove_something(
        "(let x (int 0)
         (let y (int 1)
         (+ (var x) (var y))))",
        &[
            "(let y (int 1)
             (+ (int 0) (var y)))",
            "(+ (int 0) (int 1))",
            "(int 1)",
        ],
    );
}

#[test]
#[should_panic(expected = "Couldn't prove goal 0")]
fn lambda_capture() {
    prove_something("(subst (int 1) x (lam x (var x)))", &["(lam x (int 1))"]);
}

#[test]
fn lambda_compose() {
    prove_something(
        "(let compose (lam f (lam g (lam x (app (var f)
                                           (app (var g) (var x))))))
         (let add1 (lam y (+ (var y) (int 1)))
         (app (app (var compose) (var add1)) (var add1))))",
        &[
            "(lam x (+ (int 1)
                       (app (lam y (+ (int 1) (var y)))
                            (var x))))",
            "(lam x (+ (var x) (int 2)))",
        ],
    );
}

#[test]
fn lambda_if() {
    prove_something(
        "(let zeroone (lam x
           (if (= (var x) (int 0))
               (int 0)
               (int 1)))
         (+ (app (var zeroone) (int 0))
            (app (var zeroone) (int 10))))",
        &[
            "(+
               (if (bool false) (int 0) (int 1))
               (if (bool true) (int 0) (int 1)))",
            "(+ (int 1) (int 0))",
            "(int 1)",
        ],
    );
}

// NOTE, for some reason this breaks the parent pointers version,
// namely it's missing a union (would require more rebuilds)
#[cfg_attr(feature = "parent-pointers", ignore)]
#[test]
fn lambda_fib() {
    prove_something(
        "(let fib (fix fib (lam n
           (if (= (var n) (int 0))
               (int 0)
           (if (= (var n) (int 1))
               (int 1)
           (+ (app (var fib)
                   (+ (var n) (int -1)))
              (app (var fib)
                   (+ (var n) (int -2))))))))
         (app (var fib) (int 4)))",
        &["(int 3)"],
    );
}
