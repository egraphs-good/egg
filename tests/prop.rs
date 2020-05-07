use egg::*;

define_language! {
    enum Prop {
        Bool(bool),
        And = "&",
        Not = "~",
        Or = "|",
        Implies = "->",
        Variable(String),
    }
}

type EGraph = egg::EGraph<Prop, ConstantFold>;

macro_rules! rule {
    ($name:ident, $left:literal, $right:literal) => {
        #[allow(dead_code)]
        fn $name<M: Metadata<Prop>>() -> Rewrite<Prop, M> {
            rewrite!(stringify!($name); $left => $right)
        }
    };
    ($name:ident, $name2:ident, $left:literal, $right:literal) => {
        rule!($name, $left, $right);
        rule!($name2, $right, $left);
    };
}

rule! {def_imply, def_imply_flip,   "(-> ?a ?b)",       "(| (~ ?a) ?b)"          }
rule! {double_neg, double_neg_flip,  "(~ (~ ?a))",       "?a"                     }
rule! {assoc_or,    "(| ?a (| ?b ?c))", "(| (| ?a ?b) ?c)"       }
rule! {dist_and_or, "(& ?a (| ?b ?c))", "(| (& ?a ?b) (& ?a ?c))"}
rule! {dist_or_and, "(| ?a (& ?b ?c))", "(& (| ?a ?b) (| ?a ?c))"}
rule! {comm_or,     "(| ?a ?b)",        "(| ?b ?a)"              }
rule! {comm_and,    "(& ?a ?b)",        "(& ?b ?a)"              }
rule! {lem,         "(| ?a (~ ?a))",    "true"                      }
rule! {or_true,     "(| ?a true)",         "true"                      }
rule! {and_true,    "(& ?a true)",         "?a"                     }
rule! {contrapositive, "(-> ?a ?b)",    "(-> (~ ?b) (~ ?a))"     }
rule! {lem_imply, "(& (-> ?a ?b) (-> (~ ?a) ?c))", "(| ?b ?c)"}

fn prove_something(name: &str, start: &str, rewrites: &[Rewrite<Prop, ()>], goals: &[&str]) {
    let _ = env_logger::builder().is_test(true).try_init();
    println!("Proving {}", name);

    let start_expr: RecExpr<Prop> = start.parse().unwrap();
    let goal_exprs: Vec<RecExpr<Prop>> = goals.iter().map(|g| g.parse().unwrap()).collect();

    let egraph = Runner::new()
        .with_iter_limit(20)
        .with_node_limit(5_000)
        .with_expr(&start_expr)
        .run(rewrites)
        .egraph;

    for (i, (goal_expr, goal_str)) in goal_exprs.iter().zip(goals).enumerate() {
        println!("Trying to prove goal {}: {}", i, goal_str);
        let equivs = egraph.equivs(&start_expr, &goal_expr);
        if equivs.is_empty() {
            panic!("Couldn't prove goal {}: {}", i, goal_str);
        }
    }
}

#[test]
fn prove_contrapositive() {
    let _ = env_logger::builder().is_test(true).try_init();
    let rules = &[def_imply(), def_imply_flip(), double_neg_flip(), comm_or()];
    prove_something(
        "contrapositive",
        "(-> x y)",
        rules,
        &[
            "(-> x y)",
            "(| (~ x) y)",
            "(| (~ x) (~ (~ y)))",
            "(| (~ (~ y)) (~ x))",
            "(-> (~ y) (~ x))",
        ],
    );
}

#[test]
fn prove_chain() {
    let _ = env_logger::builder().is_test(true).try_init();
    let rules = &[
        // rules needed for contrapositive
        def_imply(),
        def_imply_flip(),
        double_neg_flip(),
        comm_or(),
        // and some others
        comm_and(),
        lem_imply(),
    ];
    prove_something(
        "chain",
        "(& (-> x y) (-> y z))",
        rules,
        &[
            "(& (-> x y) (-> y z))",
            "(& (-> (~ y) (~ x)) (-> y z))",
            "(& (-> y z)         (-> (~ y) (~ x)))",
            "(| z (~ x))",
            "(| (~ x) z)",
            "(-> x z)",
        ],
    );
}

type ConstantFold = Option<bool>;

impl Metadata<Prop> for ConstantFold {
    type Error = std::convert::Infallible;
    fn merge(&self, other: &Self) -> Self {
        println!("Merge");
        self.and(*other)
    }
    fn make(egraph: &EGraph, enode: &ENode<Prop>) -> Self {
        let a = |i: usize| egraph[enode.children[i]].metadata;
        let result = match &enode.op {
            Prop::Bool(c) => Some(*c),
            Prop::Variable(_) => None,
            op => Some(match op {
                Prop::And => a(0)? && a(1)?,
                Prop::Or => a(0)? || a(1)?,
                Prop::Implies => a(1)? || !a(0)?,
                Prop::Not => {
                    assert_eq!(enode.children.len(), 1);
                    !a(0)?
                }
                _ => panic!("Unknown op: {:?}", op),
            }),
        };
        println!("Make: {:?} -> {:?}", enode, result);
        result
    }
    fn modify(egraph: &mut EGraph, id: Id) {
        println!("Modifying {}", id);
        if let Some(c) = egraph[id].metadata {
            let const_id = egraph.add(ENode::leaf(Prop::Bool(c)));
            egraph.union(id, const_id);
        }
    }
}

#[test]
fn const_fold() {
    let start = "(| (& false true) (& true false))";
    let start_expr = start.parse().unwrap();
    let end = "false";
    let end_expr = end.parse().unwrap();
    let (mut eg, _) = EGraph::from_expr(&start_expr);
    eg.rebuild();
    assert!(!eg.equivs(&start_expr, &end_expr).is_empty());
}
