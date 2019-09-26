use egg::{
    define_term,
    egraph::EGraph,
    expr::{Language, Name},
    parse::ParsableLanguage,
    pattern::Rewrite,
};
use log::*;

define_term! {
    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    enum List {
        Nil = "nil",
        Cons = "cons",
        List = "list",
        Variable(Name),
    }
}

impl Language for List {
    fn cost(&self, _children: &[u64]) -> u64 {
        unimplemented!()
    }
}

macro_rules! rule {
    ($name:ident, $left:expr, $right:expr) => {
        #[allow(dead_code)]
        fn $name() -> Rewrite<List> {
            trace!(
                "Building rule {} ==> {}",
                stringify!($left),
                stringify!($right)
            );
            let rw = List::parse_rewrite(stringify!($name), $left, $right).unwrap();
            println!(
                "Rewrite {{
  name: {},
  lhs: {:?},
  rhs: {:?},
}}",
                rw.name, rw.lhs, rw.rhs
            );
            rw
        }
    };
}

rule! {fold_nil, "nil", "list"}
rule! {fold_cons, "(cons ?a (list ?tail...))", "(list ?a ?tail...)"}

fn prove_something(start: &str, rewrites: &[Rewrite<List>], goals: &[&str]) {
    let _ = env_logger::builder().is_test(true).try_init();

    let start_expr = List::parse_expr(start).unwrap();
    let goal_exprs: Vec<_> = goals.iter().map(|g| List::parse_expr(g).unwrap()).collect();

    let (mut egraph, _old_root) = EGraph::<List, ()>::from_expr(&start_expr);

    for _ in 0..20 {
        for rw in rewrites {
            rw.run(&mut egraph);
        }
        egraph.rebuild();
    }

    for (i, (goal_expr, goal_str)) in goal_exprs.iter().zip(goals).enumerate() {
        info!("Trying to prove goal {}: {}", i, goal_str);
        let equivs = egraph.equivs(&start_expr, &goal_expr);
        if equivs.is_empty() {
            panic!("Couldn't prove goal {}: {}", i, goal_str);
        }
    }
}

#[test]
fn fold_em_up() {
    let rules = &[fold_nil(), fold_cons()];
    prove_something(
        "(cons a (cons b (cons c nil)))",
        rules,
        &[
            "(cons a (cons b (cons c list)))",
            "(cons a (cons b (list c)))",
            "(cons a (list b c))",
            "(list a b c)",
        ],
    );
}
