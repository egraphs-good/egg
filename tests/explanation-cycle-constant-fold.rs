use egg::{Symbol, *};
use std::time::Duration;

define_language! {
    pub enum Math {
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "^" = Pow([Id; 2]),
        Const(u64),
        Var(Symbol),
    }
}

pub type EGraph = egg::EGraph<Math, ConstantFold>;
pub type Rewrite = egg::Rewrite<Math, ConstantFold>;
pub type Runner = egg::Runner<Math, ConstantFold, ()>;

#[derive(Default)]
pub struct ConstantFold;
impl Analysis<Math> for ConstantFold {
    type Data = Option<(i64, PatternAst<Math>)>;

    fn make(egraph: &mut EGraph, enode: &Math) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref().map(|d| d.0);
        Some(match enode {
            Math::Const(c) => (*c as i64, format!("{}", c).parse().unwrap()),
            Math::Add([a, b]) => (
                x(a)? + x(b)?,
                format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Math::Mul([a, b]) => (
                x(a)? * x(b)?,
                format!("(* {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            _ => return None,
        })
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_option(to, from, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let data = egraph[id].data.clone();
        if let Some((c, pat)) = data {
            if egraph.are_explanations_enabled() {
                egraph.union_instantiations(
                    &pat,
                    &format!("{}", c).parse().unwrap(),
                    &Default::default(),
                    "constant_fold".to_string(),
                );
            } else {
                let added = egraph.add(Math::Const(c as u64));
                egraph.union(id, added);
            }
            // to not prune, comment this out
            egraph[id].nodes.retain(|n| n.is_leaf());

            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}

fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(n) = &egraph[subst[var]].data {
            n.0 != 0
        } else {
            true
        }
    }
}

#[test]
fn repro_cycle_existance() {
    let mut rules = vec![
        rewrite!("add_comm";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rewrite!("mul_comm";  "(* ?a ?b)"        => "(* ?b ?a)"),
        rewrite!("mul_zero"; "(* ?a 0)" => "0"),
        rewrite!("recip-mul-div"; "(* ?x (/ 1 ?x))" => "1" if is_not_zero("?x")),
    ];
    rules.extend(rewrite!("add_assoc"; "(+ ?a (+ ?b ?c))" <=> "(+ (+ ?a ?b) ?c)"));
    rules.extend(rewrite!("mul_assoc"; "(* ?a (* ?b ?c))" <=> "(* (* ?a ?b) ?c)"));
    rules.extend(rewrite!("add_zero"; "(+ ?a 0)" <=> "?a"));
    rules.extend(rewrite!("mul_one";  "(* ?a 1)" <=> "?a"));
    rules.extend(rewrite!("distribute"; "(* ?a (+ ?b ?c))" <=> "(+ (* ?a ?b) (* ?a ?c))"));
    rules.extend(rewrite!("div_canon"; "(/ ?a ?b)" <=> "(* ?a (^ ?b -1))" if is_not_zero("?b")));

    let start = "(+ (/ a b) c)".parse().unwrap();
    let end: RecExpr<Math> = "(/ (+ a (* b c)) b)".parse().unwrap();
    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&start)
        .with_expr(&end)
        .with_time_limit(Duration::from_secs(1000000000000))
        .with_iter_limit(6)
        .with_node_limit(usize::MAX)
        .run(&rules);

    println!(
        "{}",
        runner.explain_equivalence(&start, &end).get_flat_string()
    );
}
