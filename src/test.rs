/*! Utilities for testing / benchmarking egg.

These are not considered part of the public api.
*/

use std::fmt::Display;
use std::io::{self, Write};
use std::process::{Command, Stdio};
use symbolic_expressions::Sexp;

use crate::*;

pub fn env_var<T>(s: &str) -> Option<T>
where
    T: std::str::FromStr,
    T::Err: std::fmt::Debug,
{
    use std::env::VarError;
    match std::env::var(s) {
        Err(VarError::NotPresent) => None,
        Err(VarError::NotUnicode(_)) => panic!("Environment variable {} isn't unicode", s),
        Ok(v) if v.is_empty() => None,
        Ok(v) => match v.parse() {
            Ok(v) => Some(v),
            Err(err) => panic!("Couldn't parse environment variable {}={}, {:?}", s, v, err),
        },
    }
}

fn get_z3_funcs<L>(pattern: &PatternAst<L>) -> HashSet<(String, usize)>
where
    L: Language + Display + 'static,
{
    let mut set: HashSet<(String, usize)> = Default::default();

    for node in pattern.as_ref() {
        if let ENodeOrVar::ENode(node) = node {
            set.insert((node.to_string(), node.children().len()));
        }
    }

    set
}

fn get_all_z3_funcs_consts<L, A>(
    rules: &[Rewrite<L, A>],
    start: &RecExpr<L>,
    goals: &[Pattern<L>],
) -> (Vec<String>, Vec<String>)
where
    L: Language + Display + 'static,
    A: Analysis<L> + Default,
{
    let mut set: HashSet<(String, usize)> = Default::default();

    let mut const_set: HashSet<String> = Default::default();

    for rule in rules {
        set = set
            .union(&get_z3_funcs(rule.searcher.get_pattern_ast().unwrap()))
            .cloned()
            .collect();
        set = set
            .union(&get_z3_funcs(rule.applier.get_pattern_ast().unwrap()))
            .cloned()
            .collect();
    }

    for node in start.as_ref() {
        set.insert((node.to_string(), node.children().len()));
    }

    for goal in goals {
        set = set.union(&get_z3_funcs(&goal.ast)).cloned().collect();
    }

    let mut res = vec!["(declare-fun wrap-int (Int) A)".to_string()];
    let mut consts = vec![];

    for s in set {
        if s.1 > 0 {
            let avec = vec!["A"; s.1];
            res.push(format!("(declare-fun {} ({}) A)", s.0, avec.join(" ")));
        } else {
            if s.0.parse::<i64>().is_err() {
                consts.push(format!("(declare-const {} A)", s.0));
            }
        }
    }

    (res, consts)
}

fn get_const_fold_rewrites() -> Vec<String> {
    let mut res = vec![];

    let ops = vec!["+", "-", "*", "/"];
    for op in ops {
        res.push(format!("(assert (forall ((?x Int) (?y Int)) (= ({} (wrap-int ?x) (wrap-int ?y)) (wrap-int ({} ?x ?y)))))", op, op));
    }
    res
}

fn wrap_ints(sexp: Sexp) -> Sexp {
    match sexp {
        Sexp::List(l) => {
            Sexp::List(l.into_iter().map(wrap_ints).collect())
        }
        Sexp::String(s) => {
            if s.parse::<i64>().is_ok() {
                Sexp::List(vec![Sexp::String("wrap-int".to_string()), Sexp::String(s)])
            } else {
                Sexp::String(s)
            }
        }
        Empty => Empty,
    }
}

fn pat_to_z3_string<L: Language + Display>(pat: &PatternAst<L>) -> String {
    let sexp = pat.to_sexp(usize::from(pat.as_ref().len()-1));
    wrap_ints(sexp).to_string()
}

fn get_z3_rewrites<L, A>(rules: &[Rewrite<L, A>]) -> Vec<String>
where
    L: Language + Display + 'static,
    A: Analysis<L> + Default,
{
    let mut results = get_const_fold_rewrites();
    for rule in rules {
        let left_pat = rule.searcher.get_pattern_ast().unwrap();
        let right_pat = rule.applier.get_pattern_ast().unwrap();
        let left = pat_to_z3_string(left_pat);
        let right = pat_to_z3_string(right_pat);
        let mut vars: HashSet<String> = Default::default();
        for node in left_pat.as_ref() {
            if let ENodeOrVar::Var(v) = node {
                vars.insert(v.to_string());
            }
        }
        for node in right_pat.as_ref() {
            if let ENodeOrVar::Var(v) = node {
                vars.insert(v.to_string());
            }
        }

        let final_str = if vars.len() == 0 {
            format!("(assert (= {} {}))", left, right)
        } else {
            let vars_str = format!(
                "({})",
                vars.iter()
                    .map(|v| format!("({} A)", v))
                    .collect::<Vec<_>>()
                    .join(" ")
            );

            format!("(assert (forall {} (= {} {})))", vars_str, left, right)
        };
        results.push(final_str);
    }

    results
}

fn test_z3<L, A>(rules: &[Rewrite<L, A>], start: RecExpr<L>, goals: &[Pattern<L>])
where
    L: Language + Display + 'static,
    A: Analysis<L> + Default,
{
    let quantified_rewrites = get_z3_rewrites(rules);
    let (funs, consts) = get_all_z3_funcs_consts(rules, &start, goals);
    let current_goal = &goals[0];
    let mut goal_vars: HashSet<String> = Default::default();
    for node in current_goal.ast.as_ref() {
        if let ENodeOrVar::Var(v) = node {
            goal_vars.insert(v.to_string());
        }
    }

    let goal_string = if goal_vars.len() == 0 {
        format!(
            "(assert (not (= {} {})))",
            wrap_ints(start.to_sexp(start.as_ref().len() - 1)),
            pat_to_z3_string(&current_goal.ast)
        )
    } else {
        format!(
            "(assert (forall ({}) (not (= {} {}))))",
            goal_vars
                .iter()
                .map(|v| format!("({} A)", v))
                .collect::<Vec<_>>()
                .join(" "),
            wrap_ints(start.to_sexp(start.as_ref().len() - 1)),
            pat_to_z3_string(&current_goal.ast),
        )
    };

    let mut z3_process = Command::new("z3")
        .arg("-smt2")
        .arg("-in")
        .stdin(Stdio::piped())
        //.stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let z3_input = vec!["(set-option :produce-proofs true)".to_string(),
                    "(declare-sort A)".to_string(),
                    consts.join("\n"),
                    funs.join("\n"),
                    quantified_rewrites.join("\n"),
                    goal_string,
                    "(check-sat)".to_string(),
                    "(get-proof)".to_string(),].join("\n");

                    println!("{}", z3_input);


    let z3_in = z3_process.stdin.as_mut().unwrap();
    z3_in
        .write_all(z3_input.as_bytes())
        .unwrap();

    drop(z3_in);

    z3_process.wait().unwrap();
    //let output = z3_process.wait_with_output().unwrap();
    //println!("Output from z3 = {:?}", output);
}

#[allow(clippy::type_complexity)]
pub fn test_runner<L, A>(
    name: &str,
    runner: Option<Runner<L, A, ()>>,
    rules: &[Rewrite<L, A>],
    start: RecExpr<L>,
    goals: &[Pattern<L>],
    check_fn: Option<fn(Runner<L, A, ()>)>,
    should_check: bool,
) where
    L: Language + Display + 'static,
    A: Analysis<L> + Default,
{
    test_z3(rules, start.clone(), goals);

    let mut runner = runner.unwrap_or_default();

    if let Some(lim) = env_var("EGG_NODE_LIMIT") {
        runner = runner.with_node_limit(lim)
    }
    if let Some(lim) = env_var("EGG_ITER_LIMIT") {
        runner = runner.with_iter_limit(lim)
    }
    if let Some(lim) = env_var("EGG_TIME_LIMIT") {
        runner = runner.with_time_limit(std::time::Duration::from_secs(lim))
    }
    if let Some(is_enabled) = env_var("EGG_TEST_EXPLANATIONS") {
        if is_enabled {
            runner = runner.with_explanations_enabled();
        } else {
            // in case we enabled it in order to add expressions
            runner = runner.with_explanations_disabled();
        }
    } else {
        // in case we enabled it in order to add expressions
        runner = runner.with_explanations_disabled();
    }

    runner = runner.with_expr(&start);
    // NOTE this is a bit of hack, we rely on the fact that the
    // initial root is the last expr added by the runner. We can't
    // use egraph.find_expr(start) because it may have been pruned
    // away
    let id = runner.egraph.find(*runner.roots.last().unwrap());

    if check_fn.is_none() {
        let goals = goals.to_vec();
        runner = runner.with_hook(move |r| {
            if goals
                .iter()
                .all(|g: &Pattern<_>| g.search_eclass(&r.egraph, id).is_some())
            {
                Err("Done".into())
            } else {
                Ok(())
            }
        });
    }
    let mut runner = runner.run(rules);

    if should_check {
        runner.print_report();
        runner.egraph.check_goals(id, &goals);

        if runner.egraph.are_explanations_enabled() && name != "lambda_function_repeat" {
            for goal in goals {
                let matches = goal.search_eclass(&runner.egraph, id).unwrap();
                let subst = matches.substs[0].clone();
                let mut explained = runner.explain_matches(&start, &goal.ast, &subst, 0, false);
                explained.get_sexp_with_let();
                let vanilla_len = explained.get_flat_sexps().len();
                explained.check_proof(rules);
                assert!(explained.get_tree_size() > 0);

                let mut explained_short =
                    runner.explain_matches(&start, &goal.ast, &subst, 4, true);
                explained_short.get_sexp_with_let();
                let short_len = explained_short.get_flat_sexps().len();
                assert!(short_len <= vanilla_len);
                assert!(explained_short.get_tree_size() > 0);
                println!("Unoptimized {} Optimized {}", vanilla_len, short_len);
                explained_short.check_proof(rules);
            }
        }

        if let Some(check_fn) = check_fn {
            check_fn(runner)
        }
    }
}

/// Make a test function
#[macro_export]
macro_rules! test_fn {
    (
        $(#[$meta:meta])*
        $name:ident, $rules:expr,
        $(runner = $runner:expr,)?
        $start:literal
        =>
        $($goal:literal),+ $(,)?
        $(@check $check_fn:expr)?
    ) => {
        mod $name {
            use super::*;
            pub fn run(check: bool) {
                let _ = env_logger::builder().is_test(true).try_init();

                $crate::test::test_runner(
                    stringify!($name),
                    None $(.or(Some($runner)))?,
                    &$rules,
                    $start.parse().unwrap(),
                    &[$( $goal.parse().unwrap() ),+],
                    None $(.or(Some($check_fn)))?,
                    check,
                )
            }

            $(#[$meta])* #[test] fn test() { run(true) }
        }

        pub fn $name() { $name::run(false) }
    };
}
