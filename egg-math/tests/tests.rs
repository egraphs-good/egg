use egg::{
    egraph::{EGraph, Metadata},
    extract::{calculate_cost, Extractor},
    parse::ParsableLanguage,
    pattern::Pattern,
};
use log::*;
use std::time::{Duration, Instant};

use egg_math::{Math, Meta};

#[test]
fn associate_adds() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start = "(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))";
    let start_expr = Math.parse_expr(start).unwrap();

    let (mut egraph, _root) = EGraph::<Math, ()>::from_expr(&start_expr);

    let rules = {
        let all = egg_math::rules();
        let mut r = Vec::new();
        r.extend(all["associativity"].clone());
        r.extend(all["commutativity"].clone());
        r
    };

    for _ in 0..4 {
        for rule in &rules {
            rule.run(&mut egraph);
            egraph.rebuild();
        }
    }

    // there are exactly 127 non-empty subsets of 7 things
    assert_eq!(egraph.number_of_classes(), 127);

    egraph.dump_dot("associate.dot");
}

fn print_time(name: &str, duration: Duration) {
    println!(
        "{}: {}.{:06}",
        name,
        duration.as_secs(),
        duration.subsec_micros()
    );
}

fn run_rules<M>(egraph: &mut EGraph<Math, M>, iters: usize, limit: usize) -> Duration
where
    M: Metadata<Math>,
{
    let rules = egg_math::rules();
    let start_time = Instant::now();

    for i in 0..iters {
        println!("\n\nIteration {}\n", i);

        let search_time = Instant::now();

        let mut applied = 0;
        let mut total_matches = 0;
        let mut last_total_matches = 0;
        let mut matches = Vec::new();
        for (_name, list) in rules.iter() {
            for rule in list {
                let ms = rule.search(&egraph);
                if !ms.is_empty() {
                    matches.push(ms);
                }
                // rule.run(&mut egraph);
                // egraph.rebuild();
            }
        }

        print_time("Search time", search_time.elapsed());

        let match_time = Instant::now();

        for m in matches {
            let actually_matched = m.apply_with_limit(egraph, limit);
            if egraph.total_size() > limit {
                panic!("Node limit exceeded. {} > {}", egraph.total_size(), limit);
            }

            applied += actually_matched.len();
            total_matches += m.len();

            // log the growth of the egraph
            if total_matches - last_total_matches > 1000 {
                last_total_matches = total_matches;
                let elapsed = match_time.elapsed();
                debug!(
                    "nodes: {}, eclasses: {}, actual: {}, total: {}, us per match: {}",
                    egraph.total_size(),
                    egraph.number_of_classes(),
                    applied,
                    total_matches,
                    elapsed.as_micros() / total_matches as u128
                );
            }
        }

        print_time("Match time", match_time.elapsed());

        let rebuild_time = Instant::now();
        egraph.rebuild();
        // egraph.prune();
        print_time("Rebuild time", rebuild_time.elapsed());
    }

    println!("Final size {}", egraph.total_size());

    let rules_time = start_time.elapsed();
    print_time("Rules time", rules_time);

    rules_time
}

#[must_use]
struct CheckSimplify {
    start: &'static str,
    end: &'static str,
    iters: usize,
    limit: usize,
}

impl CheckSimplify {
    fn check(self) {
        let _ = env_logger::builder().is_test(true).try_init();
        let start_expr = Math.parse_expr(self.start).unwrap();
        let end_expr = Math.parse_expr(self.end).unwrap();

        let (mut egraph, root) = EGraph::<Math, Meta>::from_expr(&start_expr);
        run_rules(&mut egraph, self.iters, self.limit);

        let ext = Extractor::new(&egraph);
        let best = ext.find_best(root);
        println!("Best ({}): {}", best.cost, best.expr.to_sexp());

        if best.expr != end_expr {
            println!("start: {}", start_expr.to_sexp());
            println!("start: {:?}", start_expr);
            panic!("Could not simplify {} to {}", self.start, self.end);
        }

        // make sure that pattern search also works
        let pattern = Pattern::from_expr(&end_expr);
        let matches = pattern.search_eclass(&egraph, root).unwrap();
        assert!(!matches.mappings.is_empty());
    }
}

#[test]
#[should_panic(expected = "Could not simplify")]
fn does_not_simplify() {
    CheckSimplify {
        start: "(+ x y)",
        end: "(/ x y)",
        iters: 5,
        limit: 1_000,
    }
    .check();
}

#[test]
fn simplifies() {
    CheckSimplify {
        start: r#"
          (/ 1
             (- (/ (+ 1 (sqrt five))
                   2)
                (/ (- 1 (sqrt five))
                   2)))
        "#,
        end: "(/ 1 (sqrt five))",
        iters: 6,
        limit: 75_000,
    }
    .check();
}

#[test]
fn fold_after_rewrite() {
    CheckSimplify {
        start: "
          (+ 1
             (- a
                (* (- 2 1)
                   a)))",
        end: "1",
        iters: 4,
        limit: 10_000,
    }
    .check();
}

static EXP: &str = r#"
(/
 (*
  (*
   (*
    (pow
     (/ 1 (+ 1 (exp (- 0 s))))
     c_p)
    (pow
     (- 1 (/ 1 (+ 1 (exp (- 0 s)))))
     c_n))
   (*
    (pow
     (/ 1 (+ 1 (exp (- 0 s))))
     c_p)
    (pow
     (- 1 (/ 1 (+ 1 (exp (- 0 s)))))
     c_n)))
  (*
   (pow
    (/ 1 (+ 1 (exp (- 0 s))))
    c_p)
   (pow
    (- 1 (/ 1 (+ 1 (exp (- 0 s)))))
    c_n)))
 (*
  (*
   (*
    (pow
     (/ 1 (+ 1 (exp (- 0 t))))
     c_p)
    (pow
     (- 1 (/ 1 (+ 1 (exp (- 0 t)))))
     c_n))
   (*
    (pow
     (/ 1 (+ 1 (exp (- 0 t))))
     c_p)
    (pow
     (- 1 (/ 1 (+ 1 (exp (- 0 t)))))
     c_n)))
  (*
   (pow
    (/ 1 (+ 1 (exp (- 0 t))))
    c_p)
   (pow
    (- 1 (/ 1 (+ 1 (exp (- 0 t)))))
    c_n))))
"#;

#[test]
fn do_something() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start_expr = Math.parse_expr(EXP).unwrap();
    let (mut egraph, root) = EGraph::<Math, Meta>::from_expr(&start_expr);

    let herbies_result = "(*
  (*
   (*
    (/
     (pow (- 1 (/ 1 (+ (exp (- 0 s)) 1))) c_n)
     (pow (- 1 (/ 1 (+ (exp (- 0 t)) 1))) c_n))
    (/ (pow (/ 1 (+ (exp (- 0 s)) 1)) c_p) (pow (/ 1 (+ (exp (- 0 t)) 1)) c_p)))
   (*
    (/
     (pow (- 1 (/ 1 (+ (exp (- 0 s)) 1))) c_n)
     (pow (- 1 (/ 1 (+ (exp (- 0 t)) 1))) c_n))
    (/ (pow (/ 1 (+ (exp (- 0 s)) 1)) c_p) (pow (/ 1 (+ (exp (- 0 t)) 1)) c_p))))
  (*
   (/
    (pow (- 1 (/ 1 (+ (exp (- 0 s)) 1))) c_n)
    (pow (- 1 (/ 1 (+ (exp (- 0 t)) 1))) c_n))
   (/ (pow (/ 1 (+ (exp (- 0 s)) 1)) c_p) (pow (/ 1 (+ (exp (- 0 t)) 1)) c_p))))";

    let other_expr = Math.parse_expr(herbies_result).unwrap();
    println!(
        "Herbie ({}): {}",
        calculate_cost(&other_expr),
        other_expr.to_sexp()
    );

    run_rules(&mut egraph, 3, 20_000);
    let start_time = Instant::now();

    let ext = Extractor::new(&egraph);
    let best = ext.find_best(root);
    let extract_time = start_time.elapsed();

    println!(
        "Start ({}): {}",
        calculate_cost(&start_expr),
        start_expr.to_sexp()
    );
    println!("Best ({}): {}", best.cost, best.expr.to_sexp());

    print_time("Extract time", extract_time);
}
