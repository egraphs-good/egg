use egg::{
    extract::{CostFunction, Extractor},
    parse::ParsableLanguage,
    pattern::Pattern,
    run::{Runner, SimpleRunner},
};
use std::time::Instant;

use egg_math::{EGraph, Math, MathCostFn};

#[test]
fn associate_adds() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start = "(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))";
    let start_expr = Math::parse_expr(start).unwrap();

    let rules = {
        let all = egg_math::rules();
        let mut r = Vec::new();
        r.extend(all["associativity"].clone());
        r.extend(all["commutativity"].clone());
        r
    };

    // Must specfify the () metadata so pruning doesn't mess us up here
    let egraph: EGraph<()> = SimpleRunner::default()
        .with_iter_limit(7)
        .with_node_limit(8_000)
        .run_expr(start_expr, &rules)
        .0;

    // there are exactly 127 non-empty subsets of 7 things
    assert_eq!(egraph.number_of_classes(), 127);

    egraph.dump_dot("associate.dot");
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
        let start_expr = Math::parse_expr(self.start).unwrap();
        let end_expr = Math::parse_expr(self.end).unwrap();

        let (mut egraph, root) = EGraph::from_expr(&start_expr);
        SimpleRunner::default()
            .with_iter_limit(self.iters)
            .with_node_limit(self.limit)
            .run(&mut egraph, &egg_math::all_rules());

        let (cost, best) = Extractor::new(&egraph, MathCostFn).find_best(root);
        println!("Best ({}): {}", cost, best.to_sexp());

        if best != end_expr {
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
    let start_expr = Math::parse_expr(EXP).unwrap();
    let (mut egraph, root) = EGraph::from_expr(&start_expr);

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

    let other_expr = Math::parse_expr(herbies_result).unwrap();
    println!(
        "Herbie ({}): {}",
        MathCostFn.cost_rec(&other_expr),
        other_expr.to_sexp()
    );

    SimpleRunner::default()
        .with_iter_limit(3)
        .with_node_limit(20_000)
        .run(&mut egraph, &egg_math::all_rules());

    let start_time = Instant::now();
    let (cost, best) = Extractor::new(&egraph, MathCostFn).find_best(root);
    let extract_time = start_time.elapsed();

    println!(
        "Start ({}): {}",
        MathCostFn.cost_rec(&start_expr),
        start_expr.to_sexp()
    );
    println!("Best ({}): {}", cost, best.to_sexp());

    println!("Extract time: {:.4}", extract_time.as_secs_f64());
}
