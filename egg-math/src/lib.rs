extern crate libc;

use std::time::{Instant, Duration};
use log::debug;

use egg::{
    egraph::{EClass, EGraph},
    expr::{Expr, Language, Name, QuestionMarkName, RecExpr},
    parse::ParsableLanguage,
    extract::{Extractor},
    define_term,
};

use ordered_float::NotNan;
pub type MathEGraph<M = Meta> = egg::egraph::EGraph<Math, M>;

mod rules;
pub use rules::rules;


use std::ffi::{CStr, CString};
use std::mem::transmute;
use std::os::raw::c_char;

unsafe fn cstring_to_recexpr(c_string: *const c_char) -> Option<RecExpr<Math>> {
    let bytes = CStr::from_ptr(c_string).to_bytes();
    let string_result = std::str::from_utf8(bytes);
    match string_result {
        Ok(expr_string) =>
        {
            let parse_result = Math::parse_expr(expr_string);
            match parse_result {
                Ok(rec_expr) => Some(rec_expr),
                Err(error) => None,
            }
        },
        Err(error) => None,
    }
}

// I had to add $(rustc --print sysroot)/lib to LD_LIBRARY_PATH to get linking to work after installing rust with rustup
#[no_mangle]
pub unsafe extern "C" fn egraph_create(expr: *const c_char) -> *mut EGraph<Math, Meta> {
    let egraph : EGraph<Math, Meta> = Default::default();

    Box::into_raw(Box::new(egraph))
}

#[no_mangle]
pub unsafe extern "C" fn egraph_destroy(egraph_ptr: *mut EGraph<Math, Meta>) {
    let _counter: Box<EGraph<Math, Meta>> = transmute(egraph_ptr);
    // Drop
}

// a struct to report failure if the add fails
#[repr(C)]
pub struct EGraphAddResult {
    id: u32,
    successp: bool,
}

#[no_mangle]
pub unsafe extern "C" fn egraph_add_expr(egraph_ptr: *mut EGraph<Math, Meta>, expr: *const c_char) -> *mut EGraphAddResult {
    let mut egraph = &mut *egraph_ptr;
    let parsed_expr = cstring_to_recexpr(expr);

    let result = match parsed_expr {
        Some(rec_expr) => EGraphAddResult{id: egraph.add_expr(&rec_expr),
                                          successp: true},
        None => EGraphAddResult{ id: 0,
                                 successp: false},
    };
    Box::into_raw(Box::new(result))
}

#[no_mangle]
pub unsafe extern "C" fn egraph_run_rules(egraph_ptr: *mut EGraph<Math, Meta>, iters: u32, limit: u32) {
    let mut egraph = &mut *egraph_ptr;
    run_rules(egraph, iters, limit);
}

#[no_mangle]
pub unsafe extern "C" fn egraph_get_simplest(egraph_ptr: *mut EGraph<Math, Meta>, node_id: u32) -> *const c_char {
    let mut egraph = &mut *egraph_ptr;
    let ext = Extractor::new(&egraph);
    let best = ext.find_best(node_id);


    let best_str = CString::new(best.expr.to_sexp().to_string()).unwrap();
    let best_str_pointer = best_str.as_ptr();
    std::mem::forget(best_str);
    best_str_pointer
}

fn print_time(name: &str, duration: Duration) {
    println!(
        "{}: {}.{:06}",
        name,
        duration.as_secs(),
        duration.subsec_micros()
    );
}

fn run_rules(egraph: &mut EGraph<Math, Meta>, iters: u32, limit: u32)
{
    let rules = rules();
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
            let actually_matched = m.apply_with_limit(egraph, limit as usize);
            if egraph.total_size() > limit as usize {
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
        
        print_time("Rebuild time", rebuild_time.elapsed());
    }

    println!("Final size {}", egraph.total_size());

    let rules_time = start_time.elapsed();
    print_time("Rules time", rules_time);

}

type Constant = NotNan<f64>;


define_term! {
    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    pub enum Math {
        Constant(Constant),
        Add = "+",
        Sub = "-",
        Mul = "*",
        Div = "/",
        Pow = "pow",
        Exp = "exp",
        Log = "log",
        Sqrt = "sqrt",
        Cbrt = "cbrt",
        Fabs = "fabs",
        // Sin = "sin",
        // Cos = "cos",
        // Tan = "tan",
        // Asin = "asin",
        // Acos = "acos",
        // Atan = "atan",
        // Atan2 = "atan2",
        // Sinh = "sinh",
        // Cosh = "cosh",
        // Tanh = "tanh",
        // Asinh = "asinh",
        // Acosh = "acosh",
        // Atanh = "atanh",

        // Fma = "fma",
        Log1p = "log1p",
        Expm1 = "expm1",
        // Hypot = "hypot",

        // PositAdd = "+.p16",
        // PositSub = "-.p16",
        // PositMul = "*.p16",
        // PositDiv = "/.p16",
        RealToPosit = "real->posit",
        Variable(Name),
    }
}

impl Language for Math {
    fn cost(&self, children: &[u64]) -> u64 {
        let cost = match self {
            Math::Constant(_) | Math::Variable(_) => 1,
            Math::Add => 40,
            Math::Sub => 40,
            Math::Mul => 40,
            Math::Div => 40,
            Math::Pow => 210,
            Math::Exp => 70,
            Math::Log => 70,
            Math::Sqrt => 40,
            Math::Cbrt => 80,
            Math::Fabs => 40,
            Math::RealToPosit => 0,
            Math::Expm1 => 70,
            Math::Log1p => 70,
        };

        cost + children.iter().sum::<u64>()
    }
}

#[derive(Debug, Clone)]
pub struct Meta {
    pub cost: u64,
    pub best: RecExpr<Math>,
}

fn eval(op: Math, args: &[Constant]) -> Option<Constant> {
    let a = |i| args.get(i).cloned();
    match op {
        Math::Add => Some(a(0)? + a(1)?),
        Math::Sub => Some(a(0)? - a(1)?),
        Math::Mul => Some(a(0)? * a(1)?),
        Math::Div => Some(a(0)? / a(1)?),
        Math::Pow => None, // a(0)?.powf(a(1)?),
        Math::Exp => None, // a(0)?.exp(),
        Math::Log => None, // a(0)?.ln(),
        Math::Sqrt => {
            None
            // unimplemented!()
            // if let Some(sqrt) = args[0].sqrt() {
            //     #[allow(clippy::float_cmp)]
            //     let is_int = sqrt == sqrt.trunc();
            //     if is_int {
            //         sqrt.into()
            //     } else {
            //         None
            //     }
            // } else {
            //     None
            // }
        }
        // Math::Cbrt => {
        //     if let Some(cbrt) = args[0].to_f64().map(f64::cbrt) {
        //         #[allow(clippy::float_cmp)]
        //         let is_int = cbrt == cbrt.trunc();
        //         if is_int {
        //             cbrt.into()
        //         } else {
        //             None
        //         }
        //     } else {
        //         None
        //     }
        // }
        Math::Fabs => Some(Constant::new(args[0].abs()).unwrap()),
        Math::RealToPosit => Some(args[0]),
        _ => None,
    }
}

impl egg::egraph::Metadata<Math> for Meta {
    type Error = std::convert::Infallible;
    fn merge(&self, other: &Self) -> Self {
        if self.cost <= other.cost {
            self.clone()
        } else {
            other.clone()
        }
    }

    fn make(expr: Expr<Math, &Self>) -> Self {
        let expr = {
            let const_args: Option<Vec<Constant>> = expr
                .children
                .iter()
                .map(|meta| match meta.best.as_ref().op {
                    Math::Constant(c) => Some(c),
                    _ => None,
                })
                .collect();

            const_args
                .and_then(|a| eval(expr.op.clone(), &a))
                .map(|c| Expr::unit(Math::Constant(c)))
                .unwrap_or(expr)
        };

        let best: RecExpr<_> = expr.map_children(|c| c.best.clone()).into();
        Self {
            best,
            cost: expr.map_children(|c| c.cost).cost(),
        }
    }

    fn modify(eclass: &mut EClass<Math, Self>) {
        // NOTE pruning vs not pruning is decided right here
        let best = eclass.metadata.best.as_ref();
        if best.children.is_empty() {
            eclass.nodes = vec![Expr::unit(best.op.clone())]
        }
    }
}
