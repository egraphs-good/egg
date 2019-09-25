extern crate libc;

use egg::{
    egraph::{EClass, EGraph},
    expr::{Expr, Language, Name, QuestionMarkName, RecExpr},
    parse::ParsableLanguage,
};

use ordered_float::NotNan;
use strum_macros::{Display, EnumString};

pub type MathEGraph<M = Meta> = egg::egraph::EGraph<Math, M>;

mod rules;
pub use rules::rules;

use std::ffi::CStr;
use std::mem::transmute;
use std::os::raw::c_char;

// I had to add $(rustc --print sysroot)/lib to LD_LIBRARY_PATH to get linking to work after installing rust with rustup
#[no_mangle]
pub unsafe extern "C" fn create_egraph(expr: *const c_char) -> *mut EGraph<Math, ()> {
    let bytes = CStr::from_ptr(expr).to_bytes();
    let expr_string: &str = std::str::from_utf8(bytes).unwrap(); // make sure the bytes are UTF-8

    let start_expr = Math.parse_expr(expr_string).unwrap();
    let (egraph, _root) = EGraph::<Math, ()>::from_expr(&start_expr);

    Box::into_raw(Box::new(egraph))
}

#[no_mangle]
pub unsafe extern "C" fn destroy_egraph(ptr: *mut EGraph<Math, ()>) {
    let _counter: Box<EGraph<Math, ()>> = transmute(ptr);
    // Drop
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Math;

#[derive(Debug, PartialEq, Eq, Hash, Clone, EnumString, Display)]
pub enum Op {
    #[strum(serialize = "+")]
    Add,
    #[strum(serialize = "-")]
    Sub,
    #[strum(serialize = "*")]
    Mul,
    #[strum(serialize = "/")]
    Div,
    #[strum(serialize = "pow")]
    Pow,
    #[strum(serialize = "exp")]
    Exp,
    #[strum(serialize = "log")]
    Log,
    #[strum(serialize = "sqrt")]
    Sqrt,
    #[strum(serialize = "cbrt")]
    Cbrt,
    #[strum(serialize = "fabs")]
    Fabs,
    // #[strum(serialize = "sin")]
    // Sin,
    // #[strum(serialize = "cos")]
    // Cos,
    // #[strum(serialize = "tan")]
    // Tan,
    // #[strum(serialize = "asin")]
    // Asin,
    // #[strum(serialize = "acos")]
    // Acos,
    // #[strum(serialize = "atan")]
    // Atan,
    // #[strum(serialize = "atan2")]
    // Atan2,
    // #[strum(serialize = "sinh")]
    // Sinh,
    // #[strum(serialize = "cosh")]
    // Cosh,
    // #[strum(serialize = "tanh")]
    // Tanh,
    // #[strum(serialize = "asinh")]
    // Asinh,
    // #[strum(serialize = "acosh")]
    // Acosh,
    // #[strum(serialize = "atanh")]
    // Atanh,

    // #[strum(serialize = "fma")]
    // Fma,
    #[strum(serialize = "log1p")]
    Log1p,
    #[strum(serialize = "expm1")]
    Expm1,
    // #[strum(serialize = "hypot")]
    // Hypot,

    // #[strum(serialize = "+.p16")]
    // PositAdd,
    // #[strum(serialize = "-.p16")]
    // PositSub,
    // #[strum(serialize = "*.p16")]
    // PositMul,
    // #[strum(serialize = "/.p16")]
    // PositDiv,
    #[strum(serialize = "real->posit16")]
    RealToPosit,
}

type Constant = NotNan<f64>;

impl Language for Math {
    type Constant = Constant;
    type Operator = Op;
    type Variable = Name;
    type Wildcard = QuestionMarkName;

    fn cost(node: &Expr<Math, u64>) -> u64 {
        match node {
            Expr::Constant(_) | Expr::Variable(_) => 1,
            Expr::Operator(op, child_costs) => {
                let cost = match op {
                    Op::Add => 40,
                    Op::Sub => 40,
                    Op::Mul => 40,
                    Op::Div => 40,
                    Op::Pow => 210,
                    Op::Exp => 70,
                    Op::Log => 70,
                    Op::Sqrt => 40,
                    Op::Cbrt => 80,
                    Op::Fabs => 40,
                    Op::RealToPosit => 0,
                    Op::Expm1 => 70,
                    Op::Log1p => 70,
                };

                cost + child_costs.iter().sum::<u64>()
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Meta {
    pub cost: u64,
    pub best: RecExpr<Math>,
}

fn eval(op: Op, args: &[Constant]) -> Option<Constant> {
    let a = |i| args.get(i).cloned();
    match op {
        Op::Add => Some(a(0)? + a(1)?),
        Op::Sub => Some(a(0)? - a(1)?),
        Op::Mul => Some(a(0)? * a(1)?),
        Op::Div => Some(a(0)? / a(1)?),
        Op::Pow => None, // a(0)?.powf(a(1)?),
        Op::Exp => None, // a(0)?.exp(),
        Op::Log => None, // a(0)?.ln(),
        Op::Sqrt => {
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
        // Op::Cbrt => {
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
        Op::Fabs => Some(Constant::new(args[0].abs()).unwrap()),
        Op::RealToPosit => Some(args[0]),
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
        let expr = match expr {
            Expr::Operator(op, args) => {
                let const_args: Option<Vec<Constant>> = args
                    .iter()
                    .map(|meta| match meta.best.as_ref() {
                        Expr::Constant(c) => Some(*c),
                        _ => None,
                    })
                    .collect();

                const_args
                    .and_then(|a| eval(op.clone(), &a))
                    .map(Expr::Constant)
                    .unwrap_or_else(|| Expr::Operator(op, args))
            }
            expr => expr,
        };

        let best: RecExpr<_> = expr.map_children(|c| c.best.clone()).into();
        Self {
            best,
            cost: Math::cost(&expr.map_children(|c| c.cost)),
        }
    }

    fn modify(eclass: &mut EClass<Math, Self>) {
        match &eclass.metadata.best.as_ref() {
            // NOTE pruning vs not pruning is decided right here
            // Expr::Constant(c) => eclass.nodes.push(Expr::Constant(*c)),
            // Expr::Variable(v) => eclass.nodes.push(Expr::Variable(v.clone())),
            Expr::Constant(c) => eclass.nodes = vec![Expr::Constant(*c)],
            Expr::Variable(v) => eclass.nodes = vec![Expr::Variable(v.clone())],
            _ => (),
        }
    }
}
