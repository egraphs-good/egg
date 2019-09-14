use std::fmt;
use std::str::FromStr;

use egg::{
    egraph::EClass,
    expr::{Expr, Language, Name, QuestionMarkName, RecExpr},
};

use ordered_float::NotNan;
pub type MathEGraph<M = Meta> = egg::egraph::EGraph<Math, M>;

mod rules;
pub use rules::rules;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Math;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Term {
    Constant(Constant),
    Variable(Name),
    Add,
    Sub,
    Mul,
    Div,
    Pow,
    Exp,
    Log,
    Sqrt,
    Cbrt,
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
    Log1p,
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
    RealToPosit,
}

type Constant = NotNan<f64>;

type BoxedErr = Box<dyn std::error::Error>;
impl FromStr for Term {
    type Err = BoxedErr;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "+" => Ok(Term::Add),
            "-" => Ok(Term::Sub),
            "*" => Ok(Term::Mul),
            "/" => Ok(Term::Div),
            "pow" => Ok(Term::Pow),
            "exp" => Ok(Term::Exp),
            "log" => Ok(Term::Log),
            "sqrt" => Ok(Term::Sqrt),
            "cbrt" => Ok(Term::Cbrt),
            "fabs" => Ok(Term::Fabs),
            "log1p" => Ok(Term::Log1p),
            "expm1" => Ok(Term::Expm1),
            "real->posit16" => Ok(Term::RealToPosit),
            s => s
                .parse()
                .map(Term::Constant)
                .map_err(BoxedErr::from)
                .or_else(|_| s.parse().map(Term::Variable).map_err(BoxedErr::from)),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Variable(v) => write!(f, "{}", v),
            Term::Constant(c) => write!(f, "{}", c),
            Term::Add => write!(f, "+"),
            Term::Sub => write!(f, "-"),
            Term::Mul => write!(f, "*"),
            Term::Div => write!(f, "/"),
            Term::Pow => write!(f, "pow"),
            Term::Exp => write!(f, "exp"),
            Term::Log => write!(f, "log"),
            Term::Sqrt => write!(f, "sqrt"),
            Term::Cbrt => write!(f, "cbrt"),
            Term::Fabs => write!(f, "fabs"),
            Term::Log1p => write!(f, "log1p"),
            Term::Expm1 => write!(f, "expm1"),
            Term::RealToPosit => write!(f, "real->posit16"),
        }
    }
}

impl Language for Math {
    type Term = Term;
    type Wildcard = QuestionMarkName;

    fn cost(node: &Expr<Math, u64>) -> u64 {
        let cost = match &node.t {
            Term::Constant(_) | Term::Variable(_) => 1,
            Term::Add => 40,
            Term::Sub => 40,
            Term::Mul => 40,
            Term::Div => 40,
            Term::Pow => 210,
            Term::Exp => 70,
            Term::Log => 70,
            Term::Sqrt => 40,
            Term::Cbrt => 80,
            Term::Fabs => 40,
            Term::RealToPosit => 0,
            Term::Expm1 => 70,
            Term::Log1p => 70,
        };

        cost + node.children.iter().sum::<u64>()
    }
}

#[derive(Debug, Clone)]
pub struct Meta {
    pub cost: u64,
    pub best: RecExpr<Math>,
}

fn eval(op: Term, args: &[Constant]) -> Option<Constant> {
    let a = |i| args.get(i).cloned();
    match op {
        Term::Add => Some(a(0)? + a(1)?),
        Term::Sub => Some(a(0)? - a(1)?),
        Term::Mul => Some(a(0)? * a(1)?),
        Term::Div => Some(a(0)? / a(1)?),
        Term::Pow => None, // a(0)?.powf(a(1)?),
        Term::Exp => None, // a(0)?.exp(),
        Term::Log => None, // a(0)?.ln(),
        Term::Sqrt => {
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
        // Term::Cbrt => {
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
        Term::Fabs => Some(Constant::new(args[0].abs()).unwrap()),
        Term::RealToPosit => Some(args[0]),
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
                .map(|meta| match meta.best.as_ref().t {
                    Term::Constant(c) => Some(c.clone()),
                    _ => None,
                })
                .collect();

            const_args
                .and_then(|a| eval(expr.t.clone(), &a))
                .map(|c| Expr::unit(Term::Constant(c)))
                .unwrap_or(expr)
        };

        let best: RecExpr<_> = expr.map_children(|c| c.best.clone()).into();
        Self {
            best,
            cost: Math::cost(&expr.map_children(|c| c.cost)),
        }
    }

    fn modify(eclass: &mut EClass<Math, Self>) {
        // NOTE pruning vs not pruning is decided right here
        let best = eclass.metadata.best.as_ref();
        if best.children.is_empty() {
            eclass.nodes = vec![Expr::unit(best.t.clone())]
        }
    }
}
