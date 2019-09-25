use egg::{
    define_term,
    egraph::EClass,
    expr::{Expr, Language, Name, RecExpr},
};

use ordered_float::NotNan;
pub type MathEGraph<M = Meta> = egg::egraph::EGraph<Math, M>;

mod rules;
pub use rules::rules;

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
