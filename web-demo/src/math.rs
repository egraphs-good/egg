use egg::{
    egraph::{EGraph, Metadata},
    expr::{RecExpr, Expr, Language, Name, QuestionMarkName},
    extract::{calculate_cost, Extractor},
    parse::ParsableLanguage,
    pattern::Rewrite,
    util::HashMap,
};
use log::*;
use ordered_float::NotNan;
use std::time::Instant;

use strum_macros::{Display, EnumString};

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
}

impl Language for Math {
    type Constant = NotNan<f64>;
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
                };
                cost + child_costs.iter().sum::<u64>()
            }
        }
    }

    fn eval(_op: Self::Operator, _args: &[Self::Constant]) -> Self::Constant {
        unimplemented!()
    }
}

#[derive(Debug)]
pub struct BestExpr {
    pub cost: u64,
    pub expr: RecExpr<Math>,
}

impl Metadata<Math> for BestExpr {
    type Error = std::convert::Infallible;
    fn merge(self, other: Self) -> Self {
        if other.cost < self.cost {
            other
        } else {
            self
        }
    }
    fn make(expr: Expr<Math, &Self>) -> Self {
        let cost = match &expr {
            Expr::Constant(_) | Expr::Variable(_) => 1,
            Expr::Operator(op, children) => {
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
                };
                cost + children.iter().map(|best| best.cost).sum::<u64>()
            }
        };

        let expr: RecExpr<Math> = expr.map_children(|b| b.expr.clone()).into();
        BestExpr {cost, expr}
    }
}

pub type MathEGraph = EGraph<Math, BestExpr>;
