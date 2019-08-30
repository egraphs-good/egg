use std::fmt::{self, Debug};
use std::hash::Hash;
use std::rc::Rc;

use symbolic_expressions::Sexp;

use crate::unionfind::UnionFind;

pub type Id = u32;

pub type IdNode<L> = Expr<L, Id>;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Expr<L: Language, Child> {
    Constant(L::Constant),
    Variable(L::Variable),
    Operator(L::Operator, Vec<Child>),
}

type Inner<L> = Expr<L, RecExpr<L>>;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct RecExpr<L: Language> {
    rc: Rc<Inner<L>>,
}

impl<L: Language> From<Inner<L>> for RecExpr<L> {
    fn from(inner: Inner<L>) -> Self {
        let rc = Rc::new(inner);
        RecExpr { rc }
    }
}

impl<L: Language> std::borrow::Borrow<Inner<L>> for RecExpr<L> {
    fn borrow(&self) -> &Inner<L> {
        &self.rc
    }
}

impl<L: Language> AsRef<Inner<L>> for RecExpr<L> {
    fn as_ref(&self) -> &Inner<L> {
        &self.rc
    }
}

impl<L: Language> RecExpr<L> {
    pub fn to_sexp(&self) -> Sexp {
        match self.as_ref() {
            Expr::Constant(c) => Sexp::String(c.to_string()),
            Expr::Variable(v) => Sexp::String(v.to_string()),
            Expr::Operator(op, args) => {
                let mut vec: Vec<_> = args.iter().map(Self::to_sexp).collect();
                vec.insert(0, Sexp::String(op.to_string()));
                Sexp::List(vec)
            }
        }
    }
}

impl<L: Language, Child> Expr<L, Child> {
    pub fn var(v: impl Into<L::Variable>) -> Self {
        Expr::Variable(v.into())
    }

    pub fn map_children_result<Child2, F, Error>(&self, f: F) -> Result<Expr<L, Child2>, Error>
    where
        Child: Clone,
        F: FnMut(Child) -> Result<Child2, Error>,
    {
        use Expr::*;
        Ok(match self {
            Constant(c) => Constant(c.clone()),
            Variable(v) => Variable(v.clone()),
            Operator(op, args) => {
                let args2: Result<Vec<_>, Error> = args.iter().cloned().map(f).collect();
                Operator(op.clone(), args2?)
            }
        })
    }

    pub fn map_children<Child2, F>(&self, mut f: F) -> Expr<L, Child2>
    where
        Child: Clone,
        F: FnMut(Child) -> Child2,
    {
        let some_f = |child| Result::<Child2, std::convert::Infallible>::Ok(f(child));
        self.map_children_result(some_f).unwrap()
    }

    pub fn children(&self) -> &[Child] {
        match self {
            Expr::Constant(_) => &[],
            Expr::Variable(_) => &[],
            Expr::Operator(_, args) => args,
        }
    }

    pub fn symbol(&self) -> Symbol<L, Child> {
        Symbol { node: self }
    }
}

impl<L: Language> Expr<L, Id> {
    pub fn update_ids<V>(&self, unionfind: &UnionFind<Id, V>) -> Self {
        self.map_children(|id| unionfind.find(id))
    }
}

pub struct Symbol<'a, L: Language, Child> {
    node: &'a Expr<L, Child>,
}

impl<'a, L: Language, Child> fmt::Display for Symbol<'a, L, Child> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.node {
            Expr::Variable(v) => write!(f, "{}", v),
            Expr::Constant(c) => write!(f, "{}", c),
            Expr::Operator(op, _) => write!(f, "{}", op),
        }
    }
}

/// Trait that wraps up information from the client about the language
/// we're working with.
///
/// [`TestLang`] is provided as a simple implementation.
///
/// TODO I think I can remove the requirements on Language itself if I
/// manually derive these things for Expr
///
/// [`TestLang`]: tests/struct.TestLang.html
pub trait Language: Debug + PartialEq + Eq + Hash + Clone {
    type Constant: Debug + PartialEq + Eq + Hash + Clone + fmt::Display;
    type Variable: Debug + PartialEq + Eq + Hash + Clone + fmt::Display;
    type Operator: Debug + PartialEq + Eq + Hash + Clone + fmt::Display;
    type Wildcard: Debug + PartialEq + Eq + Hash + Clone;

    fn cost(node: &Expr<Self, u64>) -> u64;
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Name(pub Rc<str>);

impl<S: std::borrow::Borrow<str>> From<S> for Name {
    fn from(s: S) -> Self {
        Name(s.borrow().into())
    }
}

impl std::str::FromStr for Name {
    type Err = std::convert::Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.into())
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct QuestionMarkName(pub Rc<str>);

impl std::str::FromStr for QuestionMarkName {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with('?') {
            Ok(QuestionMarkName(s.into()))
        } else {
            Err(format!("'{}' didn't start with a '?'", s))
        }
    }
}

impl fmt::Display for QuestionMarkName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl AsRef<str> for QuestionMarkName {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

pub mod tests {

    use super::*;

    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    pub struct TestLang;

    impl Language for TestLang {
        type Constant = i32;
        type Variable = Name;
        type Operator = Name;
        type Wildcard = QuestionMarkName;

        fn cost(node: &Expr<Self, u64>) -> u64 {
            match node {
                Expr::Variable(_) => 1,
                Expr::Constant(_) => 1,
                Expr::Operator(op, costs) => {
                    let my_costs = match op.as_ref() {
                        "+" => 5,
                        "*" => 50,
                        "/" => 150,
                        _ => 10,
                    };
                    my_costs + costs.iter().sum::<u64>()
                }
            }
        }
    }

    pub fn var<T>(v: &str) -> Expr<TestLang, T> {
        Expr::Variable(v.parse().unwrap())
    }

    pub fn op<Child>(o: &str, args: Vec<Child>) -> Expr<TestLang, Child> {
        Expr::Operator(o.parse().unwrap(), args)
    }
}
