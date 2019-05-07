use std::fmt::{self, Debug};
use std::hash::Hash;
use std::rc::Rc;

use crate::unionfind::UnionFind;

pub type Id = u32;

pub type IdNode<L> = Expr<L, Id>;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Expr<L: Language, Child> {
    Constant(L::Constant),
    Variable(L::Variable),
    Operator(L::Operator, Vec<Child>),
}

impl<L: Language, Child> Expr<L, Child> {
    pub fn map_children<Child2>(&self, f: impl FnMut(Child) -> Child2) -> Expr<L, Child2>
    where
        Child: Clone,
    {
        use Expr::*;
        match self {
            Constant(c) => Constant(c.clone()),
            Variable(v) => Variable(v.clone()),
            Operator(op, args) => {
                let args2 = args.iter().cloned().map(f).collect();
                Operator(op.clone(), args2)
            }
        }
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
    pub fn update_ids(&self, unionfind: &UnionFind) -> Self {
        self.map_children(|id| unionfind.just_find(id))
    }
}

pub struct Symbol<'a, L: Language, Child> {
    node: &'a Expr<L, Child>,
}

impl<'a, L: Language, Child> fmt::Display for Symbol<'a, L, Child>
where
    L::Constant: fmt::Display,
    L::Variable: fmt::Display,
    L::Operator: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.node {
            Expr::Variable(v) => write!(f, "{}", v),
            Expr::Constant(c) => write!(f, "{}", c),
            Expr::Operator(op, _) => write!(f, "{}", op),
        }
    }
}

// TODO I think I can remove the requirements on Language itself if I
// manually derive these things for Expr
pub trait Language: Debug + PartialEq + Eq + Hash + Clone {
    type Constant: Debug + PartialEq + Eq + Hash + Clone;
    type Variable: Debug + PartialEq + Eq + Hash + Clone;
    type Operator: Debug + PartialEq + Eq + Hash + Clone;
    type Wildcard: Debug + PartialEq + Eq + Hash + Clone;

    fn cost(node: &Expr<Self, Id>) -> u64;
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Flat<T> {
    pub root: Id,
    pub nodes: Vec<T>,
}

pub type FlatExpr<L> = Flat<Expr<L, Id>>;

impl<T> Default for Flat<T> {
    fn default() -> Self {
        Flat {
            root: 0,
            nodes: Vec::new(),
        }
    }
}

impl<T> Flat<T> {
    pub fn inner_into<T2: From<T>>(self) -> Flat<T2> {
        Flat {
            root: self.root,
            nodes: self.nodes.into_iter().map(T2::from).collect(),
        }
    }

    pub fn add(&mut self, t: T) -> Id {
        let id = self.nodes.len() as Id;
        self.nodes.push(t);
        id
    }

    #[inline(always)]
    pub fn get_node(&self, i: Id) -> &T {
        &self.nodes[i as usize]
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Name(pub Rc<str>);

impl std::str::FromStr for Name {
    type Err = std::convert::Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Name(s.into()))
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

#[cfg(test)]
pub mod tests {

    use super::*;

    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    pub struct TestLang;

    impl Language for TestLang {
        type Constant = i32;
        type Variable = Name;
        type Operator = Name;
        type Wildcard = QuestionMarkName;

        fn cost(node: &Expr<Self, Id>) -> u64 {
            match node {
                Expr::Variable(_) => 1,
                Expr::Constant(_) => 1,
                Expr::Operator(op, _) => match op.as_ref() {
                    "+" => 5,
                    "*" => 50,
                    "/" => 150,
                    _ => 10,
                },
            }
        }
    }

    pub fn var(v: &str) -> Expr<TestLang, Id> {
        Expr::Variable(v.parse().unwrap())
    }

    pub fn op<Child>(o: &str, args: Vec<Child>) -> Expr<TestLang, Child> {
        Expr::Operator(o.parse().unwrap(), args)
    }
}
