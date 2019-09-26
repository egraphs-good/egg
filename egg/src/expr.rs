use std::fmt::{self, Debug};
use std::hash::Hash;
use std::rc::Rc;

use smallvec::SmallVec;
use symbolic_expressions::Sexp;

use crate::unionfind::UnionFind;

pub type Id = u32;

pub type IdNode<L> = Expr<L, Id>;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Expr<O, Child> {
    pub op: O,
    pub children: SmallVec<[Child; 2]>,
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

impl<L: Language + fmt::Display> RecExpr<L> {
    pub fn to_sexp(&self) -> Sexp {
        let e = self.as_ref();
        let mut vec: Vec<_> = e.children.iter().map(Self::to_sexp).collect();
        let op = Sexp::String(e.op.to_string());
        if vec.is_empty() {
            op
        } else {
            vec.insert(0, op);
            Sexp::List(vec)
        }
    }
}

impl<L: Language, Child> Expr<L, Child> {
    #[inline(always)]
    pub fn unit(op: L) -> Self {
        Expr::new(op, Default::default())
    }

    #[inline(always)]
    pub fn new(op: L, children: SmallVec<[Child; 2]>) -> Self {
        Expr { op, children }
    }

    #[inline(always)]
    pub fn map_children_result<Child2, F, Error>(&self, f: F) -> Result<Expr<L, Child2>, Error>
    where
        Child: Clone,
        F: FnMut(Child) -> Result<Child2, Error>,
    {
        let ch2: Result<SmallVec<_>, Error> = self.children.iter().cloned().map(f).collect();
        Ok(Expr::new(self.op.clone(), ch2?))
    }

    #[inline(always)]
    pub fn map_children<Child2, F>(&self, mut f: F) -> Expr<L, Child2>
    where
        Child: Clone,
        F: FnMut(Child) -> Child2,
    {
        let some_f = |child| Result::<Child2, std::convert::Infallible>::Ok(f(child));
        self.map_children_result(some_f).unwrap()
    }
}

impl<L: Language> Expr<L, Id> {
    pub fn update_ids<V>(&self, unionfind: &UnionFind<Id, V>) -> Self {
        self.map_children(|id| unionfind.find(id))
    }
}

impl<L: Language> Expr<L, u64> {
    pub fn cost(&self) -> u64 {
        self.op.cost(&self.children)
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
pub trait Language: Debug + PartialEq + Eq + Hash + Clone + 'static {
    fn cost(&self, children: &[u64]) -> u64;
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
    use std::fmt;
    use std::str::FromStr;

    #[derive(Debug, Clone, Hash, PartialEq, Eq)]
    pub struct TestLang(String);

    impl fmt::Display for TestLang {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    impl FromStr for TestLang {
        type Err = ();
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            Ok(TestLang(s.into()))
        }
    }

    impl Language for TestLang {
        fn cost(&self, children: &[u64]) -> u64 {
            let my_costs = match self.0.as_ref() {
                "+" => 5,
                "*" => 50,
                "/" => 150,
                _ => 10,
            };
            my_costs + children.iter().sum::<u64>()
        }
    }

    pub fn var<T>(v: &str) -> Expr<TestLang, T> {
        Expr::unit(v.parse().unwrap())
    }

    pub fn op<E, Child>(o: &str, args: Vec<Child>) -> E
    where
        E: From<Expr<TestLang, Child>>,
    {
        Expr::new(o.parse().unwrap(), args.into()).into()
    }
}
