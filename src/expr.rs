use std::fmt::{self, Debug};
use std::hash::Hash;
use std::rc::Rc;

use smallvec::SmallVec;
use symbolic_expressions::Sexp;

use crate::unionfind::UnionFind;

pub type Id = u32;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct ENode<O, Child = Id> {
    pub op: O,
    pub children: SmallVec<[Child; 2]>,
}

type Inner<L> = ENode<L, RecExpr<L>>;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct RecExpr<L> {
    rc: Rc<Inner<L>>,
}

#[cfg(feature = "serde-1")]
impl<L: Language + fmt::Display> serde::Serialize for RecExpr<L> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        // 3 is the number of fields in the struct.
        let s = self.pretty(80);
        serializer.serialize_str(&s)
    }
}

impl<L> From<Inner<L>> for RecExpr<L> {
    fn from(inner: Inner<L>) -> Self {
        let rc = Rc::new(inner);
        RecExpr { rc }
    }
}

impl<L> std::borrow::Borrow<Inner<L>> for RecExpr<L> {
    fn borrow(&self) -> &Inner<L> {
        &self.rc
    }
}

impl<L> AsRef<Inner<L>> for RecExpr<L> {
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

    pub fn pretty(&self, width: usize) -> String {
        use std::fmt::{Result, Write};
        let sexp = self.to_sexp();

        fn pp(buf: &mut String, sexp: &Sexp, width: usize, level: usize) -> Result {
            if let Sexp::List(list) = sexp {
                let indent = sexp.to_string().len() > width;
                write!(buf, "(")?;

                for (i, val) in list.iter().enumerate() {
                    if indent && i > 0 {
                        writeln!(buf)?;
                        for _ in 0..level {
                            write!(buf, "  ")?;
                        }
                    }
                    pp(buf, val, width, level + 1)?;
                    if !indent && i < list.len() - 1 {
                        write!(buf, " ")?;
                    }
                }

                write!(buf, ")")?;
                Ok(())
            } else {
                // I don't care about quotes
                write!(buf, "{}", sexp.to_string().trim_matches('"'))
            }
        }

        let mut buf = String::new();
        pp(&mut buf, &sexp, width, 1).unwrap();
        buf
    }
}

impl<L: Language, Child> ENode<L, Child> {
    #[inline(always)]
    pub fn leaf(op: L) -> Self {
        ENode::new(op, vec![])
    }

    #[inline(always)]
    pub fn new(op: L, children: impl IntoIterator<Item = Child>) -> Self {
        let children = children.into_iter().collect();
        ENode { op, children }
    }

    #[inline(always)]
    pub fn try_new<E, I>(op: L, children: I) -> Result<Self, E>
    where
        I: IntoIterator<Item = Result<Child, E>>,
    {
        let c: Result<_, E> = children.into_iter().collect();
        c.map(|children| ENode { op, children })
    }

    #[inline(always)]
    pub fn map_children_result<Child2, F, Error>(&self, f: F) -> Result<ENode<L, Child2>, Error>
    where
        Child: Clone,
        F: FnMut(Child) -> Result<Child2, Error>,
    {
        ENode::try_new(self.op.clone(), self.children.iter().cloned().map(f))
    }

    #[inline(always)]
    pub fn map_children<Child2, F>(&self, mut f: F) -> ENode<L, Child2>
    where
        Child: Clone,
        F: FnMut(Child) -> Child2,
    {
        let some_f = |child| Result::<Child2, std::convert::Infallible>::Ok(f(child));
        self.map_children_result(some_f).unwrap()
    }
}

impl<L: Language> ENode<L> {
    pub fn update_ids<V>(&self, unionfind: &UnionFind<Id, V>) -> Self {
        self.map_children(|id| unionfind.find(id))
    }
}

/// Trait defines a Language whose terms will be in the `EGraph`.
///
/// Typically, you'll want your language to implement `FromStr` as well.
/// Check out the [`define_language!`] macro for an easy way to create
/// a `Language`.
/// [`define_language!`]: macro.define_language.html
pub trait Language: Debug + PartialEq + Eq + Hash + Clone + 'static {}

impl Language for String {}
impl Language for &'static str {}

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
