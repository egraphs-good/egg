use std::fmt::{self, Debug};
use std::hash::Hash;
use symbolic_expressions::Sexp;

use crate::{EGraph, Id};

pub trait Language: Sized {
    type ENode: ENode;
    type Metadata: PartialEq + std::fmt::Debug + Clone;

    fn metadata_make(egraph: &mut EGraph<Self>, enode: &Self::ENode) -> Self::Metadata;
    fn metadata_modify(egraph: &mut EGraph<Self>, id: Id) {}
    fn metadata_merge(&self, to: &mut Self::Metadata, from: Self::Metadata) -> bool;
}

pub trait ENode: Debug + Clone + Eq + Ord + Hash {
    fn matches(&self, other: &Self) -> bool;
    fn for_each<F: FnMut(Id)>(&self, f: F);
    fn for_each_mut<F: FnMut(&mut Id)>(&mut self, f: F);

    fn for_each_i<F: FnMut(usize, Id)>(&self, mut f: F) {
        let mut i = 0;
        self.for_each(|id| {
            f(i, id);
            i += 1;
        });
    }

    fn update_children<F: FnMut(Id) -> Id>(&mut self, mut f: F) {
        self.for_each_mut(|id| *id = f(*id))
    }

    fn map_children<F: FnMut(Id) -> Id>(mut self, f: F) -> Self {
        self.update_children(f);
        self
    }

    fn fold<F, T>(&self, init: T, mut f: F) -> T
    where
        F: FnMut(T, Id) -> T,
        T: Clone,
    {
        let mut acc = init;
        self.for_each(|id| acc = f(acc.clone(), id));
        acc
    }

    // NOTE doesn't early terminate
    fn all<F: FnMut(Id) -> bool>(&self, mut f: F) -> bool {
        self.fold(true, |b, id| b & f(id))
    }

    fn is_leaf(&self) -> bool {
        self.len() == 0
    }

    fn len(&self) -> usize {
        self.fold(0, |sum, _| sum + 1)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct RecExpr<N> {
    nodes: Vec<N>,
}

impl<N> Default for RecExpr<N> {
    fn default() -> Self {
        Self { nodes: vec![] }
    }
}

impl<N> AsRef<[N]> for RecExpr<N> {
    fn as_ref(&self) -> &[N] {
        &self.nodes
    }
}

impl<N> RecExpr<N> {
    pub fn add(&mut self, node: N) -> Id {
        // TODO check for duplication
        self.nodes.push(node);
        self.nodes.len() as Id - 1
    }
}

impl<N: ENode + ENodeDisplay> RecExpr<N> {
    fn to_sexp(&self, i: Id) -> Sexp {
        let node = &self.nodes[i as usize];
        let op = Sexp::String(node.display_op().to_string());
        if node.is_leaf() {
            op
        } else {
            let mut vec = vec![op];
            node.for_each(|id| vec.push(self.to_sexp(id)));
            Sexp::List(vec)
        }
    }

    /// Pretty print with a maximum line length.
    ///
    /// This gives you a nice, indented, pretty-printed s-expression.
    ///
    /// # Example
    /// ```
    /// # use egg::*;
    /// define_language! {
    ///     enum FooLanguage {
    ///         Num(i32),
    ///         Add = "+",
    ///         Mul = "*",
    ///         Symbol(String),
    ///     }
    /// }
    ///
    /// let e: RecExpr<FooLanguage> = "(* (+ 2 2) (+ x y))".parse().unwrap();
    /// assert_eq!(e.pretty(10), "
    /// (*
    ///   (+ 2 2)
    ///   (+ x y))
    /// ".trim());
    /// ```
    pub fn pretty(&self, width: usize) -> String {
        use std::fmt::{Result, Write};
        let sexp = self.to_sexp(self.nodes.len() as Id - 1);

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

pub trait ENodeDisplay {
    fn display_op(&self) -> &dyn fmt::Display;
}

pub trait ENodeFromStr: Sized {
    fn from_op_str(op_str: &str, children: Vec<Id>) -> Result<Self, String>;
}

macro_rules! bail {
    ($s:literal $(,)?) => {
        return Err($s.into())
    };
    ($s:literal, $($args:expr),+) => {
        return Err(format!($s, $($args),+).into())
    };
}

impl<N: ENodeFromStr> std::str::FromStr for RecExpr<N> {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        fn parse_sexp_into<N>(sexp: &Sexp, expr: &mut RecExpr<N>) -> Result<Id, String>
        where
            N: ENodeFromStr,
        {
            match sexp {
                Sexp::Empty => Err("Found empty s-expression".into()),
                Sexp::String(s) => {
                    let node = ENodeFromStr::from_op_str(s, vec![])?;
                    Ok(expr.add(node))
                }
                Sexp::List(list) if list.is_empty() => Err(format!("Found empty s-expression")),
                Sexp::List(list) => match &list[0] {
                    Sexp::Empty => unreachable!("Cannot be in head position"),
                    Sexp::List(l) => bail!("Found a list in the head position: {:?}", l),
                    Sexp::String(op) => {
                        let arg_ids: Result<Vec<Id>, _> =
                            list[1..].iter().map(|s| parse_sexp_into(s, expr)).collect();

                        let node = ENodeFromStr::from_op_str(op, arg_ids?)?;
                        Ok(expr.add(node))
                    }
                },
            }
        }

        let mut expr = RecExpr::default();
        let sexp = symbolic_expressions::parser::parse_str(s.trim()).map_err(|e| e.to_string())?;
        parse_sexp_into(&sexp, &mut expr)?;
        Ok(expr)
    }
}

/// A simple language used for testing.
///
/// Its language implementation uses () as metadata.
pub struct SimpleLanguage<ENode>(std::marker::PhantomData<ENode>);

impl<N> Default for SimpleLanguage<N> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<N: ENode> Language for SimpleLanguage<N> {
    type ENode = N;
    type Metadata = ();

    fn metadata_make(_egraph: &mut EGraph<Self>, _enode: &Self::ENode) -> Self::Metadata {
        ()
    }
    fn metadata_merge(&self, to: &mut Self::Metadata, from: Self::Metadata) -> bool {
        false
    }
}

/// A simple `ENode` used for testing
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StringENode {
    pub op: String,
    pub children: Vec<Id>,
}

impl StringENode {
    pub fn leaf(op: impl Into<String>) -> Self {
        Self::new(op, vec![])
    }

    pub fn new(op: impl Into<String>, children: impl IntoIterator<Item = Id>) -> Self {
        Self {
            op: op.into(),
            children: children.into_iter().collect(),
        }
    }
}

impl ENode for StringENode {
    fn matches(&self, other: &Self) -> bool {
        self.op == other.op && self.len() == other.len()
    }
    fn for_each<F: FnMut(Id)>(&self, f: F) {
        self.children.iter().copied().for_each(f)
    }
    fn for_each_mut<F: FnMut(&mut Id)>(&mut self, f: F) {
        self.children.iter_mut().for_each(f);
    }
}

impl ENodeFromStr for StringENode {
    fn from_op_str(op_str: &str, children: Vec<Id>) -> Result<Self, String> {
        Ok(Self::new(op_str, children))
    }
}

impl ENodeDisplay for StringENode {
    fn display_op(&self) -> &dyn fmt::Display {
        &self.op
    }
}
