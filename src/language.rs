use std::fmt::{self, Debug};
use std::hash::Hash;

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
    fn for_each_mut<F: FnMut(Id) -> Id>(&mut self, f: F);

    fn for_each_i<F: FnMut(usize, Id)>(&self, mut f: F) {
        let mut i = 0;
        self.for_each(|id| {
            f(i, id);
            i += 1;
        });
    }

    fn map_children<F: FnMut(Id) -> Id>(mut self, f: F) -> Self {
        self.for_each_mut(f);
        self
    }

    // NOTE doesn't early terminate
    fn all<F: FnMut(Id) -> bool>(&self, mut f: F) -> bool {
        let mut all = true;
        self.for_each(|id| all &= f(id));
        all
    }

    fn is_leaf(&self) -> bool {
        self.len() == 0
    }

    fn len(&self) -> usize {
        let mut len = 0;
        self.for_each(|_| len += 1);
        len
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

pub trait ENodeDisplay {
    fn write_op(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
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
        use symbolic_expressions::Sexp;
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
    fn for_each_mut<F: FnMut(Id) -> Id>(&mut self, mut f: F) {
        self.children.iter_mut().for_each(|id| *id = f(*id));
    }
}

impl ENodeFromStr for StringENode {
    fn from_op_str(op_str: &str, children: Vec<Id>) -> Result<Self, String> {
        Ok(Self::new(op_str, children))
    }
}

impl ENodeDisplay for StringENode {
    fn write_op(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.op)
    }
}
