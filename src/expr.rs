use std::fmt::Debug;
use std::hash::Hash;

pub type Id = u32;

// TODO if NodeEnum is public, I could just make it my representation
// It being generic over the traitbound would allow me to just have a public enum
// (without to/from_enum) at the cost of just fixing my representation

pub enum NodeEnum<'a, N: Node, Child> {
    Constant(&'a N::Constant),
    Variable(&'a N::Variable),
    Operator(&'a N::Operator, &'a [Child]),
}

impl<'a, N: Node> NodeEnum<'a, N, Id> {
    #[inline(always)]
    fn to_node(self) -> N {
        N::from_enum(self)
    }
}

pub trait Node: Debug + PartialEq + Eq + Hash + Clone {
    type Constant: Debug + PartialEq;
    type Variable: Debug + PartialEq + Eq + Hash + Clone;
    type Operator: Debug + PartialEq + Clone;

    fn cost(&self) -> u64;

    #[inline(always)]
    fn to_enum(&self) -> NodeEnum<Self, Id>;

    #[inline(always)]
    fn from_enum(node_enum: NodeEnum<Self, Id>) -> Self;
}

pub(crate) trait NodeExt: Node {
    fn map_children(&self, f: impl FnMut(Id) -> Id) -> Self {
        use NodeEnum::*;
        match self.to_enum() {
            Constant(c) => Constant(c).to_node(),
            Variable(v) => Variable(v).to_node(),
            Operator(op, args) => {
                let args2: Vec<_> = args.iter().cloned().map(f).collect();
                Operator(op, &args2).to_node()
            }
        }
    }
    fn children(&self) -> &[Id] {
        match self.to_enum() {
            NodeEnum::Constant(_) => &[],
            NodeEnum::Variable(_) => &[],
            NodeEnum::Operator(_, args) => args,
        }
    }
}

impl<N: Node> NodeExt for N {}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Expr<N> {
    pub root: Id,
    pub nodes: Vec<N>,
}

impl<N> Default for Expr<N> {
    fn default() -> Self {
        Expr {
            root: 0,
            nodes: Vec::new(),
        }
    }
}

impl<N> Expr<N> {
    pub fn add(&mut self, n: N) -> Id {
        let id = self.nodes.len() as Id;
        self.nodes.push(n);
        id
    }

    #[inline(always)]
    pub fn get_node(&self, i: Id) -> &N {
        &self.nodes[i as usize]
    }
}

#[cfg(test)]
pub mod tests {

    use super::*;
    use std::rc::Rc;

    pub type Name = Rc<str>;

    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    pub enum TestNode {
        Const(Name),
        Var(Name),
        Op(Name, Vec<Id>),
    }

    use TestNode::*;

    impl Node for TestNode {
        type Constant = Name;
        type Variable = Name;
        type Operator = Name;

        fn cost(&self) -> u64 {
            match self {
                Var(_) => 1,
                Const(_) => 1,
                Op(op, _) => match op.as_ref() {
                    "+" => 5,
                    "*" => 50,
                    "/" => 150,
                    _ => 10,
                },
            }
        }

        fn to_enum(&self) -> NodeEnum<Self, Id> {
            match self {
                Var(v) => NodeEnum::Variable(v),
                Const(c) => NodeEnum::Constant(c),
                Op(o, args) => NodeEnum::Operator(o, args),
            }
        }

        fn from_enum(node_enum: NodeEnum<Self, Id>) -> Self {
            match node_enum {
                NodeEnum::Variable(v) => Var(Rc::clone(v)),
                NodeEnum::Constant(c) => Const(Rc::clone(c)),
                NodeEnum::Operator(o, args) => Op(Rc::clone(o), args.to_vec()),
            }
        }
    }

    use std::fmt::{Display, Formatter, Result};

    impl Display for TestNode {
        fn fmt(&self, f: &mut Formatter) -> Result {
            match self {
                Var(v) => write!(f, "{}", v),
                Const(c) => write!(f, "{}", c),
                Op(o, _) => write!(f, "{}", o),
            }
        }
    }

    pub fn var(v: &str) -> TestNode {
        TestNode::Var(v.into())
    }

    pub fn op(o: &str, args: Vec<Id>) -> TestNode {
        TestNode::Op(o.into(), args)
    }
}
