use std::fmt::{self, Debug};
use std::hash::Hash;

pub type Id = u32;

// TODO if NodeEnum is public, I could just make it my representation
// It being generic over the traitbound would allow me to just have a public enum
// (without to/from_enum) at the cost of just fixing my representation

pub type IdNode<N> = Node<N, Id>;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Node<N: NodeLike, Child> {
    Constant(N::Constant),
    Variable(N::Variable),
    Operator(N::Operator, Vec<Child>),
}

impl<N: NodeLike, Child> Node<N, Child> {
    pub fn map_children<Child2>(&self, f: impl FnMut(Child) -> Child2) -> Node<N, Child2>
    where
        Child: Clone,
    {
        use Node::*;
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
            Node::Constant(_) => &[],
            Node::Variable(_) => &[],
            Node::Operator(_, args) => args,
        }
    }

    pub fn symbol(&self) -> Symbol<N, Child> {
        Symbol { node: self }
    }
}

pub struct Symbol<'a, N: NodeLike, Child> {
    node: &'a Node<N, Child>,
}

impl<'a, N: NodeLike, Child> fmt::Display for Symbol<'a, N, Child>
where
    N::Constant: fmt::Display,
    N::Variable: fmt::Display,
    N::Operator: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.node {
            Node::Variable(v) => write!(f, "{}", v),
            Node::Constant(c) => write!(f, "{}", c),
            Node::Operator(op, _) => write!(f, "{}", op),
        }
    }
}

pub trait NodeLike: Debug + PartialEq + Eq + Hash + Clone {
    type Constant: Debug + PartialEq + Eq + Hash + Clone;
    type Variable: Debug + PartialEq + Eq + Hash + Clone;
    type Operator: Debug + PartialEq + Eq + Hash + Clone;

    fn cost(node: &Node<Self, Id>) -> u64;
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Expr<N: NodeLike> {
    pub root: Id,
    pub nodes: Vec<Node<N, Id>>,
}

impl<N: NodeLike> Default for Expr<N> {
    fn default() -> Self {
        Expr {
            root: 0,
            nodes: Vec::new(),
        }
    }
}

impl<N: NodeLike> Expr<N> {
    pub fn add(&mut self, n: Node<N, Id>) -> Id {
        let id = self.nodes.len() as Id;
        self.nodes.push(n);
        id
    }

    #[inline(always)]
    pub fn get_node(&self, i: Id) -> &Node<N, Id> {
        &self.nodes[i as usize]
    }
}

#[cfg(test)]
pub mod tests {

    use super::*;
    use std::rc::Rc;

    pub type Name = Rc<str>;

    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    pub enum TestNode {}

    impl NodeLike for TestNode {
        type Constant = Name;
        type Variable = Name;
        type Operator = Name;

        fn cost(node: &Node<Self, Id>) -> u64 {
            match node {
                Node::Variable(_) => 1,
                Node::Constant(_) => 1,
                Node::Operator(op, _) => match op.as_ref() {
                    "+" => 5,
                    "*" => 50,
                    "/" => 150,
                    _ => 10,
                },
            }
        }
    }

    pub fn var(v: &str) -> Node<TestNode, Id> {
        Node::Variable(v.into())
    }

    pub fn op<Child>(o: &str, args: Vec<Child>) -> Node<TestNode, Child> {
        Node::Operator(o.into(), args)
    }
}
