use std::fmt::Debug;
use std::hash::Hash;

pub type Id = u32;

pub trait Node: Debug + PartialEq + Eq + Hash + Clone {
    type Constant: Debug + PartialEq;
    type Variable: Debug + PartialEq + Eq + Hash + Clone;
    type Operator: Debug + PartialEq;

    fn map_children(self, f: impl FnMut(Id) -> Id) -> Self;
    fn children(&self) -> &[Id];
    fn get_variable(&self) -> Option<&Self::Variable>;
    fn get_operator(&self) -> Option<&Self::Operator>;
    fn get_constant(&self) -> Option<&Self::Constant>;
}

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

        fn get_variable(&self) -> Option<&Self::Variable> {
            match self {
                Var(v) => Some(v),
                _ => None,
            }
        }

        fn get_operator(&self) -> Option<&Self::Operator> {
            match self {
                Op(o, _) => Some(o),
                _ => None,
            }
        }

        fn get_constant(&self) -> Option<&Self::Constant> {
            match self {
                Const(c) => Some(c),
                _ => None,
            }
        }

        fn map_children(self, mut f: impl FnMut(Id) -> Id) -> Self {
            match self {
                Var(v) => Var(v),
                Const(c) => Const(c),
                Op(o, args) => {
                    let args2 = args.iter().map(|id| f(*id)).collect();
                    TestNode::Op(o, args2)
                }
            }
        }

        fn children(&self) -> &[Id] {
            match self {
                Var(_) => &[],
                Const(_) => &[],
                Op(_, args) => &args,
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
