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
    fn children(&self) -> &[Id];
    fn children_mut(&mut self) -> &mut [Id];

    fn map_children<F>(&self, mut f: F) -> Self
    where
        F: FnMut(Id) -> Id,
    {
        let mut new = self.clone();
        new.children_mut().iter_mut().for_each(|id| *id = f(*id));
        new
    }

    fn is_leaf(&self) -> bool {
        self.children().is_empty()
    }

    fn len(&self) -> usize {
        self.children().len()
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct RecExpr<N> {
    pub(crate) nodes: Vec<N>,
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
        fn parse_sexp_into<N>(
            sexp: &Sexp,
            nodes: &mut Vec<Option<N>>,
            spot: usize,
        ) -> Result<(), String>
        where
            N: ENodeFromStr,
        {
            assert!(nodes[spot].is_none());
            match sexp {
                Sexp::Empty => Err("Found empty s-expression".into()),
                Sexp::String(s) => {
                    let node = ENodeFromStr::from_op_str(s, vec![])?;
                    nodes[spot] = Some(node);
                    Ok(())
                }
                Sexp::List(list) if list.is_empty() => Err(format!("Found empty s-expression")),
                Sexp::List(list) => match &list[0] {
                    Sexp::Empty => unreachable!("Cannot be in head position"),
                    Sexp::List(l) => bail!("Found a list in the head position: {:?}", l),
                    Sexp::String(op) => {
                        // make room for the arguments
                        let mut arg_ids = vec![];
                        for _ in &list[1..] {
                            arg_ids.push(nodes.len() as Id);
                            nodes.push(None);
                        }

                        let node = ENodeFromStr::from_op_str(op, arg_ids.clone())?;

                        assert_eq!(arg_ids.len(), list.len() - 1);
                        for (arg_id, sexp) in arg_ids.into_iter().zip(&list[1..]) {
                            parse_sexp_into(sexp, nodes, arg_id as usize)?
                        }

                        nodes[spot] = Some(node);
                        Ok(())
                    }
                },
            }
        }

        let mut nodes = vec![None];
        let sexp = symbolic_expressions::parser::parse_str(s.trim()).map_err(|e| e.to_string())?;
        parse_sexp_into(&sexp, &mut nodes, 0)?;
        Ok(RecExpr {
            nodes: nodes.into_iter().map(Option::unwrap).collect(),
        })
    }
}
