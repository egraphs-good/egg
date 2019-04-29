#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VarId(pub u32);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConstId(pub u32);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct OpId(pub u32);

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Expr<Id> {
    Var(VarId),
    Const(ConstId),
    Op(OpId, Vec<Id>),
}

impl<Id> Expr<Id> {
    pub fn map_ids<Id2>(&self, mut f: impl FnMut(Id) -> Id2) -> Expr<Id2>
    where
        Id: Clone,
    {
        match self {
            Expr::Var(v) => Expr::Var(*v),
            Expr::Const(c) => Expr::Const(*c),
            Expr::Op(o, args) => {
                let args2 = args.iter().map(|id| f(id.clone())).collect();
                Expr::Op(*o, args2)
            }
        }
    }

    pub fn convert_atom<Id2>(&self) -> Expr<Id2> {
        match self {
            Expr::Var(v) => Expr::Var(*v),
            Expr::Const(c) => Expr::Const(*c),
            Expr::Op(_, _) => panic!("Tried to convert_atom an op"),
        }
    }

    pub fn children(&self) -> &[Id] {
        match self {
            Expr::Var(_) => &[],
            Expr::Const(_) => &[],
            Expr::Op(_op, args) => &args,
        }
    }
}

pub type SimpleNode = Expr<u32>;

#[derive(Debug, Default, PartialEq, Eq, Hash, Clone)]
pub struct SimpleExpr {
    pub nodes: Vec<SimpleNode>,
}

impl SimpleExpr {
    pub fn add(&mut self, node: SimpleNode) -> u32 {
        let id = self.nodes.len() as u32;
        self.nodes.push(node);
        id
    }
}

#[cfg(test)]
pub fn var<Id>(vid: u32) -> Expr<Id> {
    Expr::Var(VarId(vid))
}

#[cfg(test)]
pub fn op<Id>(oid: u32, args: Vec<Id>) -> Expr<Id> {
    Expr::Op(OpId(oid), args)
}
