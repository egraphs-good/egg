#![allow(dead_code, unused_imports, unused_variables, unreachable_code)]
use crate::{EClass, EGraph, ENode, Id, Language, Pattern, PatternAst, Subst, Var};

use log::trace;
use std::cmp::Ordering;
use std::fmt;

struct Machine<'a, L, M> {
    egraph: &'a EGraph<L, M>,
    program: &'a [Instruction<L>],
    pc: usize,
    reg: Vec<Id>,
    stack: Vec<Binder<'a, L>>,
}

type Addr = usize;
type Reg = usize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Instruction<L> {
    Bind(Reg, L, usize, Reg),
    Check(Reg, L),
    Compare(Reg, Reg),
    Yield(Vec<Reg>),
}

struct Binder<'a, L> {
    out: Reg,
    next: Addr,
    searcher: EClassSearcher<'a, L>,
}

struct EClassSearcher<'a, L> {
    op: L,
    len: usize,
    nodes: &'a [ENode<L>],
}

impl<'a, L: PartialEq> Iterator for EClassSearcher<'a, L> {
    type Item = &'a [Id];
    fn next(&mut self) -> Option<Self::Item> {
        for (i, enode) in self.nodes.iter().enumerate() {
            if enode.op == self.op && enode.children.len() == self.len {
                self.nodes = &self.nodes[i + 1..];
                return Some(enode.children.as_slice());
            }
        }
        None
    }
}

use Instruction::*;

impl<'a, L: Language, M> Machine<'a, L, M> {
    fn new(egraph: &'a EGraph<L, M>, program: &'a [Instruction<L>]) -> Self {
        Self {
            egraph,
            program,
            pc: 0,
            reg: Vec::new(),
            stack: Vec::new(),
        }
    }

    #[inline(always)]
    fn find_reg(&self, reg: usize) -> Id {
        self.egraph.find(self.reg[reg])
    }

    #[must_use]
    #[inline(always)]
    fn backtrack(&mut self) -> Option<()> {
        trace!("Backtracking, stack size: {}", self.stack.len());
        let Binder {
            out,
            next,
            searcher,
        } = self.stack.last_mut()?;

        if let Some(matched) = searcher.next() {
            trace!("Binding: {:?}", matched);
            let new_len = *out + matched.len();
            self.reg.resize(new_len, 0);
            let out_regs = &mut self.reg[*out..new_len];
            out_regs.copy_from_slice(&matched);
            self.pc = *next;
            Some(())
        } else {
            self.stack.pop().expect("we know the stack isn't empty");
            self.backtrack()
        }
    }

    fn next(&mut self) -> Option<Vec<Id>> {
        loop {
            let instr = &self.program.get(self.pc)?;
            self.pc += 1;

            trace!("Executing {:?}", instr);

            match instr {
                Bind(i, op, len, out) => {
                    let eclass = &self.egraph[self.reg[*i]];
                    self.stack.push(Binder {
                        out: *out,
                        next: self.pc,
                        searcher: EClassSearcher {
                            op: op.clone(),
                            len: *len,
                            nodes: &eclass.nodes,
                        },
                    });
                    self.backtrack()?;
                }
                Check(i, t) => {
                    let id = self.reg[*i];
                    let eclass = &self.egraph[id];
                    if eclass
                        .nodes
                        .iter()
                        .any(|n| &n.op == t && n.children.is_empty())
                    {
                        trace!("Check(r{} = e{}, {:?}) passed", i, id, t);
                    } else {
                        trace!("Check(r{} = e{}, {:?}) failed", i, id, t);
                        self.backtrack()?;
                    }
                    // TODO the below is more efficient, but is broken
                    // because we don't support look up of ground
                    // terms, because people can just push into eclasses
                    //
                    // let id1 = self.find_reg(*i);
                    // let id2 = self.egraph.get_leaf(t.clone());

                    // if Some(id1) == id2 {
                    //     trace!("Check(r{} = e{}, {:?}) passed", i, id1, t);
                    // } else {
                    //     trace!("Check(r{} = e{}, {:?}) failed", i, id1, t);
                    //     self.backtrack()?;
                    // }
                }
                Compare(i, j) => {
                    if self.find_reg(*i) != self.find_reg(*j) {
                        self.backtrack()?;
                    }
                }
                Yield(regs) => {
                    let ids = regs.iter().map(|r| self.reg[*r]).collect();
                    // backtrack, but don't fail so we can yield
                    let _ = self.backtrack();
                    return Some(ids);
                }
            }
        }
    }
}

type RegToPat<L> = indexmap::IndexMap<Reg, PatternAst<L>>;
type VarToReg = indexmap::IndexMap<Var, Reg>;

fn size<L>(p: &PatternAst<L>) -> usize {
    match p {
        PatternAst::ENode(e) => 1 + e.children.iter().map(size).sum::<usize>(),
        PatternAst::Var(_) => 1,
    }
}

fn rank<L>(_v2r: &VarToReg, p1: &PatternAst<L>, p2: &PatternAst<L>) -> Ordering {
    size(p1).cmp(&size(p2))
}

fn compile<L>(
    r2p: &mut RegToPat<L>,
    v2r: &mut VarToReg,
    mut next_reg: Reg,
    buf: &mut Vec<Instruction<L>>,
) {
    while let Some((reg, pat)) = r2p.pop() {
        match pat {
            PatternAst::ENode(e) if e.children.is_empty() => {
                // e is a ground term, it has no children
                buf.push(Check(reg, e.op))
            }
            PatternAst::Var(v) => {
                if let Some(&r) = v2r.get(&v) {
                    buf.push(Compare(r, reg))
                } else {
                    v2r.insert(v, reg);
                }
            }
            PatternAst::ENode(e) => {
                let len = e.children.len();
                assert_ne!(len, 0);
                buf.push(Bind(reg, e.op, len, next_reg));

                r2p.extend(
                    e.children
                        .into_iter()
                        .enumerate()
                        .map(|(i, pat)| (next_reg + i, pat)),
                );

                // sort in reverse order so we pop the cheapest
                // NOTE, this doesn't seem to have a very large effect right now
                r2p.sort_by(|_, p1, _, p2| rank(v2r, p1, p2).reverse());

                next_reg += len;
            }
        }
    }

    assert!(r2p.is_empty());
    let registers = v2r.values().copied().collect();
    buf.push(Yield(registers));
}

#[derive(PartialEq, Clone)]
pub struct Program<L> {
    v2r: VarToReg,
    instrs: Vec<Instruction<L>>,
}

impl<L: fmt::Debug> fmt::Debug for Program<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Program")?;
        for (i, instr) in self.instrs.iter().enumerate() {
            writeln!(f, "{}: {:?}", i, instr)?;
        }
        Ok(())
    }
}

impl<L: Language> Program<L> {
    pub(crate) fn compile_from_pat(pat: &PatternAst<L>) -> Program<L>
    where
        L: Language,
    {
        let mut instrs = Vec::new();
        let mut r2p = RegToPat::new();
        let mut v2r = VarToReg::new();

        r2p.insert(0, pat.clone());
        compile(&mut r2p, &mut v2r, 1, &mut instrs);

        let program = Program { instrs, v2r };
        trace!("Compiled {:?} to {:?}", pat, program);
        program
    }

    pub fn run<M>(&self, egraph: &EGraph<L, M>, eclass: Id) -> Vec<Subst> {
        let mut machine = Machine::new(egraph, &self.instrs);

        assert_eq!(machine.reg.len(), 0);
        machine.reg.push(eclass);

        let mut substs = Vec::new();
        while let Some(ids) = machine.next() {
            let mut s = Subst::default();
            for (i, id) in ids.into_iter().enumerate() {
                let var = self.v2r.get_index(i).unwrap().0;
                s.insert(var.clone(), id);
            }
            substs.push(s)
        }

        trace!("Ran program, found {:?}", substs);
        substs
    }
}
