use crate::{Analysis, EClass, EGraph, ENodeOrVar, Id, Language, PatternAst, Subst, Var};
use std::cmp::Ordering;

struct Machine {
    reg: Vec<Id>,
}

impl Default for Machine {
    fn default() -> Self {
        Self { reg: vec![] }
    }
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Reg(u32);

#[derive(Debug, Clone, PartialEq, Eq)]
enum Instruction<L> {
    Bind {
        node: L,
        i: Reg,
        out: Reg,
        next: Vec<Instruction<L>>,
    },
    Yield(Subst),
    CheckLeaf {
        i: Reg,
        node: L,
        next: Box<Instruction<L>>,
    },
    Compare {
        i: Reg,
        j: Reg,
        next: Box<Instruction<L>>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program<L> {
    instruction: Instruction<L>,
    v2r: VarToReg,
}

#[inline(always)]
fn for_each_matching_node<L, D>(eclass: &EClass<L, D>, node: &L, f: impl FnMut(&L))
where
    L: Language,
{
    if eclass.nodes.len() < 50 {
        eclass.nodes.iter().filter(|n| node.matches(n)).for_each(f)
    } else {
        debug_assert!(node.children().iter().all(|&id| id == 0));
        let start = eclass.nodes.binary_search(node).unwrap_or_else(|i| i);
        eclass.nodes[start..]
            .iter()
            .take_while(|n| node.matches(n))
            .for_each(f)
    }
}

impl Machine {
    #[inline(always)]
    fn reg(&self, reg: Reg) -> Id {
        self.reg[reg.0 as usize]
    }

    fn run<L, N>(
        &mut self,
        egraph: &EGraph<L, N>,
        instruction: &Instruction<L>,
        yield_fn: &mut impl FnMut(&Self, &Subst),
    ) where
        L: Language,
        N: Analysis<L>,
    {
        match instruction {
            Instruction::Bind { i, out, next, node } => {
                debug_assert!(!next.is_empty());
                for_each_matching_node(&egraph[self.reg(*i)], node, |matched| {
                    self.reg.truncate(out.0 as usize);
                    self.reg.extend_from_slice(matched.children());
                    for next_instr in next {
                        self.run(egraph, next_instr, yield_fn)
                    }
                })
            }
            Instruction::CheckLeaf { node, i, next } => {
                debug_assert!(node.is_leaf());
                let id = self.reg(*i);
                let eclass = &egraph[id];
                if eclass.nodes.contains(node) {
                    self.run(egraph, next, yield_fn)
                }
            }
            Instruction::Compare { i, j, next } => {
                if egraph.find(self.reg(*i)) == egraph.find(self.reg(*j)) {
                    self.run(egraph, next, yield_fn)
                }
            }
            Instruction::Yield(subst) => yield_fn(self, subst),
        }
    }
}

type VarToReg = indexmap::IndexMap<Var, Reg>;
type TodoList<L> = std::collections::BinaryHeap<Todo<L>>;

#[derive(PartialEq, Eq)]
struct Todo<L> {
    reg: Reg,
    pat: ENodeOrVar<L>,
}

impl<L: Language> PartialOrd for Todo<L> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<L: Language> Ord for Todo<L> {
    // TodoList is a max-heap, so we greater is higher priority
    fn cmp(&self, other: &Self) -> Ordering {
        use ENodeOrVar::*;
        match (&self.pat, &other.pat) {
            // fewer children means higher priority
            (ENode(e1), ENode(e2)) => e2.len().cmp(&e1.len()),
            // Var is higher prio than enode
            (ENode(_), Var(_)) => Ordering::Less,
            (Var(_), ENode(_)) => Ordering::Greater,
            (Var(_), Var(_)) => Ordering::Equal,
        }
    }
}

struct Compiler<'a, L> {
    pattern: &'a [ENodeOrVar<L>],
    v2r: VarToReg,
    todo: TodoList<L>,
    out: Reg,
}

impl<'a, L: Language> Compiler<'a, L> {
    fn compile(pattern: &'a [ENodeOrVar<L>]) -> Program<L> {
        let last = pattern.last().unwrap();
        let mut compiler = Self {
            pattern,
            v2r: Default::default(),
            todo: Default::default(),
            out: Reg(1),
        };
        compiler.todo.push(Todo {
            reg: Reg(0),
            pat: last.clone(),
        });
        Program {
            instruction: compiler.go(),
            v2r: compiler.v2r,
        }
    }

    fn go(&mut self) -> Instruction<L> {
        let Todo { reg: i, pat } = match self.todo.pop() {
            Some(tup) => tup,
            None => {
                let mut subst = Subst::default();
                for (v, r) in &self.v2r {
                    subst.insert(*v, r.0);
                }
                return Instruction::Yield(subst);
            }
        };

        match pat {
            ENodeOrVar::Var(v) => {
                if let Some(&j) = self.v2r.get(&v) {
                    let next = Box::new(self.go());
                    Instruction::Compare { i, j, next }
                } else {
                    self.v2r.insert(v, i);
                    self.go()
                }
            }
            ENodeOrVar::ENode(node) => {
                if node.is_leaf() {
                    let next = Box::new(self.go());
                    Instruction::CheckLeaf { i, node, next }
                } else {
                    let out = self.out;
                    self.out.0 += node.len() as u32;

                    for (id, &child) in node.children().iter().enumerate() {
                        let r = Reg(out.0 + id as u32);
                        self.todo.push(Todo {
                            reg: r,
                            pat: self.pattern[child as usize].clone(),
                        });
                    }

                    // zero out the children so Bind can use it to sort
                    let node = node.map_children(|_| 0);
                    let next = vec![self.go()];
                    Instruction::Bind { i, node, out, next }
                }
            }
        }
    }
}

impl<L: Language> Program<L> {
    pub(crate) fn compile_from_pat(pattern: &PatternAst<L>) -> Program<L> {
        let program = Compiler::compile(pattern.as_ref());
        log::debug!("Compiled {:?} to {:?}", pattern.as_ref(), program);
        program
    }

    pub fn run<A>(&self, egraph: &EGraph<L, A>, eclass: Id) -> Vec<Subst>
    where
        A: Analysis<L>,
    {
        let mut machine = Machine::default();

        assert_eq!(machine.reg.len(), 0);
        machine.reg.push(eclass);

        let mut substs = Vec::new();
        machine.run(egraph, &self.instruction, &mut |machine, subst| {
            let subst_vec = subst
                .vec
                .iter()
                .map(|(v, reg_id)| (*v, machine.reg(Reg(*reg_id))))
                .collect();
            substs.push(Subst { vec: subst_vec })
        });

        log::trace!("Ran program, found {:?}", substs);
        substs
    }
}
