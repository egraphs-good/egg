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
pub struct Program<L> {
    instructions: Vec<Instruction<L>>,
    subst: Subst,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Instruction<L> {
    Bind { node: L, i: Reg, out: Reg },
    Compare { i: Reg, j: Reg },
}

#[inline(always)]
fn for_each_matching_node<L, D>(eclass: &EClass<L, D>, node: &L, mut f: impl FnMut(&L))
where
    L: Language,
{
    #[allow(clippy::mem_discriminant_non_enum)]
    if eclass.nodes.len() < 50 {
        eclass.nodes.iter().filter(|n| node.matches(n)).for_each(f)
    } else {
        debug_assert!(node.children().iter().all(|&id| id == Id::from(0)));
        debug_assert!(eclass.nodes.windows(2).all(|w| w[0] < w[1]));
        let mut start = eclass.nodes.binary_search(node).unwrap_or_else(|i| i);
        let discrim = std::mem::discriminant(node);
        while start > 0 {
            if std::mem::discriminant(&eclass.nodes[start - 1]) == discrim {
                start -= 1;
            } else {
                break;
            }
        }
        let matching = eclass.nodes[start..]
            .iter()
            .take_while(|&n| std::mem::discriminant(n) == discrim)
            .filter(|n| node.matches(n));
        debug_assert_eq!(
            matching.clone().count(),
            eclass.nodes.iter().filter(|n| node.matches(n)).count(),
            "matching node {:?}\nstart={}\n{:?} != {:?}\nnodes: {:?}",
            node,
            start,
            matching.clone().collect::<indexmap::IndexSet<_>>(),
            eclass
                .nodes
                .iter()
                .filter(|n| node.matches(n))
                .collect::<indexmap::IndexSet<_>>(),
            eclass.nodes
        );
        matching.for_each(&mut f);
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
        instructions: &[Instruction<L>],
        subst: &Subst,
        yield_fn: &mut impl FnMut(&Self, &Subst),
    ) where
        L: Language,
        N: Analysis<L>,
    {
        let mut instructions = instructions.iter();
        while let Some(instruction) = instructions.next() {
            match instruction {
                Instruction::Bind { i, out, node } => {
                    let remaining_instructions = instructions.as_slice();
                    return for_each_matching_node(&egraph[self.reg(*i)], node, |matched| {
                        self.reg.truncate(out.0 as usize);
                        self.reg.extend_from_slice(matched.children());
                        self.run(egraph, remaining_instructions, subst, yield_fn)
                    });
                }
                Instruction::Compare { i, j } => {
                    if egraph.find(self.reg(*i)) != egraph.find(self.reg(*j)) {
                        return;
                    }
                }
            }
        }

        yield_fn(self, subst)
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
        compiler.go()
    }

    fn go(&mut self) -> Program<L> {
        let mut instructions = vec![];
        while let Some(Todo { reg: i, pat }) = self.todo.pop() {
            match pat {
                ENodeOrVar::Var(v) => {
                    if let Some(&j) = self.v2r.get(&v) {
                        instructions.push(Instruction::Compare { i, j })
                    } else {
                        self.v2r.insert(v, i);
                    }
                }
                ENodeOrVar::ENode(node) => {
                    let out = self.out;
                    self.out.0 += node.len() as u32;

                    for (id, &child) in node.children().iter().enumerate() {
                        let r = Reg(out.0 + id as u32);
                        self.todo.push(Todo {
                            reg: r,
                            pat: self.pattern[usize::from(child)].clone(),
                        });
                    }

                    // zero out the children so Bind can use it to sort
                    let node = node.map_children(|_| Id::from(0));
                    instructions.push(Instruction::Bind { i, node, out })
                }
            }
        }

        let mut subst = Subst::default();
        for (v, r) in &self.v2r {
            subst.insert(*v, Id::from(r.0 as usize));
        }
        Program {
            instructions,
            subst,
        }
    }
}

impl<L: Language> Program<L> {
    pub(crate) fn compile_from_pat(pattern: &PatternAst<L>) -> Self {
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
        machine.run(
            egraph,
            &self.instructions,
            &self.subst,
            &mut |machine, subst| {
                let subst_vec = subst
                    .vec
                    .iter()
                    // HACK we are reusing Ids here, this is bad
                    .map(|(v, reg_id)| (*v, machine.reg(Reg(usize::from(*reg_id) as u32))))
                    .collect();
                substs.push(Subst { vec: subst_vec })
            },
        );

        log::trace!("Ran program, found {:?}", substs);
        substs
    }
}
