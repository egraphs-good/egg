use crate::util::HashSet;
use crate::{Analysis, EClass, EGraph, ENodeOrVar, Id, Language, PatternAst, RecExpr, Subst, Var};
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
    ground_terms: Vec<RecExpr<L>>,
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
        debug_assert!(node.all(|id| id == Id::from(0)));
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
            matching.clone().collect::<HashSet<_>>(),
            eclass
                .nodes
                .iter()
                .filter(|n| node.matches(n))
                .collect::<HashSet<_>>(),
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
                        matched.for_each(|id| self.reg.push(id));
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

type VarToReg = crate::util::IndexMap<Var, Reg>;
type TodoList<L> = std::collections::BinaryHeap<Todo<L>>;

#[derive(PartialEq, Eq)]
struct Todo<L> {
    reg: Reg,
    is_ground: bool,
    loc: usize,
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
        match (&self.is_ground, &other.is_ground) {
            (true, false) => return Ordering::Greater,
            (false, true) => return Ordering::Less,
            _ => (),
        };
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
        let mut compiler = Self {
            pattern,
            v2r: Default::default(),
            todo: Default::default(),
            out: Reg(0),
        };
        compiler.go()
    }

    fn get_ground_locs(&mut self, is_ground: &Vec<bool>) -> Vec<Option<Reg>> {
        let mut ground_locs: Vec<Option<Reg>> = vec![None; self.pattern.len()];
        for i in 0..self.pattern.len() {
            if let ENodeOrVar::ENode(node) = &self.pattern[i] {
                if !is_ground[i] {
                    node.for_each(|c| {
                        let c = usize::from(c);
                        // If a ground pattern is a child of a non-ground pattern,
                        // we load the ground pattern
                        if is_ground[c] && ground_locs[c].is_none() {
                            if let ENodeOrVar::ENode(_) = &self.pattern[c] {
                                ground_locs[c] = Some(self.out);
                                self.out.0 += 1;
                            } else {
                                unreachable!("ground locs");
                            }
                        }
                    })
                }
            }
        }
        if *is_ground.last().unwrap() {
            if let Some(_) = self.pattern.last() {
                *ground_locs.last_mut().unwrap() = Some(self.out);
                self.out.0 += 1;
            } else {
                unreachable!("ground locs");
            }
        }
        ground_locs
    }

    fn build_ground_terms(&self, loc: usize, expr: &mut RecExpr<L>) {
        if let ENodeOrVar::ENode(mut node) = self.pattern[loc].clone() {
            node.update_children(|c| {
                self.build_ground_terms(usize::from(c), expr);
                (expr.as_ref().len() - 1).into()
            });
            expr.add(node);
        } else {
            panic!("could only build ground terms");
        }
    }

    fn go(&mut self) -> Program<L> {
        let mut is_ground: Vec<bool> = vec![false; self.pattern.len()];
        for i in 0..self.pattern.len() {
            if let ENodeOrVar::ENode(node) = &self.pattern[i] {
                is_ground[i] = node.all(|c| is_ground[usize::from(c)]);
            }
        }

        let ground_locs = self.get_ground_locs(&is_ground);
        let ground_terms: Vec<RecExpr<L>> = ground_locs
            .iter()
            .enumerate()
            .filter_map(|(i, r)| r.map(|_| i))
            .map(|i| {
                let mut expr = Default::default();
                self.build_ground_terms(i, &mut expr);
                expr
            })
            .collect();
        self.todo.push(Todo {
            reg: Reg(self.out.0),
            is_ground: is_ground[self.pattern.len() - 1],
            loc: self.pattern.len() - 1,
            pat: self.pattern.last().unwrap().clone(),
        });
        self.out.0 += 1;

        let mut instructions = vec![];

        while let Some(Todo {
            reg: i, pat, loc, ..
        }) = self.todo.pop()
        {
            match pat {
                ENodeOrVar::Var(v) => {
                    if let Some(&j) = self.v2r.get(&v) {
                        instructions.push(Instruction::Compare { i, j })
                    } else {
                        self.v2r.insert(v, i);
                    }
                }
                ENodeOrVar::ENode(node) => {
                    if let Some(j) = ground_locs[loc] {
                        instructions.push(Instruction::Compare { i, j });
                        continue;
                    }

                    let out = self.out;
                    self.out.0 += node.len() as u32;

                    let mut id = 0;
                    node.for_each(|child| {
                        let r = Reg(out.0 + id as u32);
                        self.todo.push(Todo {
                            reg: r,
                            is_ground: is_ground[usize::from(child)],
                            loc: usize::from(child),
                            pat: self.pattern[usize::from(child)].clone(),
                        });
                        id += 1;
                    });

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
            ground_terms,
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
        for expr in &self.ground_terms {
            if let Some(id) = egraph.lookup_expr(&mut expr.clone()) {
                machine.reg.push(id)
            } else {
                return vec![];
            }
        }
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
