use crate::*;
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
    Lookup { term: PatternAst<L>, i: Reg },
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
                Instruction::Lookup { term, i } => {
                    let mut new_ids = Vec::with_capacity(term.as_ref().len());
                    for node in term.as_ref() {
                        match node {
                            ENodeOrVar::ENode(node) => {
                                let node = node.clone().map_children(|i| new_ids[usize::from(i)]);
                                match egraph.lookup(node) {
                                    Some(id) => new_ids.push(id),
                                    None => return,
                                }
                            }
                            ENodeOrVar::Var(_) => {
                                panic!("Lookup instruction only supports ground terms right now")
                                // in the future, this could ids for registers
                            }
                        }
                    }

                    let id = egraph.find(self.reg(*i));
                    if new_ids.last().copied() != Some(id) {
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
    pat: ENodeOrVar<L>,
    /// location within the pattern
    id: Id,
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
        let cmp_ground = self.is_ground.cmp(&other.is_ground);
        cmp_ground.then_with(|| match (&self.pat, &other.pat) {
            // fewer children means higher priority
            (ENode(e1), ENode(e2)) => e2.len().cmp(&e1.len()),
            // Var is higher prio than enode
            (ENode(_), Var(_)) => Ordering::Less,
            (Var(_), ENode(_)) => Ordering::Greater,
            (Var(_), Var(_)) => Ordering::Equal,
        })
    }
}

struct Compiler<'a, L: Language> {
    pattern: &'a PatternAst<L>,
    v2r: VarToReg,
    todo: TodoList<L>,
    out: Reg,
}

impl<'a, L: Language> Compiler<'a, L> {
    fn compile(pattern: &'a PatternAst<L>) -> Program<L> {
        let mut compiler = Self {
            pattern,
            v2r: Default::default(),
            todo: Default::default(),
            out: Reg(0),
        };
        compiler.go()
    }

    fn go(&mut self) -> Program<L> {
        let nodes = self.pattern.as_ref();
        let len = nodes.len();
        let mut is_ground: Vec<bool> = vec![false; len];
        for (i, node) in nodes.iter().enumerate() {
            if let ENodeOrVar::ENode(node) = node {
                is_ground[i] = node.all(|c| is_ground[usize::from(c)]);
            }
        }

        let last_i = len - 1;
        self.todo.push(Todo {
            reg: Reg(self.out.0),
            is_ground: is_ground[last_i],
            id: Id::from(last_i),
            pat: nodes[last_i].clone(),
        });
        self.out.0 += 1;

        let mut instructions = vec![];

        while let Some(todo) = self.todo.pop() {
            match todo.pat {
                ENodeOrVar::Var(v) => {
                    if let Some(&j) = self.v2r.get(&v) {
                        instructions.push(Instruction::Compare { i: todo.reg, j })
                    } else {
                        self.v2r.insert(v, todo.reg);
                    }
                }
                ENodeOrVar::ENode(node) => {
                    if todo.is_ground && !node.is_leaf() {
                        instructions.push(Instruction::Lookup {
                            i: todo.reg,
                            term: self.pattern.extract(todo.id),
                        });
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
                            id: child,
                            pat: nodes[usize::from(child)].clone(),
                        });
                        id += 1;
                    });

                    // zero out the children so Bind can use it to sort
                    let node = node.map_children(|_| Id::from(0));
                    instructions.push(Instruction::Bind {
                        i: todo.reg,
                        node,
                        out,
                    })
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
        let program = Compiler::compile(pattern);
        log::debug!("Compiled {:?} to {:?}", pattern.as_ref(), program);
        program
    }

    pub fn run<A>(&self, egraph: &EGraph<L, A>, eclass: Id) -> Vec<Subst>
    where
        A: Analysis<L>,
    {
        let mut machine = Machine::default();

        assert!(egraph.clean, "Tried to search a dirty e-graph!");
        assert_eq!(machine.reg.len(), 0);
        machine.reg.push(eclass);

        let mut matches = Vec::new();
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
                matches.push(Subst { vec: subst_vec });
            },
        );

        log::trace!("Ran program, found {:?}", matches);
        matches
    }
}
