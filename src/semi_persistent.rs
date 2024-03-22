use crate::explain::Connection;
use crate::util::HashMap;
use crate::{EClass, EGraph, Id, Language, WithUndo};
use indexmap::IndexSet;
use std::fmt::Debug;

#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
struct UndoNode {
    /// Other ENodes that were unioned with this ENode and chose it as their representative
    representative_of: Vec<Id>,
    /// Non-canonical Id's of direct parents of this non-canonical node
    parents: Vec<Id>,
}

fn visit_undo_node(id: Id, undo_find: &[UndoNode], f: &mut impl FnMut(Id, &UndoNode)) {
    let node = &undo_find[usize::from(id)];
    f(id, node);
    node.representative_of
        .iter()
        .for_each(|&id| visit_undo_node(id, undo_find, &mut *f))
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
struct PushInfo {
    node_count: Id,
    union_count: usize,
    explain_count: usize,
    memo_log_count: usize,
}

/// Value for [`Analysis::UndoLog`](crate::Analysis::UndoLog) that enables [`push`](EGraph::push) and
/// [`pop`](EGraph::pop)
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct UndoLog<L: Language> {
    undo_find: Vec<UndoNode>,
    union_log: Vec<Id>,
    explain_log: Vec<(Id, Id)>,
    memo_log: Vec<(L, Option<Id>)>,
    push_log: Vec<PushInfo>,
    // Scratch space, should be empty other that when inside `pop`
    #[cfg_attr(feature = "serde-1", serde(skip))]
    dirty: IndexSet<Id>,
}

impl<L: Language> Default for UndoLog<L> {
    fn default() -> Self {
        UndoLog {
            undo_find: Default::default(),
            union_log: Default::default(),
            explain_log: Default::default(),
            memo_log: Default::default(),
            push_log: Default::default(),
            dirty: Default::default(),
        }
    }
}

pub trait UndoLogT<L: Language>: Default + Debug {
    fn add_node(&mut self, node: &L, node_id: Id);

    fn union(&mut self, id1: Id, id2: Id);

    fn union_explain(&mut self, node1: Id, node2: Id);

    fn modify_memo(&mut self, memo: &mut HashMap<L, Id>, key: L, new_val: Option<Id>)
        -> Option<Id>;
}

impl<L: Language> UndoLogT<L> for UndoLog<L> {
    fn add_node(&mut self, node: &L, node_id: Id) {
        assert_eq!(self.undo_find.len(), usize::from(node_id));
        self.undo_find.push(UndoNode::default());
        for id in node.children() {
            self.undo_find[usize::from(*id)].parents.push(node_id)
        }
    }

    fn union(&mut self, id1: Id, id2: Id) {
        self.undo_find[usize::from(id1)].representative_of.push(id2);
        self.union_log.push(id1)
    }

    fn union_explain(&mut self, node1: Id, node2: Id) {
        self.explain_log.push((node1, node2));
    }

    fn modify_memo(
        &mut self,
        memo: &mut HashMap<L, Id>,
        key: L,
        new_val: Option<Id>,
    ) -> Option<Id> {
        let res = match new_val {
            None => memo.remove(&key),
            Some(id) => memo.insert(key.clone(), id),
        };
        self.memo_log.push((key, res));
        res
    }
}

impl<L: Language> UndoLogT<L> for () {
    fn add_node(&mut self, _: &L, _: Id) {}

    fn union(&mut self, _: Id, _: Id) {}

    fn union_explain(&mut self, _: Id, _: Id) {}

    fn modify_memo(
        &mut self,
        memo: &mut HashMap<L, Id>,
        key: L,
        new_val: Option<Id>,
    ) -> Option<Id> {
        match new_val {
            None => memo.remove(&key),
            Some(id) => memo.insert(key, id),
        }
    }
}

impl<L: Language> EGraph<L, WithUndo> {
    /// Push the current egraph off the stack
    /// Requires that the egraph is clean
    ///
    /// See [`EGraph::pop`]
    pub fn push(&mut self) {
        assert!(self.pending.is_empty() && self.analysis_pending.is_empty());
        let undo = &mut self.undo_log;
        undo.push_log.push(PushInfo {
            node_count: undo.undo_find.len().into(),
            union_count: undo.union_log.len(),
            explain_count: undo.explain_log.len(),
            memo_log_count: undo.memo_log.len(),
        })
    }

    /// Pop the current egraph off the stack, replacing
    /// it with the previously [`push`](EGraph::push)ed egraph
    ///
    /// ```
    /// use egg::{EGraph, SymbolLang, WithUndo};
    /// let mut egraph = EGraph::new(WithUndo).with_explanations_enabled();
    /// let a = egraph.add_uncanonical(SymbolLang::leaf("a"));
    /// let b = egraph.add_uncanonical(SymbolLang::leaf("b"));
    /// egraph.rebuild();
    /// egraph.push();
    /// egraph.union(a, b);
    /// assert_eq!(egraph.find(a), egraph.find(b));
    /// egraph.pop();
    /// assert_ne!(egraph.find(a), egraph.find(b));
    /// ```
    pub fn pop(&mut self) {
        self.pop_n(1);
    }

    /// Equivalent to calling [`pop`](EGraph::pop) `n` times but possibly more efficient
    pub fn pop_n(&mut self, count: usize) {
        if count == 0 {
            return;
        }
        self.pending.clear();
        self.analysis_pending.clear();
        let mut push_info = None;
        for _ in 0..count {
            push_info = self.undo_log.push_log.pop();
        }
        let PushInfo {
            node_count,
            union_count,
            explain_count,
            memo_log_count,
        } = push_info.unwrap_or_else(|| panic!("Not enough pushes to pop"));
        self.pop_memo(memo_log_count);
        self.pop_unions(union_count, node_count);
        self.pop_explain(explain_count);
        self.pop_nodes(usize::from(node_count));
    }

    fn pop_memo(&mut self, old_count: usize) {
        for (k, v) in self.undo_log.memo_log.drain(old_count..).rev() {
            match v {
                Some(v) => self.memo.insert(k, v),
                None => self.memo.remove(&k),
            };
        }
    }

    fn pop_unions(&mut self, old_count: usize, node_count: Id) {
        let explain = self.explain.as_mut().unwrap();
        explain.shortest_explanation_memo.clear();
        let undo = &mut self.undo_log;
        for id in undo.union_log.drain(old_count..) {
            let id2 = undo.undo_find[usize::from(id)]
                .representative_of
                .pop()
                .unwrap();
            for id in [id, id2] {
                if id < node_count {
                    undo.dirty.insert(id);
                }
            }
        }
        let very_dirty_count = undo.dirty.len();
        // Very dirty nodes were canonical in the state we are reverting to and were then unioned with other node
        // either becoming non-canonical or having there EClass merged so the their EClasses must be completely rebuilt
        // all the nodes they represented in the old state must have there parent field reset since it may have been
        // path-compressed using unions that are now being reverted
        for i in 0..very_dirty_count {
            let root = *undo.dirty.get_index(i).unwrap();
            let mut class = EClass {
                id: root,
                nodes: Default::default(),
                data: (),
                parents: Default::default(),
            };
            let union_find = &mut self.unionfind;
            let dirty = &mut undo.dirty;
            visit_undo_node(root, &undo.undo_find, &mut |id, node| {
                union_find.union(root, id);
                dirty.extend(node.parents.iter().copied().filter(|&id| id < node_count));
                class.parents.extend(
                    node.parents
                        .iter()
                        .map(|&id| (explain.node(id).clone(), id)),
                );
                class.nodes.push(explain.node(id).clone())
            });
            self.classes.insert(root, class);
            self.classes_by_op.values_mut().for_each(|ids| ids.clear());
        }

        let dirty_count = undo.dirty.len();
        // Dirty nodes are nodes that have very dirty children so canonicalization applied their `nodes` fields may no
        // longer be correct and must be reverted
        for i in very_dirty_count..dirty_count {
            let root = *undo.dirty.get_index(i).unwrap();
            let class = self.classes.get_mut(&root).unwrap();
            class.nodes.clear();
            visit_undo_node(root, &undo.undo_find, &mut |id, _| {
                class.nodes.push(explain.node(id).clone())
            });
        }
        undo.dirty.clear()
    }

    fn pop_explain(&mut self, old_count: usize) {
        if let Some(explain) = self.explain.as_mut() {
            for (node1, node2) in self
                .undo_log
                .explain_log
                .drain(old_count..)
                .rev()
                .flat_map(|(n1, n2)| [(n1, n2), (n2, n1)])
            {
                let exp_node = &mut explain.explainfind[usize::from(node1)];
                if exp_node.parent_connection.next == node2 {
                    exp_node.parent_connection = Connection::dummy(node1);
                }
                let c = exp_node.neighbors.pop().unwrap();
                debug_assert_eq!(c.next, node2);
            }
        } else {
            debug_assert!(self.undo_log.explain_log.is_empty())
        }
    }

    fn pop_nodes(&mut self, old_count: usize) {
        if let Some(explain) = self.explain.as_mut() {
            for x in explain.explainfind.drain(old_count..).rev() {
                explain.uncanon_memo.remove(&x.node);
            }
        }
        let new_count = self.undo_log.undo_find.len();
        for i in old_count..new_count {
            self.classes.remove(&Id::from(i));
        }
        self.undo_log.undo_find.truncate(old_count);
        self.unionfind.parents.truncate(old_count);
    }
}

#[test]
fn simple_push_pop() {
    use crate::{Pattern, Searcher, SymbolLang};
    use core::str::FromStr;
    crate::init_logger();
    let mut egraph = EGraph::new(WithUndo).with_explanations_enabled();

    let a = egraph.add_uncanonical(SymbolLang::leaf("a"));
    let fa = egraph.add_uncanonical(SymbolLang::new("f", vec![a]));
    let c = egraph.add_uncanonical(SymbolLang::leaf("c"));
    egraph.rebuild();
    egraph.push();
    let b = egraph.add_uncanonical(SymbolLang::leaf("b"));
    let _fb = egraph.add_uncanonical(SymbolLang::new("g", vec![b]));
    egraph.union_trusted(b, a, "b=a");
    egraph.union_trusted(b, c, "b=c");
    egraph.rebuild();
    assert_eq!(egraph.find(a), b);
    egraph.pop();
    assert_eq!(egraph.lookup(SymbolLang::leaf("a")), Some(a));
    assert_eq!(egraph.lookup(SymbolLang::new("f", vec![a])), Some(fa));
    assert_eq!(egraph.lookup(SymbolLang::leaf("b")), None);

    egraph.rebuild();
    let f_pat = Pattern::from_str("(f ?a)").unwrap();
    let s = f_pat.search(&egraph);

    assert_eq!(s.len(), 1);
    assert_eq!(s[0].substs.len(), 1);
    assert_eq!(s[0].substs[0].vec[0].1, a);
}

#[test]
fn push_pop_explain() {
    use crate::SymbolLang;
    crate::init_logger();
    let mut egraph = EGraph::new(WithUndo).with_explanations_enabled();

    let a = egraph.add_uncanonical(SymbolLang::leaf("a"));
    let b = egraph.add_uncanonical(SymbolLang::leaf("b"));
    let c = egraph.add_uncanonical(SymbolLang::leaf("c"));
    let d = egraph.add_uncanonical(SymbolLang::leaf("d"));
    egraph.union_trusted(a, b, "a=b");
    egraph.rebuild();
    let fa = egraph.add_uncanonical(SymbolLang::new("f", vec![a]));
    let fb = egraph.add_uncanonical(SymbolLang::new("f", vec![b]));
    egraph.union_trusted(c, fa, "c=fa");
    egraph.union_trusted(d, fb, "d=fb");
    egraph.rebuild();
    egraph.push();
    egraph.union_trusted(c, d, "bad");
    egraph.pop();
    let mut exp = egraph.explain_id_equivalence(c, d);
    assert_eq!(exp.make_flat_explanation().len(), 4);
}

#[test]
fn push_pop_explain2() {
    use crate::SymbolLang;
    crate::init_logger();
    let mut egraph = EGraph::new(WithUndo).with_explanations_enabled();

    let a = egraph.add_uncanonical(SymbolLang::leaf("a"));
    let b = egraph.add_uncanonical(SymbolLang::leaf("b"));
    let c = egraph.add_uncanonical(SymbolLang::leaf("c"));
    let d = egraph.add_uncanonical(SymbolLang::leaf("d"));
    let fa = egraph.add_uncanonical(SymbolLang::new("f", vec![a]));
    let fb = egraph.add_uncanonical(SymbolLang::new("f", vec![b]));
    egraph.union_trusted(c, fa, "c=fa");
    egraph.union_trusted(d, fb, "d=fb");
    egraph.rebuild();
    egraph.push();
    egraph.union_trusted(c, d, "bad");
    egraph.pop();
    egraph.union_trusted(a, b, "a=b");
    egraph.rebuild();
    let mut exp = egraph.explain_id_equivalence(c, d);
    assert_eq!(exp.make_flat_explanation().len(), 4);
}

#[test]
fn push_pop_explain3() {
    use crate::SymbolLang;
    crate::init_logger();
    let mut egraph = EGraph::new(WithUndo).with_explanations_enabled();

    let a = egraph.add_uncanonical(SymbolLang::leaf("a"));
    let b = egraph.add_uncanonical(SymbolLang::leaf("b"));
    let c = egraph.add_uncanonical(SymbolLang::leaf("c"));
    let fa = egraph.add_uncanonical(SymbolLang::new("f", vec![a]));
    egraph.rebuild();
    egraph.push();
    egraph.union_trusted(a, b, "a=b");
    let _ = egraph.add_uncanonical(SymbolLang::new("f", vec![b]));
    egraph.rebuild();
    egraph.pop();
    let fb = egraph.add_uncanonical(SymbolLang::new("f", vec![b]));
    egraph.union_trusted(fb, c, "fb=c");
    egraph.union_trusted(c, fa, "c=fa");
    egraph.rebuild();
    let mut exp = egraph.explain_id_equivalence(fa, fb);
    assert_eq!(exp.make_flat_explanation().len(), 3);
}
