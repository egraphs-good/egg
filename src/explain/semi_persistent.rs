use crate::explain::{Connection, Explain};
use crate::raw::EGraphResidual;
use crate::{Id, Language};

pub(super) type UndoLog = Option<Vec<Id>>;

#[derive(Default, Clone, Debug)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub(crate) struct PushInfo(usize);

impl<L: Language> Explain<L> {
    pub(super) fn undo_log_union(&mut self, node: Id) {
        if let Some(x) = &mut self.undo_log {
            x.push(node)
        }
    }
    pub(crate) fn enable_undo_log(&mut self) {
        assert_eq!(self.explainfind.len(), 0);
        self.undo_log = Some(Vec::new());
    }

    pub(crate) fn disable_undo_log(&mut self) {
        self.undo_log = None
    }

    pub(crate) fn push(&self) -> PushInfo {
        PushInfo(self.undo_log.as_ref().unwrap().len())
    }

    pub(crate) fn pop(
        &mut self,
        info: PushInfo,
        number_of_uncanon_nodes: usize,
        egraph: &EGraphResidual<L>,
    ) {
        for id in self.undo_log.as_mut().unwrap().drain(info.0..).rev() {
            let node1 = &mut self.explainfind[usize::from(id)];
            let id2 = node1.neighbors.pop().unwrap().next;
            if node1.parent_connection.next == id2 {
                node1.parent_connection = Connection::end(id);
            }
            let node2 = &mut self.explainfind[usize::from(id2)];
            let id1 = node2.neighbors.pop().unwrap().next;
            assert_eq!(id, id1);
            if node2.parent_connection.next == id1 {
                node2.parent_connection = Connection::end(id2);
            }
        }
        self.explainfind.truncate(number_of_uncanon_nodes);
        // We can't easily undo memoize operations, so we just clear them
        self.shortest_explanation_memo.clear();
        dbg!(egraph.dump_uncanonical());
        dbg!(&self.uncanon_memo);
        for (id, node) in egraph.uncanonical_nodes().skip(number_of_uncanon_nodes) {
            if *self.uncanon_memo.get(node).unwrap() == id {
                self.uncanon_memo.remove(node).unwrap();
            }
        }
    }

    pub(crate) fn clear_memo(&mut self) {
        self.shortest_explanation_memo.clear()
    }

    pub(crate) fn clear(&mut self) {
        if let Some(v) = &mut self.undo_log {
            v.clear()
        }
        self.explainfind.clear();
        self.uncanon_memo.clear();
        self.shortest_explanation_memo.clear();
    }
}
