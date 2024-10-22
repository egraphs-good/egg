use std::{cell::RefCell, collections::VecDeque, hash::{Hash, Hasher}, ops::{Add, AddAssign, Sub, SubAssign}, rc::Rc, u32};

use hashbrown::{HashMap, HashSet};

use crate::StopReason;

type State = u32;
type Symbol = u32;

const EMPTY: State = 0;

#[derive(Debug)]
struct SymbolicRule {
    symbol: Symbol,
    input: Vec<State>,
    output: State
}

impl SymbolicRule {
    fn new(symbol: Symbol, input: Vec<State>, output: State) -> SymbolicRule {
        return SymbolicRule {
            symbol,
            input,
            output
        };
    }
}

type SymbolicRulePtr = Rc<RefCell<SymbolicRule>>;

#[derive(Debug)]
struct TransitionTable {
    rules: Vec<SymbolicRulePtr>,
    state_to_rule: HashMap<State, Vec<SymbolicRulePtr>>
}

impl TransitionTable {
    fn new(rules: Vec<SymbolicRule>) -> TransitionTable {
        let mut table_rules: Vec<SymbolicRulePtr> = Vec::new();
        let mut table_state_map: HashMap<State, Vec<SymbolicRulePtr>> = HashMap::new();
        for rule in rules {
            let current_rule: SymbolicRulePtr = Rc::new(RefCell::new(rule));
            table_rules.push(current_rule.clone());
            table_state_map.entry(current_rule.borrow().output).or_insert(Vec::new()).push(current_rule.clone());
        }
        return TransitionTable {
            rules: table_rules,
            state_to_rule: table_state_map
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Hash)]
struct Hash64(u64);

impl Hash64 {
    pub fn new(value: u64) -> Self {
        Hash64(value)
    }
    pub fn accumulate(&mut self, value: u64) {
        self.0 = self.0.wrapping_add(value);
    }
}

impl Add<u64> for Hash64 {
    type Output = Self;

    fn add(self, other: u64) -> Self::Output {
        Hash64(self.0.wrapping_add(other))
    }
}

impl AddAssign<u64> for Hash64 {
    fn add_assign(&mut self, other: u64) {
        self.0 = self.0.wrapping_add(other);
    }
}

impl Sub<u64> for Hash64 {
    type Output = Self;

    fn sub(self, other: u64) -> Self::Output {
        Hash64(self.0.wrapping_sub(other))
    }
}

impl SubAssign<u64> for Hash64 {
    fn sub_assign(&mut self, other: u64) {
        self.0 = self.0.wrapping_sub(other);
    }
}

struct Context {
    //change hash in O(1)
    elements: Vec<State>,
    empty_index: usize,
    stored_hash: Hash64
}

impl Context {
    fn new(elements: Vec<State>, empty_index: usize) -> Self {
        let stored_hash: Hash64 = elements.iter().cloned().fold(Hash64::new(0), |mut acc, value| {
            acc.accumulate(value as u64);
            acc
        });
        let mut result: Context = Context {
            elements,
            empty_index,
            stored_hash
        };
        result.replace_element_with_empty(empty_index);
        return result;
    }
    fn replace_empty_element(&mut self, element: State) {
        let element_hash = self.hash_element(EMPTY, self.empty_index);
        self.stored_hash -= element_hash;
        let element_hash = self.hash_element(element, self.empty_index);
        self.stored_hash += element_hash;

        self.elements[self.empty_index] = element;
        self.empty_index = self.elements.len();
    }
    fn replace_element_with_empty(&mut self, index: usize) {
        let element_hash = self.hash_element(self.elements[index], index);
        self.stored_hash -= element_hash;
        let element_hash = self.hash_element(EMPTY, index);
        self.stored_hash += element_hash;

        self.empty_index = index;
        self.elements[self.empty_index] = EMPTY;
    }
    fn hash_element(&mut self, element: State, index: usize) -> u64 {
        let mut result: u64 = element as u64;
        result = (result ^ (result >> 30)) * 0xbf58476d1ce4e5b9;
        result = (result ^ (result >> 27)) * 0x94d049bb133111eb;
        result = result ^ (result >> 31);
        result = result.rotate_left((index % 32) as u32);
        return result;
    }
}

impl Hash for Context {
    fn hash<H: Hasher>(&self, state: &mut H) {
        return self.stored_hash.hash(state);
    }
}

impl PartialEq for Context {
    fn eq(&self, other: &Self) -> bool {
        if self.stored_hash != other.stored_hash {
            return false;
        }
        return self.empty_index == other.empty_index && self.elements == other.elements;
    }
}

impl Eq for Context {}

type FineBlockId = u32;

#[derive(Debug)]
struct FineBlock {
    id: FineBlockId,
    elements: HashSet<State>
}

impl FineBlock {
    fn size(&self) -> usize {
        return self.elements.len();
    }
}

type CoarsePartitionPtr = Rc<RefCell<CoarsePartition>>;
type FinePartitionPtr = Rc<RefCell<FinePartition>>;
type TransitionTablePtr = Rc<RefCell<TransitionTable>>;

#[derive(Debug)]
struct FinePartition {
    id_to_block: HashMap<FineBlockId, FineBlock>,
    state_to_block: HashMap<State, FineBlockId>,
    coarse_partition_ptr: CoarsePartitionPtr,
    transition_table_ptr: TransitionTablePtr
    free_ids: VecDeque<FineBlockId>
}

impl FinePartition {
    fn new(coarse_partition: CoarsePartitionPtr, transition_table: TransitionTablePtr, q: &HashSet<State>, f: &HashSet<State>) -> Self {
        let id: FineBlockId = 0;
        let block: FineBlock = FineBlock {
            id,
            elements: q.clone()
        };
        let mut result: Self = FinePartition {
            id_to_block: HashMap::new(),
            state_to_block: HashMap::new(),
            coarse_partition_ptr: coarse_partition,
            transition_table_ptr: transition_table,
            free_ids: VecDeque::new()
        };
        result.id_to_block.insert(id, block);
        for &state in q {
            result.state_to_block.insert(state, id);
        }
        result.splitf(id);

        let mut states_to_cut: HashMap<FineBlockId, Vec<State>> = HashMap::new();

        for (id, block) in &result.id_to_block {
            for state in &block.elements {
                if f.contains(state) {
                    states_to_cut.entry(id.clone()).or_insert(Vec::new()).push(state.clone());
                }
            }
        }

        for (id, state_vec) in &states_to_cut {
            result.cut_from_set(id, state_vec);
        }

        return result;
    }
    fn get_equiv_classes(&self) -> Vec<Vec<State>> {
        todo!();
    }
    fn get_free_id(&mut self) -> FineBlockId {
        if self.free_ids.is_empty() {
            return self.id_to_block.len() as FineBlockId;
        }
        return self.free_ids.pop_front().unwrap();
    }
    fn get_block(&self, id: FineBlockId) -> &FineBlock {
        assert!(self.id_to_block.contains_key(&id));
        return self.id_to_block.get(&id).unwrap();
    }
    fn get_block_mut(&mut self, id: FineBlockId) -> &mut FineBlock {
        assert!(self.id_to_block.contains_key(&id));
        return self.id_to_block.get_mut(&id).unwrap();
    }
    fn fine_block_ids(&self) -> Vec<FineBlockId> {
        return self.id_to_block.keys().cloned().collect();
    }
    fn get_block_size(&self, id: FineBlockId) -> usize {
        assert!(self.id_to_block.contains_key(&id));
        return self.id_to_block.get(&id).unwrap().size();
    }
    fn splitf(&mut self, b: FineBlockId) {
        todo!();
        //loop transition rules
        //init context
        //loop args and change hash in O(1)
        //observations: state -> context -> count
        //for each context: map obskey -> vec state
        //loop through map, divide
    }
    fn splitfn(&mut self, s: CoarseBlockId, b: FineBlockId) {
        todo!();
    }
    fn cut_from_set(&mut self, b: &FineBlockId, set: &Vec<State>) {
        assert!(self.id_to_block.contains_key(b));
        {
            let block: &mut FineBlock = self.get_block_mut(b.clone());
            assert!(set.iter().all(|&state| block.elements.contains(&state)));

            if set.len() == block.elements.len() {
                return;
            }
        }

        let new_block_id: FineBlockId = self.get_free_id();
        let new_block: FineBlock = FineBlock {
            id: new_block_id,
            elements: set.iter().cloned().collect()
        };

        {
            let block: &mut FineBlock = self.get_block_mut(b.clone());

            for state in set {
                block.elements.remove(state);
            }
        }

        for state in set {
            self.state_to_block.insert(state.clone(), new_block_id);
        }

        self.id_to_block.insert(new_block_id, new_block);
        self.coarse_partition_ptr.borrow_mut().alert_fine_block_split(*b, new_block_id);
    }
}

type CoarseBlockId = u32;

#[derive(Debug)]
struct CoarseBlock {
    id: CoarseBlockId,
    elements: HashSet<FineBlockId>,
}

impl CoarseBlock {
    fn remove(&mut self, fine_id: FineBlockId) {
        assert!(self.elements.contains(&fine_id));
        self.elements.remove(&fine_id);
    }
    fn insert(&mut self, fine_id: FineBlockId) {
        assert!(!self.elements.contains(&fine_id));
        self.elements.insert(fine_id);
    }
    fn len(&self) -> usize {
        return self.elements.len();
    }
}

#[derive(Debug)]
struct CoarsePartition {
    id_to_block: HashMap<CoarseBlockId, CoarseBlock>,
    fine_id_to_id: HashMap<FineBlockId, CoarseBlockId>,
    compound_blocks: HashSet<CoarseBlockId>,
    fine_partition: Option<FinePartitionPtr>,
    free_ids: VecDeque<CoarseBlockId>
}

impl CoarsePartition {
    fn new() -> Self {
        return CoarsePartition {
            id_to_block: HashMap::new(),
            fine_id_to_id: HashMap::new(),
            compound_blocks: HashSet::new(),
            fine_partition: None,
            free_ids: VecDeque::new()
        };
    }
    fn add_block(&mut self, fine_id: FineBlockId) {
        assert!(!self.fine_id_to_id.contains_key(&fine_id));
        let new_id: CoarseBlockId = self.get_free_id();
        let new_block: CoarseBlock = CoarseBlock {
            id: new_id,
            elements: HashSet::from([fine_id])
        };
        self.fine_id_to_id.insert(fine_id, new_id);
        self.id_to_block.insert(new_id, new_block);
    }
    fn get_free_id(&mut self) -> CoarseBlockId {
        if self.free_ids.is_empty() {
            return self.id_to_block.len() as CoarseBlockId;
        }
        return self.free_ids.pop_front().unwrap();
    }
    fn remove_empty_block(&mut self, id: CoarseBlockId) {
        assert!(self.id_to_block.contains_key(&id));
        assert_eq!(self.id_to_block.get(&id).unwrap().len(), 0);
        self.id_to_block.remove(&id);
        self.free_ids.push_back(id);
    }
    fn remove_fine_id(&mut self, fine_id: FineBlockId) {
        assert!(self.fine_id_to_id.contains_key(&fine_id));
        let id: CoarseBlockId = self.fine_id_to_id.get(&fine_id).unwrap().clone();

        let block: &mut CoarseBlock = self.id_to_block.get_mut(&id).unwrap();
        block.remove(fine_id);
        match block.len() {
            0 => {self.remove_empty_block(id);},
            1 => {self.compound_blocks.remove(&id);},
            _ => {}
        }
        self.fine_id_to_id.remove(&fine_id);
    }
    fn set_fine_partition(&mut self, fine_partition: FinePartitionPtr) {
        self.fine_partition = Some(fine_partition);
    }
    fn num_compound_blocks(&self) -> usize {
        return self.compound_blocks.len();
    }
    fn choose_compound_block(&self) -> CoarseBlockId {
        assert!(self.num_compound_blocks() != 0);
        return self.compound_blocks.iter().cloned().next().unwrap();
    }
    fn choose_smaller_half(&self, b: CoarseBlockId) -> FineBlockId {
        assert!(self.compound_blocks.contains(&b));
        assert!(self.fine_partition.is_some());
        let b_block: &CoarseBlock = self.get_block(b);
        let first_fine_id: FineBlockId = b_block.elements.get(&0).unwrap().clone();
        let second_fine_id: FineBlockId = b_block.elements.get(&1).unwrap().clone();

        let fine_partition = self.fine_partition.as_ref().unwrap().borrow();

        if fine_partition.get_block_size(first_fine_id) < fine_partition.get_block_size(second_fine_id) {
            return first_fine_id;
        }
        return second_fine_id;
    }
    fn get_block(&self, id: CoarseBlockId) -> &CoarseBlock {
        assert!(self.id_to_block.contains_key(&id));
        return self.id_to_block.get(&id).unwrap();
    }
    fn get_block_mut(&mut self, id: CoarseBlockId) -> &mut CoarseBlock {
        assert!(self.id_to_block.contains_key(&id));
        return self.id_to_block.get_mut(&id).unwrap();
    }
    fn cut(&mut self, b: FineBlockId) {
        self.remove_fine_id(b);
        self.add_block(b);
    }
    fn alert_fine_block_split(&mut self, original: FineBlockId, new: FineBlockId) {
        assert!(self.fine_id_to_id.contains_key(&original));
        assert!(!self.fine_id_to_id.contains_key(&new));
        let id: CoarseBlockId = self.fine_id_to_id.get(&original).unwrap().clone();

        self.get_block_mut(id).insert(new);
    }
}

#[derive(Debug)]
pub struct DTFA {
    states: HashSet<State>,
    accepting_states: HashSet<State>,
    transition_table: TransitionTablePtr
}

impl DTFA {
    fn new(states: HashSet<State>, accepting_states: HashSet<State>, rules: Vec<SymbolicRule>) -> Self {
        assert!(!states.contains(&EMPTY));
        assert!(!accepting_states.contains(&EMPTY));
        return DTFA {
            states,
            accepting_states,
            transition_table: Rc::new(RefCell::new(TransitionTable::new(rules)))
        };
    }
    fn minimize(&self) -> Vec<Vec<State>> {
        let p: CoarsePartitionPtr = Rc::new(RefCell::new(CoarsePartition::new()));
        let r: FinePartitionPtr = Rc::new(RefCell::new(FinePartition::new(
                    p.clone(), self.transition_table.clone(), &self.states, &self.accepting_states
        )));

        while p.borrow_mut().num_compound_blocks() != 0 {
            let s: CoarseBlockId = p.borrow().choose_compound_block();
            let b: FineBlockId = p.borrow().choose_smaller_half(s);
            p.borrow_mut().cut(b);
            r.borrow_mut().splitf(b);
            r.borrow_mut().splitfn(s, b);
        }

        return r.borrow().get_equiv_classes();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dtfa() {
        print!("TESTING DTFA");
    }
}
