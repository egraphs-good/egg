use std::{cell::RefCell, collections::VecDeque, hash::{Hash, Hasher}, ops::{Add, AddAssign, Sub, SubAssign}, rc::Rc, u32};

use hashbrown::{HashMap, HashSet};

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
    pub fn new(rules: Vec<SymbolicRule>) -> TransitionTable {
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

type ContextId = u32;

#[derive(Debug, Clone)]
struct Context {
    //change hash in O(1)
    symbol: Symbol,
    //elements doesn't change after initialization
    elements: Vec<State>,
    empty_index: usize,
    stored_hash: Hash64
}

struct ContextIndexIterator {
    index: usize,
    length: usize
}

impl Iterator for ContextIndexIterator {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.length {
            let index = self.index;
            self.index += 1;
            Some(index)
        } else {
            None
        }
    }
}

impl Context {
    fn new(symbol: Symbol, elements: Vec<State>, empty_index: usize) -> Self {
        let mut stored_hash: Hash64 = Hash64::new(Self::hash_symbol(symbol));
        for (index, state) in elements.iter().cloned().enumerate() {
            stored_hash += Self::hash_element(state, index);
        }
        let mut result: Context = Context {
            symbol,
            elements,
            empty_index,
            stored_hash
        };
        result.replace_element_with_empty(empty_index);
        return result;
    }
    fn index_iter(&self) -> ContextIndexIterator {
        return ContextIndexIterator {
            index: 0,
            length: self.elements.len()
        };
    }
    fn hash_element(element: State, index: usize) -> u64 {
        let mut result: u64 = element as u64;
        result = (result ^ (result >> 30)) * 0xbf58476d1ce4e5b9;
        result = (result ^ (result >> 27)) * 0x94d049bb133111eb;
        result = result ^ (result >> 31);
        result = result.rotate_left((index % 32) as u32);
        return result;
    }
    fn hash_symbol(symbol: Symbol) -> u64 {
        let mut result: u64 = symbol as u64;
        result = (result ^ (result >> 30)) * 0xbf58476d1ce4e5b9;
        result = (result ^ (result >> 27)) * 0x94d049bb133111eb;
        result = result ^ (result >> 31);
        return result;
    }
    fn replace_empty_element(&mut self) {
        let element_hash = Self::hash_element(EMPTY, self.empty_index);
        self.stored_hash -= element_hash;
        let element_hash = Self::hash_element(self.elements[self.empty_index], self.empty_index);
        self.stored_hash += element_hash;

        self.empty_index = self.elements.len();
    }
    fn replace_element_with_empty(&mut self, index: usize) {
        let element_hash = Self::hash_element(self.elements[index], index);
        self.stored_hash -= element_hash;
        let element_hash = Self::hash_element(EMPTY, index);
        self.stored_hash += element_hash;

        self.empty_index = index;
    }
    fn move_empty_index(&mut self, index: usize) {
        self.replace_empty_element();
        self.replace_element_with_empty(index);
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
        return self.symbol == other.symbol &&
            self.empty_index == other.empty_index &&
            self.elements == other.elements;
    }
}

impl Eq for Context {}

struct ContextSet {
    elements: HashSet<ContextId>,
    stored_hash: Hash64
}

impl ContextSet {
    fn new(elements: Vec<ContextId>) -> Self {
        let stored_hash: Hash64 = elements.iter().fold(Hash64(0), |acc, &num| acc + Self::hash_element(num));
        return ContextSet {
            elements: elements.into_iter().collect(),
            stored_hash
        };
    }
    fn new_empty() -> Self {
        return ContextSet {
            elements: HashSet::new(),
            stored_hash: Hash64(0)
        };
    }
    fn hash_element(element: ContextId) -> u64 {
        let mut result: u64 = element as u64;
        result = (result ^ (result >> 30)) * 0xbf58476d1ce4e5b9;
        result = (result ^ (result >> 27)) * 0x94d049bb133111eb;
        result = result ^ (result >> 31);
        return result;
    }
    fn insert(&mut self, element: ContextId) {
        if self.elements.insert(element) {
            self.stored_hash += Self::hash_element(element);
        }
    }
    fn remove(&mut self, element: ContextId) {
        if self.elements.remove(&element) {
            self.stored_hash -= Self::hash_element(element);
        }
    }
}

impl Hash for ContextSet {
    fn hash<H: Hasher>(&self, state: &mut H) {
        return self.stored_hash.hash(state);
    }
}

impl PartialEq for ContextSet {
    fn eq(&self, other: &Self) -> bool {
        if self.stored_hash != other.stored_hash {
            return false;
        }
        return self.elements == other.elements;
    }
}

impl Eq for ContextSet {}

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
    fn contains(&self, state: State) -> bool {
        return self.elements.contains(&state);
    }
}

type CoarsePartitionPtr = Rc<RefCell<CoarsePartition>>;
type FinePartitionPtr = Rc<RefCell<FinePartition>>;
type TransitionTablePtr = Rc<RefCell<TransitionTable>>;

type ObservationMap = HashMap<State, HashMap<Context, u32>>;

#[derive(Debug)]
struct FinePartition {
    id_to_block: HashMap<FineBlockId, FineBlock>,
    state_to_block: HashMap<State, FineBlockId>,
    context_to_id: HashMap<Context, ContextId>,
    coarse_partition_ptr: CoarsePartitionPtr,
    transition_table_ptr: TransitionTablePtr,
    free_ids: VecDeque<FineBlockId>
}

impl FinePartition {
    fn new(coarse_partition: CoarsePartitionPtr, transition_table: TransitionTablePtr, q: &HashSet<State>, f: &HashSet<State>) -> Self {
        let q_id: FineBlockId = 0;
        let block: FineBlock = FineBlock {
            id: q_id,
            elements: q.clone()
        };
        let mut result: Self = FinePartition {
            id_to_block: HashMap::new(),
            state_to_block: HashMap::new(),
            context_to_id: HashMap::new(),
            coarse_partition_ptr: coarse_partition.clone(),
            transition_table_ptr: transition_table.clone(),
            free_ids: VecDeque::new()
        };

        //Insert all Q states
        result.id_to_block.insert(q_id, block);
        for &state in q {
            result.state_to_block.insert(state, q_id);
        }

        //splitf(Q)
        result.splitf(q_id);

        //separate F accepting states
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
    fn get_context_id(&mut self, context: &Context) -> ContextId {
        let context_id: u32 = self.context_to_id.len() as u32;
        if !self.context_to_id.contains_key(context) {
            self.context_to_id.insert(context.clone(), context_id);
        }
        return self.context_to_id.get(context).unwrap().clone();
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
    fn cut_from_set(&mut self, b: &FineBlockId, set: &Vec<State>) {
        //b must be valid
        assert!(self.id_to_block.contains_key(b));
        //all elements in set must be in block b
        {
            let block: &mut FineBlock = self.get_block_mut(*b);
            assert!(set.iter().all(|&state| block.contains(state)));

            //don't split if equal
            if set.len() == block.size() {
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
    fn generate_obs(&self, block_id: FineBlockId) -> ObservationMap {
        todo!();
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
        assert!(self.coarse_partition_ptr.borrow().get_block(s).contains(b));
        let s_obsmap: &mut ObservationMap = self.coarse_partition_ptr.borrow_mut().obs_q.get_mut(&s).unwrap();
        let b_obsmap: ObservationMap = self.generate_obs(b);


        
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
    fn contains(&self, fine_id: FineBlockId) -> bool {
        return self.elements.contains(&fine_id);
    }
    fn size(&self) -> usize {
        return self.elements.len();
    }
}

#[derive(Debug)]
struct CoarsePartition {
    id_to_block: HashMap<CoarseBlockId, CoarseBlock>,
    fine_id_to_id: HashMap<FineBlockId, CoarseBlockId>,
    compound_blocks: HashSet<CoarseBlockId>,
    fine_partition: Option<FinePartitionPtr>,
    free_ids: VecDeque<CoarseBlockId>,
    obs_q: HashMap<CoarseBlockId, ObservationMap>
}

impl CoarsePartition {
    fn new() -> Self {
        return CoarsePartition {
            id_to_block: HashMap::new(),
            fine_id_to_id: HashMap::new(),
            compound_blocks: HashSet::new(),
            fine_partition: None,
            free_ids: VecDeque::new(),
            obs_q: HashMap::new()
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
        assert_eq!(self.id_to_block.get(&id).unwrap().size(), 0);
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
            r.borrow_mut().splitf(b);
            r.borrow_mut().splitfn(s, b);

            //cut coarse partition after processing fine partition
            //obs counts for coarse blocks are needed for splitfn
            p.borrow_mut().cut(b);
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
