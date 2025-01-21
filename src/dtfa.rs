#![allow(dead_code)]

use std::{cell::RefCell, collections::VecDeque, hash::{Hash, Hasher}, ops::{Add, AddAssign, Sub, SubAssign}, rc::Rc, u32};

use derivative::Derivative;
use hashbrown::{HashMap, HashSet};

type State = u32;
type Symbol = u32;

/* 0 is a reserved state */
const EMPTY: State = 0;

/* symbol (input[0],input[1],...) -> output */
#[derive(Debug, Clone)]
pub struct SymbolicRule {
    symbol: Symbol,
    input: Vec<State>,
    output: State
}

impl SymbolicRule {
    pub fn new(symbol: Symbol, input: Vec<State>, output: State) -> SymbolicRule {
        return SymbolicRule {
            symbol,
            input,
            output
        };
    }
}

type SymbolicRulePtr = Rc<RefCell<SymbolicRule>>;

/* list of rules and maps each output state q to rules f(...) -> q */
#[derive(Debug)]
pub struct TransitionTable {
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
    pub fn rule_iter_by_output(&self, state: State) -> impl Iterator<Item = &SymbolicRulePtr> {
        if !self.state_to_rule.contains_key(&state) {
            return [].iter();
        }
        return self.state_to_rule.get(&state).unwrap().iter();
    }
}

/* additive hash type, overflows and underflows wrap around */
#[derive(Debug, Clone, Copy, PartialEq, Hash)]
pub struct Hash64(u64);

impl Hash64 {
    fn new(value: u64) -> Self {
        Hash64(value)
    }
    fn accumulate(&mut self, value: u64) {
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

/* f(input[0],q,input[2],...) -> q'
 * Formal def of context c[q] is (input[0],[],...)
 * where [] is the special empty symbol.
 * In obsf and obsfn, context is always used with
 * symbol f so Context struct keeps them together.
 *
 * Hash computed in O(|elements|) and hash is changed
 * in O(1) for each element changed. Changing location
 * of special symbol [] also only takes O(1).
 */
#[derive(Debug, Clone)]
pub struct Context {
    symbol: Symbol,
    elements: Vec<State>,
    empty_index: usize,
    stored_hash: Hash64
}

impl Context {
    pub fn new(symbol: Symbol, elements: Vec<State>, empty_index: usize) -> Self {
        let mut stored_hash: Hash64 = Hash64::new(Self::hash_symbol(symbol));
        for (index, state) in elements.iter().cloned().enumerate() {
            stored_hash += Self::hash_element(state, index);
        }
        let element_count = elements.len();
        let mut result: Context = Context {
            symbol,
            elements,
            empty_index,
            stored_hash
        };
        if element_count != 0 {
            result.replace_element_with_empty(empty_index);
        }
        return result;
    }
    pub fn elements_iter(&self) -> impl Iterator<Item = &State>{
        return self.elements.iter();
    }
    /* Stole this from stack overflow,
     * added rotate_left to make index
     * relevant in hash computation to
     * make collisions less likely.
     */
    pub fn hash_element(element: State, index: usize) -> u64 {
        let mut result: u64 = element as u64;
        result = (result ^ (result >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        result = (result ^ (result >> 27)).wrapping_mul(0x94d049bb133111eb);
        result = result ^ (result >> 31);
        result = result.rotate_left((index % 32) as u32);
        return result;
    }
    pub fn hash_symbol(symbol: Symbol) -> u64 {
        let mut result: u64 = symbol as u64;
        result = (result ^ (result >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        result = (result ^ (result >> 27)).wrapping_mul(0x94d049bb133111eb);
        result = result ^ (result >> 31);
        return result;
    }
    pub fn replace_empty_element(&mut self) {
        let element_hash = Self::hash_element(EMPTY, self.empty_index);
        self.stored_hash -= element_hash;
        let element_hash = Self::hash_element(self.elements[self.empty_index], self.empty_index);
        self.stored_hash += element_hash;

        self.empty_index = self.elements.len();
    }
    pub fn replace_element_with_empty(&mut self, index: usize) {
        let element_hash = Self::hash_element(self.elements[index], index);
        self.stored_hash -= element_hash;
        let element_hash = Self::hash_element(EMPTY, index);
        self.stored_hash += element_hash;

        self.empty_index = index;
    }
    pub fn move_empty_index(&mut self, index: usize) {
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
        if self.symbol != other.symbol ||
        self.empty_index != other.empty_index {
            return false;
        }
        /* Check if all elements are equal.
         * Empty index represents the special
         * symbol [] so skip. 
         */
        let skip_index = self.empty_index;
        for (i, (a, b)) in self.elements_iter().zip(other.elements_iter()).enumerate() {
            if i != skip_index && a != b {
                return false;
            }
        }
        return true;
    }
}

impl Eq for Context {}

/* ContextId assigned to every unique context.
 * ContextSet represents set of contexts to
 * use as key in hash table. Assume ContextIds
 * are accurate and leaves up to user to ensure
 * correct usage.
 */
#[derive(Clone)]
pub struct ContextSet {
    elements: HashSet<ContextId>,
    stored_hash: Hash64
}

impl ContextSet {
    pub fn new(elements: Vec<ContextId>) -> Self {
        let stored_hash: Hash64 = elements.iter().fold(Hash64(0), |acc, &num| acc + Self::hash_element(num));
        return ContextSet {
            elements: elements.into_iter().collect(),
            stored_hash
        };
    }
    pub fn new_empty() -> Self {
        return ContextSet {
            elements: HashSet::new(),
            stored_hash: Hash64(0)
        };
    }
    pub fn hash_element(element: ContextId) -> u64 {
        let mut result: u64 = element as u64;
        result = (result ^ (result >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        result = (result ^ (result >> 27)).wrapping_mul(0x94d049bb133111eb);
        result = result ^ (result >> 31);
        return result;
    }
    pub fn insert(&mut self, element: ContextId) {
        if self.elements.insert(element) {
            self.stored_hash += Self::hash_element(element);
        }
    }
    pub fn remove(&mut self, element: ContextId) {
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

#[derive(Debug, Clone)]
pub struct FineBlock {
    id: FineBlockId,
    elements: HashSet<State>
}

impl FineBlock {
    pub fn size(&self) -> usize {
        return self.elements.len();
    }
    pub fn contains(&self, state: State) -> bool {
        return self.elements.contains(&state);
    }
    pub fn elements_iter(&self) -> impl Iterator<Item = &State>{
        return self.elements.iter();
    }
}

type CoarsePartitionPtr = Rc<RefCell<CoarsePartition>>;
type FinePartitionPtr = Rc<RefCell<FinePartition>>;
type TransitionTablePtr = Rc<RefCell<TransitionTable>>;

type ObservationMap = HashMap<State, HashMap<ContextId, u32>>;

#[derive(Derivative)]
#[derivative(Debug)]
pub struct FinePartition {
    id_to_block: HashMap<FineBlockId, FineBlock>,
    state_to_block: HashMap<State, FineBlockId>,
    context_to_id: HashMap<Context, ContextId>,
    /* CoarseBlock -> State -> Context -> Count
     * q states in Coarse Block
     * for all rules f(s1,s2,...) -> q where q in
     * block: count obs for si
     */
    obs_q: HashMap<CoarseBlockId, ObservationMap>,
    #[derivative(Debug="ignore")]
    coarse_partition_ptr: CoarsePartitionPtr,
    transition_table_ptr: TransitionTablePtr,
    free_ids: VecDeque<FineBlockId>
}

impl FinePartition {
    pub fn new(coarse_partition: CoarsePartitionPtr, transition_table: TransitionTablePtr, q: &HashSet<State>, f: &HashSet<State>) -> Self {
        let q_id: FineBlockId = 0;
        let block: FineBlock = FineBlock {
            id: q_id,
            elements: q.clone()
        };
        let mut result: Self = FinePartition {
            id_to_block: HashMap::new(),
            state_to_block: HashMap::new(),
            context_to_id: HashMap::new(),
            obs_q: HashMap::new(),
            coarse_partition_ptr: coarse_partition.clone(),
            transition_table_ptr: transition_table.clone(),
            free_ids: VecDeque::new()
        };

        //Generate ObsMap for Q
        let coarse_id: CoarseBlockId = coarse_partition.borrow_mut().add_block(q_id);
        //Can use generate_obs because fine_block is not split yet
        let p0_obsmap: ObservationMap = result.generate_obs(&block);

        result.obs_q.insert(coarse_id, p0_obsmap);

        //Insert all Q states and add fine_block
        result.id_to_block.insert(q_id, block);
        for &state in q {
            result.state_to_block.insert(state, q_id);
        }

        //splitf(Q)
        result.splitf(result.get_block(q_id).clone());

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
    pub fn get_block_id_from_state(&self, state: State) -> FineBlockId {
        return *self.state_to_block.get(&state).unwrap();
    }
    pub fn get_equiv_classes(&self) -> Vec<Vec<State>> {
        let mut result: Vec<Vec<State>> = Vec::new();

        for (_, block) in self.id_to_block.iter() {
            result.push(block.elements_iter().cloned().collect());
        }

        return result;
    }
    pub fn get_context_id(&mut self, context: &Context) -> ContextId {
        let context_id: u32 = self.context_to_id.len() as u32;
        if !self.context_to_id.contains_key(context) {
            self.context_to_id.insert(context.clone(), context_id);
        }
        return self.context_to_id.get(context).unwrap().clone();
    }
    pub fn get_free_id(&mut self) -> FineBlockId {
        if self.free_ids.is_empty() {
            return self.id_to_block.len() as FineBlockId;
        }
        return self.free_ids.pop_front().unwrap();
    }
    pub fn get_block(&self, id: FineBlockId) -> &FineBlock {
        assert!(self.id_to_block.contains_key(&id));
        return self.id_to_block.get(&id).unwrap();
    }
    pub fn get_block_mut(&mut self, id: FineBlockId) -> &mut FineBlock {
        assert!(self.id_to_block.contains_key(&id));
        return self.id_to_block.get_mut(&id).unwrap();
    }
    pub fn fine_block_ids(&self) -> Vec<FineBlockId> {
        return self.id_to_block.keys().cloned().collect();
    }
    pub fn get_block_size(&self, id: FineBlockId) -> usize {
        assert!(self.id_to_block.contains_key(&id));
        return self.id_to_block.get(&id).unwrap().size();
    }
    pub fn cut_from_set(&mut self, b: &FineBlockId, set: &Vec<State>) {
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
    /* block: states q for rules like f() -> q. 
     * loop through rules where dest in block.
     * For each rule, generate context and loop
     * through the input states, switching current
     * idx with special symbol []. ObsMap is a map
     * from state -> context -> count where state
     * is instances where it was substituted in the
     * context special symbol position for a rule.
     *
     * TLDR:
     * block has states q
     * for each rule f(s1,s2,...) -> q:
     *     iterate si, context_si where context_si
     *     is f(s0,...,[si],...):
     *         obsmap[si][context_si]++;
     */
    pub fn generate_obs(&mut self, block: &FineBlock) -> ObservationMap {
        //iterates rules and counts obs
        let mut result: ObservationMap = ObservationMap::new();
        for output_q in block.elements_iter() {
            let rule_ptrs: Vec<_> = self.transition_table_ptr.borrow().rule_iter_by_output(*output_q).cloned().collect();
            for rule_ptr in rule_ptrs {
                let mut current_context: Context = Context::new(
                    rule_ptr.borrow().symbol,
                    rule_ptr.borrow().input.clone(),
                    0);

                let element_iter: Vec<(usize, State)> = current_context.elements_iter().cloned().enumerate().collect();
                for (index, state) in element_iter {
                    current_context.move_empty_index(index);
                    let current_id: ContextId = self.get_context_id(&current_context);
                    if !result.contains_key(&state) {
                        result.insert(state, HashMap::new());
                    }
                    *result.get_mut(&state).unwrap().entry(current_id).or_insert(0) += 1;
                }
            }
        }
        return result;
    }
    /* b_map is observations of fine block. For
     * each state, generate context set containing
     * contexts for which coarse_obs == fine_obs
     * counts.
     */
    pub fn generate_context_setfn(&mut self, s_id: CoarseBlockId, b_map: &ObservationMap) -> HashMap<State, ContextSet> {
        //all contexts where equal
        let mut result: HashMap<State, ContextSet> = HashMap::new();
        let s_map: &ObservationMap = self.obs_q.get(&s_id).unwrap();
        for (state, context_map) in b_map.iter() {
            for (context, count) in context_map.iter() {
                if s_map.get(state).unwrap().get(context).unwrap() != count {
                    continue;
                }
                if !result.contains_key(state) {
                    result.insert(*state, ContextSet::new_empty());
                }
                result.get_mut(state).unwrap().insert(*context);
            }
        }
        return result;
    }
    /* Before coarse block S gets cut, update
     * the obsmap counts using the obsmap for
     * fine block that will be cut from S.
     * Ex: If S has fine block B and B will be
     * cut, then compute obsmap for B and run
     * this function with (S, obsmap_B) as args.
     */
    pub fn subtract_obsmap_from_coarse_block(&mut self, block_to_subtract_from_id: CoarseBlockId, b_obsmap: &ObservationMap) {
        let block_to_subtract_from: &mut ObservationMap = self.obs_q.get_mut(&block_to_subtract_from_id).unwrap();
        for (state, context_cnt) in b_obsmap.iter() { 
            let to_subtract_from_cnts: &mut HashMap<ContextId, u32> = block_to_subtract_from.get_mut(state).unwrap();
            for (context, cnt) in context_cnt.iter() {
                /* remove key if will be 0, obsmap can
                 * only have positive keys.
                 */
                if to_subtract_from_cnts[context] == *cnt {
                    to_subtract_from_cnts.remove(context);
                    continue;
                }
                *to_subtract_from_cnts.get_mut(context).unwrap() -= cnt;
            }
        }
    }
    pub fn set_coarse_block_obsmap(&mut self, coarse_id: CoarseBlockId, b_obsmap: ObservationMap) {
        self.obs_q.insert(coarse_id, b_obsmap);
    }
    pub fn splitf(&mut self, b: FineBlock) -> ObservationMap {
        let b_obsmap: ObservationMap = self.generate_obs(&b);

        //repartition with b obs
        let mut next_partition: HashMap<FineBlockId, HashMap<ContextSet, Vec<State>>> = HashMap::new();
        for (state, context_map) in b_obsmap.iter() {
            let fine_id: FineBlockId = self.get_block_id_from_state(*state);
            let context_set: ContextSet = ContextSet::new(context_map.keys().cloned().collect());

            if !next_partition.contains_key(&fine_id) {
                next_partition.insert(fine_id, HashMap::new());
            }
            next_partition.get_mut(&fine_id).unwrap().entry(context_set).or_insert(Vec::new()).push(*state);
        }

        //cut
        for (fine_id, context_partition) in next_partition.iter() {
            for (_, partition) in context_partition.iter() {
                self.cut_from_set(fine_id, partition);
            }
        }

        return b_obsmap;
    }
    pub fn splitfn(&mut self, s: CoarseBlockId, b_obsmap: &ObservationMap) {
        let context_map: HashMap<State, ContextSet> = self.generate_context_setfn(s, &b_obsmap);

        //repartition with b counts
        let mut next_partition: HashMap<FineBlockId, HashMap<ContextSet, Vec<State>>> = HashMap::new();
        for (state, context_set) in context_map.iter() {
            let fine_id: FineBlockId = self.get_block_id_from_state(*state);
            let current_map: &mut HashMap<ContextSet, Vec<State>> = next_partition.entry(fine_id).or_insert(HashMap::new());
            if !current_map.contains_key(context_set) {
                current_map.insert(context_set.clone(), Vec::new());
            }

            current_map.get_mut(context_set).unwrap().push(*state);
        }

        //cut
        for (fine_id, context_partition) in next_partition.iter() {
            for (_, partition) in context_partition.iter() {
                self.cut_from_set(fine_id, partition);
            }
        }
    }
}

type CoarseBlockId = u32;

#[derive(Debug)]
pub struct CoarseBlock {
    id: CoarseBlockId,
    elements: HashSet<FineBlockId>,
}

impl CoarseBlock {
    pub fn remove(&mut self, fine_id: FineBlockId) {
        assert!(self.elements.contains(&fine_id));
        self.elements.remove(&fine_id);
    }
    pub fn insert(&mut self, fine_id: FineBlockId) {
        assert!(!self.elements.contains(&fine_id));
        self.elements.insert(fine_id);
    }
    pub fn contains(&self, fine_id: FineBlockId) -> bool {
        return self.elements.contains(&fine_id);
    }
    pub fn size(&self) -> usize {
        return self.elements.len();
    }
}

#[derive(Derivative)]
#[derivative(Debug)]
pub struct CoarsePartition {
    id_to_block: HashMap<CoarseBlockId, CoarseBlock>,
    fine_id_to_id: HashMap<FineBlockId, CoarseBlockId>,
    compound_blocks: HashSet<CoarseBlockId>,
    #[derivative(Debug="ignore")]
    fine_partition: Option<FinePartitionPtr>,
    free_ids: VecDeque<CoarseBlockId>,
}

impl CoarsePartition {
    pub fn new() -> Self {
        return CoarsePartition {
            id_to_block: HashMap::new(),
            fine_id_to_id: HashMap::new(),
            compound_blocks: HashSet::new(),
            fine_partition: None,
            free_ids: VecDeque::new()
        };
    }
    /* Adds coarse block with one element */
    pub fn add_block(&mut self, fine_id: FineBlockId) -> CoarseBlockId {
        assert!(!self.fine_id_to_id.contains_key(&fine_id));
        let new_id: CoarseBlockId = self.get_free_id();
        let new_block: CoarseBlock = CoarseBlock {
            id: new_id,
            elements: HashSet::from([fine_id])
        };
        self.fine_id_to_id.insert(fine_id, new_id);
        self.id_to_block.insert(new_id, new_block);
        return new_id;
    }
    /* Get unused coarse block id */
    pub fn get_free_id(&mut self) -> CoarseBlockId {
        if self.free_ids.is_empty() {
            return self.id_to_block.len() as CoarseBlockId;
        }
        return self.free_ids.pop_front().unwrap();
    }
    pub fn remove_empty_block(&mut self, id: CoarseBlockId) {
        assert!(self.id_to_block.contains_key(&id));
        assert_eq!(self.id_to_block.get(&id).unwrap().size(), 0);
        self.id_to_block.remove(&id);
        self.free_ids.push_back(id);
    }
    /* Remove fine id from its current block.
     * If coarse block is empty after removing,
     * the coarse block is removed as well.
     */
    pub fn remove_fine_id(&mut self, fine_id: FineBlockId) {
        assert!(self.fine_id_to_id.contains_key(&fine_id));
        let id: CoarseBlockId = self.fine_id_to_id.get(&fine_id).unwrap().clone();

        let block: &mut CoarseBlock = self.id_to_block.get_mut(&id).unwrap();
        block.remove(fine_id);
        match block.size() {
            0 => {self.remove_empty_block(id);},
            1 => {self.compound_blocks.remove(&id);},
            _ => {}
        }
        self.fine_id_to_id.remove(&fine_id);
    }
    /* Insert fine id into coarse block with coarse_id */
    pub fn insert_fine_id(&mut self, coarse_id: CoarseBlockId, fine_id: FineBlockId) {
        assert!(!self.get_block(coarse_id).contains(fine_id));
        let block: &mut CoarseBlock = self.get_block_mut(coarse_id);
        block.insert(fine_id);
        if block.size() == 2 {
            self.compound_blocks.insert(coarse_id);
        }
    }
    pub fn set_fine_partition(&mut self, fine_partition: FinePartitionPtr) {
        self.fine_partition = Some(fine_partition);
    } 
    pub fn num_compound_blocks(&self) -> usize {
        return self.compound_blocks.len();
    }
    pub fn choose_compound_block(&self) -> CoarseBlockId {
        assert!(self.num_compound_blocks() != 0);
        return self.compound_blocks.iter().cloned().next().unwrap();
    }
    pub fn choose_smaller_half(&self, b: CoarseBlockId) -> FineBlockId {
        assert!(self.compound_blocks.contains(&b));
        assert!(self.fine_partition.is_some());
        let b_block: &CoarseBlock = self.get_block(b);

        let mut iter = b_block.elements.iter();
        let first_fine_id: FineBlockId = iter.next().unwrap().clone();
        let second_fine_id: FineBlockId = iter.next().unwrap().clone();

        let fine_partition = self.fine_partition.as_ref().unwrap().borrow();

        if fine_partition.get_block_size(first_fine_id) < fine_partition.get_block_size(second_fine_id) {
            return first_fine_id;
        }
        return second_fine_id;
    }
    pub fn get_block(&self, id: CoarseBlockId) -> &CoarseBlock {
        assert!(self.id_to_block.contains_key(&id));
        return self.id_to_block.get(&id).unwrap();
    }
    pub fn get_block_mut(&mut self, id: CoarseBlockId) -> &mut CoarseBlock {
        assert!(self.id_to_block.contains_key(&id));
        return self.id_to_block.get_mut(&id).unwrap();
    }
    pub fn get_block_id_containing(&self, id: FineBlockId) -> CoarseBlockId {
        assert!(self.fine_id_to_id.contains_key(&id));
        return self.fine_id_to_id.get(&id).unwrap().clone();
    }
    pub fn cut(&mut self, b: FineBlockId) -> CoarseBlockId {
        self.remove_fine_id(b);
        return self.add_block(b);
    }
    pub fn alert_fine_block_split(&mut self, original: FineBlockId, new: FineBlockId) {
        assert!(!self.fine_id_to_id.contains_key(&new));
        let id: CoarseBlockId = self.get_block_id_containing(original);

        self.insert_fine_id(id, new);
        self.fine_id_to_id.insert(new, id);
    }
}

#[derive(Debug)]
pub struct Dtfa {
    states: HashSet<State>,
    accepting_states: HashSet<State>,
    transition_table: TransitionTablePtr
}

impl Dtfa {
    pub fn new(states: HashSet<State>, accepting_states: HashSet<State>, rules: Vec<SymbolicRule>) -> Self {
        assert!(!states.contains(&EMPTY));
        assert!(!accepting_states.contains(&EMPTY));
        return Dtfa {
            states,
            accepting_states,
            transition_table: Rc::new(RefCell::new(TransitionTable::new(rules)))
        };
    }
    pub fn minimize(&self) -> Vec<Vec<State>> {
        let p: CoarsePartitionPtr = Rc::new(RefCell::new(CoarsePartition::new()));
        let r: FinePartitionPtr = Rc::new(RefCell::new(FinePartition::new(
            p.clone(), self.transition_table.clone(), &self.states, &self.accepting_states
        )));

        //link p to r
        p.borrow_mut().set_fine_partition(r.clone());

        while p.borrow_mut().num_compound_blocks() != 0 {
            let s: CoarseBlockId = p.borrow().choose_compound_block();
            let b: FineBlockId = p.borrow().choose_smaller_half(s);
            let b_save: FineBlock = r.borrow().get_block(b).clone();

            /* splitf(b) returns obsmap of b such that
             * obsf_q(f,c,b) are counted in the obsmap.
             * b contains the dest states for rules in
             * the obsf def.
             */
            let b_obsmap: ObservationMap = r.borrow_mut().splitf(b_save);
            r.borrow_mut().splitfn(s, &b_obsmap);

            /* Since b will be removed from its coarse
             * block, subtract the context counts using
             * the computed b_obsmap.
             */
            r.borrow_mut().subtract_obsmap_from_coarse_block(s, &b_obsmap);

            // Cut b into a new coarse block
            let new_coarse_id: CoarseBlockId = p.borrow_mut().cut(b);

            // new_coarse_id block does not have obsmap.
            // Set the obsmap for the new block.
            r.borrow_mut().set_coarse_block_obsmap(new_coarse_id, b_obsmap);
        }

        return r.borrow().get_equiv_classes();
    }
}

#[derive(Derivative)]
#[derivative(Debug)]
pub struct DtfaMapper<StateType, SymbolType>
where
    StateType: Eq + Hash + Clone,
    SymbolType: Eq + Hash + Clone,
{
    to_state: HashMap<StateType, State>,
    to_statetype: HashMap<State, StateType>,
    accepting_states: HashSet<StateType>,
    next_free_state: State,

    #[derivative(Debug="ignore")]
    to_symbol: HashMap<SymbolType, Symbol>,
    #[derivative(Debug="ignore")]
    to_symboltype: HashMap<Symbol, SymbolType>,
    #[derivative(Debug="ignore")]
    next_free_symbol: Symbol,
    
    #[derivative(Debug="ignore")]
    rules: Vec<SymbolicRule>
}

impl<StateType, SymbolType> DtfaMapper<StateType, SymbolType>
where
    StateType: Eq + Hash + Clone,
    SymbolType: Eq + Hash + Clone,
{
    pub fn new<StateCollection, SymbolCollection>(
        states: StateCollection,
        accepting: StateCollection,
        symbols: SymbolCollection
    ) -> Self 
    where
        StateCollection: IntoIterator<Item = StateType>,
        SymbolCollection: IntoIterator<Item = SymbolType>,
    {
        let mut result: Self = Self::default();

        for state in states {
            result.add_state(state);
        }
        for accept_state in accepting {
            result.add_accepting_state(accept_state);
        }
        for symbol in symbols {
            result.add_symbol(symbol);
        }

        return result;
    }
    pub fn default() -> Self {
        return Self {
            to_state: HashMap::new(),
            to_statetype: HashMap::new(),
            accepting_states: HashSet::new(),
            next_free_state: 1,

            to_symbol: HashMap::new(),
            to_symboltype: HashMap::new(),
            next_free_symbol: 0,

            rules: Vec::new()
        };
    }
    pub fn add_state(&mut self, state: StateType) {
        if self.to_state.contains_key(&state) {
            return;
        }
        self.to_state.insert(state.clone(), self.next_free_state);
        self.to_statetype.insert(self.next_free_state, state);
        self.next_free_state += 1;
    }
    pub fn add_accepting_state(&mut self, state: StateType) {
        self.add_state(state.clone());
        self.accepting_states.insert(state);
    }
    pub fn add_symbol(&mut self, symbol: SymbolType) {
        if self.to_symbol.contains_key(&symbol) {
            return;
        }
        self.to_symbol.insert(symbol.clone(), self.next_free_symbol);
        self.to_symboltype.insert(self.next_free_symbol, symbol);
        self.next_free_symbol += 1;
    }
    pub fn add_rule(&mut self, symbol: SymbolType, input: Vec<StateType>, output: StateType) {
        assert!(self.to_symbol.contains_key(&symbol));
        assert!(input.iter().all(|state| self.to_state.contains_key(state)));
        assert!(self.to_state.contains_key(&output));

        self.rules.push(SymbolicRule::new(
            self.to_symbol[&symbol],
            input.iter().map(|state| self.to_state[state]).collect(),
            self.to_state[&output]
        ));
    }
    pub fn get_states(&self) -> HashSet<State> {
        let result: HashSet<State> = self.to_state.values().cloned().collect();
        return result;
    }
    pub fn get_symbols(&self) -> HashSet<Symbol> {
        let result: HashSet<Symbol> = self.to_symbol.values().cloned().collect();
        return result;
    }
    pub fn get_accepting_states(&self) -> HashSet<State> {
        let result: HashSet<State> = self.accepting_states.iter().map(|state| self.to_state[state]).collect();
        return result;
    }
    pub fn get_rules(&self) -> Vec<SymbolicRule> {
        return self.rules.clone();
    }
    pub fn get_equiv(&self, state_vec: Vec<Vec<State>>) -> Vec<Vec<StateType>> {
        assert!(state_vec.iter().flatten().all(|state| self.to_statetype.contains_key(state)));
        let result: Vec<Vec<StateType>> = state_vec.iter().map(|inner_vec|
            inner_vec.iter().map(|&state|
                self.to_statetype[&state].clone()
            ).collect()
        ).collect();
        return result;
    }
}

#[cfg(test)]
mod tests {
// quicksave: cargo test --lib dtfa::tests::<testname> -- --nocapture

    use super::*;

    pub fn get_dtfa() -> Dtfa {
        let symbol_id: HashMap<char, Symbol> = HashMap::from([
            ('a', 0),
            ('b', 1),
            ('f', 2)
        ]);

        let automaton: Dtfa = Dtfa::new(
            vec![1,2,3,4].into_iter().collect(),
            vec![3,4].into_iter().collect(),
            vec![
                SymbolicRule::new(symbol_id[&'a'], vec![1], 1),
                SymbolicRule::new(symbol_id[&'a'], vec![2], 2),
                SymbolicRule::new(symbol_id[&'b'], vec![], 2),
                SymbolicRule::new(symbol_id[&'f'], vec![1,2], 3),
                SymbolicRule::new(symbol_id[&'f'], vec![1,1], 4),
                SymbolicRule::new(symbol_id[&'f'], vec![2,2], 4),
                SymbolicRule::new(symbol_id[&'f'], vec![2,1], 4),
            ]
        );
        return automaton;
    }

    pub fn get_partition_pair(automaton: &Dtfa) -> (CoarsePartitionPtr, FinePartitionPtr) {
        let p: CoarsePartitionPtr = Rc::new(RefCell::new(CoarsePartition::new()));
        let r: FinePartitionPtr = Rc::new(RefCell::new(FinePartition::new(
            p.clone(), automaton.transition_table.clone(), &automaton.states, &automaton.accepting_states
        )));

        //link p to r
        p.borrow_mut().set_fine_partition(r.clone());
        return (p, r);
    }

    #[test]
    pub fn dtfa() {
        let automaton: Dtfa = get_dtfa();
        let equiv_classes = automaton.minimize();
        println!("{:?}", equiv_classes);
    }

    #[test]
    pub fn test_add_block() {
        let (coarse_partition, _) = get_partition_pair(&get_dtfa());
        println!("{:#?}", coarse_partition);
        coarse_partition.borrow_mut().add_block(3);
        println!("{:#?}", coarse_partition);
    }

    #[test]
    pub fn test_remove_fine_id() {
        let (coarse_partition, _) = get_partition_pair(&get_dtfa());
        println!("{:#?}", coarse_partition);
        for i in 0..2 {
            coarse_partition.borrow_mut().remove_fine_id(i);
            println!("removed {}: {:#?}", i, coarse_partition);
        }
    }

    #[test]
    pub fn test_context_hash() {
        let (_, fine_partition) = get_partition_pair(&get_dtfa());
        println!("{:#?}", fine_partition.borrow().context_to_id);
    }
    
    #[test]
    pub fn test_cut_from_set() {
        let (_, fine_partition) = get_partition_pair(&get_dtfa());
        println!("original: {:#?}", fine_partition);
        fine_partition.borrow_mut().cut_from_set(&0, &vec![3,4]);
        println!("cut: {:#?}", fine_partition);
    }

    #[test]
    pub fn test_gen_obs() {
        let (_, fine_partition) = get_partition_pair(&get_dtfa());
        let block = fine_partition.borrow().get_block(0).clone();
        println!("{:#?}", fine_partition.borrow().context_to_id);
        let obs = fine_partition.borrow_mut().generate_obs(&block);
        println!("{:#?}", obs);
    }

    #[test]
    pub fn test_init_obs_q() {
        let (_, fine_partition) = get_partition_pair(&get_dtfa());
        println!("original: contextid: {:#?}, {:#?}",
            fine_partition.borrow().context_to_id,
            fine_partition.borrow().obs_q);
    }
}
