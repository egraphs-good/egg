#[cfg(feature = "serde-1")]
use serde::{Deserialize, Serialize};
use std::fmt::{Debug, Formatter};
use std::mem;

#[derive(Debug, Default, Clone)]
#[cfg_attr(feature = "serde-1", derive(Serialize, Deserialize))]
pub struct DefaultVec<T>(Box<[T]>);

impl<T: Default> DefaultVec<T> {
    #[cold]
    #[inline(never)]
    fn reserve(&mut self, i: usize) {
        let mut v = mem::take(&mut self.0).into_vec();
        v.reserve(i + 1 - v.len());
        v.resize_with(v.capacity(), T::default);
        self.0 = v.into_boxed_slice();
        assert!(i < self.0.len())
    }

    pub fn get_mut(&mut self, i: usize) -> &mut T {
        if i < self.0.len() {
            &mut self.0[i]
        } else {
            self.reserve(i);
            &mut self.0[i]
        }
    }

    pub fn get(&self, i: usize) -> T
    where
        T: Copy,
    {
        self.0.get(i).copied().unwrap_or_default()
    }

    pub fn clear(&mut self) {
        self.0.fill_with(Default::default)
    }
}

type Elt = u32;

#[derive(Default, Clone)]
#[cfg_attr(feature = "serde-1", derive(Serialize, Deserialize))]
pub struct BitSet(DefaultVec<Elt>);

#[inline]
fn split(x: usize) -> (usize, Elt) {
    let offset = (x % Elt::BITS as usize) as u32;
    (x / Elt::BITS as usize, 1 << offset)
}

impl BitSet {
    pub fn insert(&mut self, x: usize) -> bool {
        let (chunk_idx, mask) = split(x);
        let chunk = self.0.get_mut(chunk_idx);
        let res = (*chunk & mask) != 0;
        *chunk |= mask;
        res
    }
    pub fn remove(&mut self, x: usize) -> bool {
        let (chunk_idx, mask) = split(x);
        let chunk = self.0.get_mut(chunk_idx);
        let res = (*chunk & mask) != 0;
        *chunk &= !mask;
        res
    }
    pub fn contains(&self, x: usize) -> bool {
        let (chunk_idx, mask) = split(x);
        let chunk = self.0.get(chunk_idx);
        (chunk & mask) != 0
    }

    /// Same as contains but already reserves space for `x`
    pub fn contains_mut(&mut self, x: usize) -> bool {
        let (chunk_idx, mask) = split(x);
        let chunk = *self.0.get_mut(chunk_idx);
        (chunk & mask) != 0
    }

    pub fn clear(&mut self) {
        self.0.clear()
    }

    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        let max = self.0 .0.len() * (Elt::BITS as usize);
        (0..max).filter(|x| self.contains(*x))
    }
}

impl Debug for BitSet {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}
