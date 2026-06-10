// Generated with Claude Sonnet 4.6

/// A low-level growable buffer, analogous to the C vec helpers.
/// Manages a raw heap allocation with explicit length and capacity.
pub struct RawVec {
    data: Vec<u8>,
    length: usize,
}

impl RawVec {
    pub fn new() -> Self {
        RawVec {
            data: Vec::new(),
            length: 0,
        }
    }

    /// Ensures there is room for at least one more element of `memsz` bytes.
    /// Doubles capacity when growth is needed (matches `vec_expand_`).
    pub fn expand(&mut self, memsz: usize) -> Result<(), ()> {
        let capacity = self.data.capacity() / memsz.max(1);
        if self.length + 1 > capacity {
            let new_cap = if capacity == 0 { 1 } else { capacity * 2 };
            self.data.reserve_exact(new_cap * memsz - self.data.capacity());
        }
        Ok(())
    }

    /// Reserves space for exactly `n` elements of `memsz` bytes
    /// (matches `vec_reserve_`).
    pub fn reserve(&mut self, memsz: usize, n: usize) -> Result<(), ()> {
        let capacity = self.data.capacity() / memsz.max(1);
        if n > capacity {
            let additional = n * memsz - self.data.capacity();
            self.data.reserve_exact(additional);
        }
        Ok(())
    }

    /// Reserves space rounded up to the next power of two
    /// (matches `vec_reserve_po2_`).
    pub fn reserve_po2(&mut self, memsz: usize, n: usize) -> Result<(), ()> {
        if n == 0 {
            return Ok(());
        }
        let n2 = n.next_power_of_two();
        self.reserve(memsz, n2)
    }

    /// Shrinks the allocation to exactly fit `length` elements
    /// (matches `vec_compact_`).
    pub fn compact(&mut self, memsz: usize) -> Result<(), ()> {
        if self.length == 0 {
            self.data = Vec::new(); // drops and frees the old allocation
        } else {
            let target = self.length * memsz;
            self.data.truncate(target);
            self.data.shrink_to_fit();
        }
        Ok(())
    }

    /// Shifts elements right to open a gap at `idx`, then expands if needed
    /// (matches `vec_insert_`).
    pub fn insert(&mut self, memsz: usize, idx: usize) -> Result<(), ()> {
        self.expand(memsz)?;
        let byte_idx = idx * memsz;
        let end = self.length * memsz;
        // Rotate the tail one element to the right
        self.data[byte_idx..end + memsz].rotate_right(memsz);
        Ok(())
    }

    /// Removes `count` elements starting at `start` by shifting the tail left
    /// (matches `vec_splice_`).
    pub fn splice(&mut self, memsz: usize, start: usize, count: usize) {
        let src = (start + count) * memsz;
        let dst = start * memsz;
        let tail_len = (self.length - start - count) * memsz;
        self.data.copy_within(src..src + tail_len, dst);
    }

    /// Removes `count` elements at `start` by overwriting them with the last
    /// `count` elements — O(count) swap-splice (matches `vec_swapsplice_`).
    pub fn swap_splice(&mut self, memsz: usize, start: usize, count: usize) {
        let src = (self.length - count) * memsz;
        let dst = start * memsz;
        self.data.copy_within(src..src + count * memsz, dst);
    }

    /// Swaps the elements at `idx1` and `idx2`
    /// (matches `vec_swap_`).
    pub fn swap_elements(&mut self, memsz: usize, idx1: usize, idx2: usize) {
        if idx1 == idx2 {
            return;
        }
        let a = idx1 * memsz;
        let b = idx2 * memsz;
        // split_at_mut lets us borrow two non-overlapping slices simultaneously
        let (lo, hi) = if a < b {
            let (left, right) = self.data.split_at_mut(b);
            (&mut left[a..a + memsz], &mut right[..memsz])
        } else {
            let (left, right) = self.data.split_at_mut(a);
            (&mut right[..memsz], &mut left[b..b + memsz])
        };
        lo.swap_with_slice(hi);
    }
}
