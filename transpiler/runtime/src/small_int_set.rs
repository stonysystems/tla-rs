//! Bitmap-backed set for small integers.
//!
//! `SmallIntSet` stores up to 64 integers in a `u64` bitmap with an `i128`
//! offset.  An integer `n` is in the set iff bit `(n - offset)` is set in
//! the bitmap.  Valid elements satisfy `0 <= n - offset < 64`.
//!
//! This is ~32× smaller than `BTreeSet<RuntimeValue>` for typical model-
//! checking workloads where sets contain server IDs or ballot numbers in a
//! small bounded range (e.g. Paxos's `Set<int>` over `{1..8}`).

use std::fmt;

/// A compact set of integers stored as a 64-bit bitmap.
///
/// Elements must lie in the range `[offset, offset + 63]`.
#[derive(Clone, Copy)]
pub struct SmallIntSet {
    /// Bitmap: bit `i` is set iff `(offset + i)` is in the set.
    bits: u64,
    /// The base value.  Element `n` maps to bit `n - offset`.
    offset: i128,
}

impl PartialEq for SmallIntSet {
    fn eq(&self, other: &Self) -> bool {
        if self.bits == 0 && other.bits == 0 {
            return true; // both empty, offset irrelevant
        }
        if self.offset == other.offset {
            return self.bits == other.bits;
        }
        // Different offsets: shift bits to compare
        let diff = other.offset - self.offset;
        if diff > 0 && diff < 64 {
            // self's bits shifted right by diff should match other's bits,
            // and self must have no bits below the shift
            self.bits >> diff as u32 == other.bits && self.bits & ((1u64 << diff as u32) - 1) == 0
        } else if diff < 0 && diff > -64 {
            let d = (-diff) as u32;
            other.bits >> d == self.bits && other.bits & ((1u64 << d) - 1) == 0
        } else {
            false // offsets too far apart to share elements
        }
    }
}

impl Eq for SmallIntSet {}

impl std::hash::Hash for SmallIntSet {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Normalize: hash based on actual elements
        for n in self.iter() {
            n.hash(state);
        }
    }
}

impl SmallIntSet {
    /// The maximum number of distinct elements (bits in a `u64`).
    pub const CAPACITY: u32 = 64;

    /// Create an empty set with the given offset.
    pub fn new(offset: i128) -> Self {
        Self { bits: 0, offset }
    }

    /// Create an empty set with offset 0.
    pub fn empty() -> Self {
        Self::new(0)
    }

    /// Try to build a `SmallIntSet` from an iterator of `i128` values.
    ///
    /// Returns `None` if the values span more than 64 apart (cannot fit in
    /// a single bitmap).  Returns `Some(empty set)` for an empty iterator.
    pub fn try_from_iter(iter: impl IntoIterator<Item = i128>) -> Option<Self> {
        let values: Vec<i128> = iter.into_iter().collect();
        if values.is_empty() {
            return Some(Self::empty());
        }
        let min = *values.iter().min().unwrap();
        let max = *values.iter().max().unwrap();
        if max - min >= Self::CAPACITY as i128 {
            return None;
        }
        let mut set = Self::new(min);
        for v in values {
            set.insert_unchecked(v);
        }
        Some(set)
    }

    /// Return the offset (minimum representable value).
    pub fn offset(&self) -> i128 {
        self.offset
    }

    /// Return the raw bitmap.
    pub fn bits(&self) -> u64 {
        self.bits
    }

    /// Number of elements in the set.
    pub fn len(&self) -> usize {
        self.bits.count_ones() as usize
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.bits == 0
    }

    /// Check whether `n` can be represented in this set (without inserting).
    pub fn can_represent(&self, n: i128) -> bool {
        let rel = n - self.offset;
        (0..Self::CAPACITY as i128).contains(&rel)
    }

    /// Check whether `n` is in the set.
    pub fn contains(&self, n: i128) -> bool {
        let rel = n - self.offset;
        if rel < 0 || rel >= Self::CAPACITY as i128 {
            return false;
        }
        self.bits & (1u64 << rel as u32) != 0
    }

    /// Insert `n` into the set.  Returns `true` if the element was new.
    ///
    /// Returns `Err(n)` if `n` is outside the representable range.
    pub fn insert(&mut self, n: i128) -> Result<bool, i128> {
        let rel = n - self.offset;
        if rel < 0 || rel >= Self::CAPACITY as i128 {
            return Err(n);
        }
        let mask = 1u64 << rel as u32;
        let was_absent = self.bits & mask == 0;
        self.bits |= mask;
        Ok(was_absent)
    }

    /// Insert without range check.  Panics in debug if out of range.
    fn insert_unchecked(&mut self, n: i128) {
        let rel = n - self.offset;
        debug_assert!(
            (0..Self::CAPACITY as i128).contains(&rel),
            "SmallIntSet::insert_unchecked: {n} out of range [{}..{})",
            self.offset,
            self.offset + Self::CAPACITY as i128,
        );
        self.bits |= 1u64 << rel as u32;
    }

    /// Remove `n` from the set.  Returns `true` if the element was present.
    pub fn remove(&mut self, n: i128) -> bool {
        let rel = n - self.offset;
        if rel < 0 || rel >= Self::CAPACITY as i128 {
            return false;
        }
        let mask = 1u64 << rel as u32;
        let was_present = self.bits & mask != 0;
        self.bits &= !mask;
        was_present
    }

    /// Set union (elements in either set).
    ///
    /// Both sets must have the same offset; panics otherwise.
    pub fn union(&self, other: &Self) -> Self {
        assert_eq!(
            self.offset, other.offset,
            "SmallIntSet::union: offset mismatch"
        );
        Self {
            bits: self.bits | other.bits,
            offset: self.offset,
        }
    }

    /// Set intersection (elements in both sets).
    pub fn intersection(&self, other: &Self) -> Self {
        if self.offset != other.offset {
            return Self::empty();
        }
        Self {
            bits: self.bits & other.bits,
            offset: self.offset,
        }
    }

    /// Set difference (elements in self but not other).
    pub fn difference(&self, other: &Self) -> Self {
        if self.offset != other.offset {
            return *self;
        }
        Self {
            bits: self.bits & !other.bits,
            offset: self.offset,
        }
    }

    /// Whether self is a subset of other.
    pub fn is_subset(&self, other: &Self) -> bool {
        if self.offset != other.offset {
            return self.is_empty();
        }
        self.bits & !other.bits == 0
    }

    /// Iterate over the elements in ascending order.
    pub fn iter(&self) -> SmallIntSetIter {
        SmallIntSetIter {
            remaining: self.bits,
            offset: self.offset,
        }
    }

    /// Collect elements into a sorted `Vec<i128>`.
    pub fn to_sorted_vec(&self) -> Vec<i128> {
        self.iter().collect()
    }
}

impl PartialOrd for SmallIntSet {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SmallIntSet {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare by sorted element sequences (matches BTreeSet ordering).
        self.len()
            .cmp(&other.len())
            .then_with(|| self.iter().cmp(other.iter()))
    }
}

impl fmt::Debug for SmallIntSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl fmt::Display for SmallIntSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for v in self.iter() {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{v}")?;
            first = false;
        }
        write!(f, "}}")
    }
}

/// Iterator over elements of a `SmallIntSet` in ascending order.
pub struct SmallIntSetIter {
    remaining: u64,
    offset: i128,
}

impl Iterator for SmallIntSetIter {
    type Item = i128;

    fn next(&mut self) -> Option<i128> {
        if self.remaining == 0 {
            return None;
        }
        let bit = self.remaining.trailing_zeros();
        self.remaining &= self.remaining - 1; // clear lowest set bit
        Some(self.offset + bit as i128)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.remaining.count_ones() as usize;
        (n, Some(n))
    }
}

impl ExactSizeIterator for SmallIntSetIter {}

impl IntoIterator for SmallIntSet {
    type Item = i128;
    type IntoIter = SmallIntSetIter;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl IntoIterator for &SmallIntSet {
    type Item = i128;
    type IntoIter = SmallIntSetIter;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let s = SmallIntSet::empty();
        assert_eq!(s.len(), 0);
        assert!(s.is_empty());
        assert!(!s.contains(0));
        assert_eq!(s.iter().count(), 0);
    }

    #[test]
    fn test_insert_contains_remove() {
        let mut s = SmallIntSet::new(0);
        assert_eq!(s.insert(5), Ok(true));
        assert_eq!(s.insert(5), Ok(false)); // duplicate
        assert!(s.contains(5));
        assert!(!s.contains(4));
        assert_eq!(s.len(), 1);

        assert!(s.remove(5));
        assert!(!s.contains(5));
        assert!(!s.remove(5)); // already removed
        assert_eq!(s.len(), 0);
    }

    #[test]
    fn test_insert_out_of_range() {
        let mut s = SmallIntSet::new(10);
        assert_eq!(s.insert(9), Err(9));
        assert_eq!(s.insert(74), Err(74)); // 10 + 64
        assert_eq!(s.insert(10), Ok(true));
        assert_eq!(s.insert(73), Ok(true)); // 10 + 63
    }

    #[test]
    fn test_negative_offset() {
        let mut s = SmallIntSet::new(-10);
        assert_eq!(s.insert(-10), Ok(true));
        assert_eq!(s.insert(-5), Ok(true));
        assert_eq!(s.insert(0), Ok(true));
        assert_eq!(s.insert(53), Ok(true)); // -10 + 63
        assert!(s.contains(-10));
        assert!(s.contains(0));
        assert!(!s.contains(-11));
        assert_eq!(s.len(), 4);
    }

    #[test]
    fn test_iter_ascending_order() {
        let mut s = SmallIntSet::new(0);
        s.insert(7).unwrap();
        s.insert(3).unwrap();
        s.insert(1).unwrap();
        s.insert(5).unwrap();
        let vals: Vec<i128> = s.iter().collect();
        assert_eq!(vals, vec![1, 3, 5, 7]);
    }

    #[test]
    fn test_iter_with_offset() {
        let mut s = SmallIntSet::new(100);
        s.insert(102).unwrap();
        s.insert(100).unwrap();
        s.insert(105).unwrap();
        let vals: Vec<i128> = s.iter().collect();
        assert_eq!(vals, vec![100, 102, 105]);
    }

    #[test]
    fn test_iter_exact_size() {
        let mut s = SmallIntSet::new(0);
        s.insert(1).unwrap();
        s.insert(3).unwrap();
        s.insert(5).unwrap();
        let iter = s.iter();
        assert_eq!(iter.len(), 3);
    }

    #[test]
    fn test_union() {
        let mut a = SmallIntSet::new(0);
        a.insert(1).unwrap();
        a.insert(3).unwrap();
        let mut b = SmallIntSet::new(0);
        b.insert(2).unwrap();
        b.insert(3).unwrap();
        let c = a.union(&b);
        assert_eq!(c.to_sorted_vec(), vec![1, 2, 3]);
    }

    #[test]
    fn test_intersection() {
        let mut a = SmallIntSet::new(0);
        a.insert(1).unwrap();
        a.insert(2).unwrap();
        a.insert(3).unwrap();
        let mut b = SmallIntSet::new(0);
        b.insert(2).unwrap();
        b.insert(3).unwrap();
        b.insert(4).unwrap();
        let c = a.intersection(&b);
        assert_eq!(c.to_sorted_vec(), vec![2, 3]);
    }

    #[test]
    fn test_intersection_different_offset() {
        let a = SmallIntSet::new(0);
        let b = SmallIntSet::new(100);
        let c = a.intersection(&b);
        assert!(c.is_empty());
    }

    #[test]
    fn test_difference() {
        let mut a = SmallIntSet::new(0);
        a.insert(1).unwrap();
        a.insert(2).unwrap();
        a.insert(3).unwrap();
        let mut b = SmallIntSet::new(0);
        b.insert(2).unwrap();
        b.insert(4).unwrap();
        let c = a.difference(&b);
        assert_eq!(c.to_sorted_vec(), vec![1, 3]);
    }

    #[test]
    fn test_difference_different_offset() {
        let mut a = SmallIntSet::new(0);
        a.insert(1).unwrap();
        let b = SmallIntSet::new(100);
        let c = a.difference(&b);
        assert_eq!(c.to_sorted_vec(), vec![1]);
    }

    #[test]
    fn test_is_subset() {
        let mut a = SmallIntSet::new(0);
        a.insert(1).unwrap();
        a.insert(2).unwrap();
        let mut b = SmallIntSet::new(0);
        b.insert(1).unwrap();
        b.insert(2).unwrap();
        b.insert(3).unwrap();
        assert!(a.is_subset(&b));
        assert!(!b.is_subset(&a));
        assert!(SmallIntSet::empty().is_subset(&a));
    }

    #[test]
    fn test_try_from_iter_empty() {
        let s = SmallIntSet::try_from_iter(Vec::<i128>::new()).unwrap();
        assert!(s.is_empty());
    }

    #[test]
    fn test_try_from_iter_success() {
        let s = SmallIntSet::try_from_iter(vec![3, 1, 4, 1, 5]).unwrap();
        assert_eq!(s.to_sorted_vec(), vec![1, 3, 4, 5]); // dedup + sorted
        assert_eq!(s.offset(), 1);
    }

    #[test]
    fn test_try_from_iter_too_wide() {
        let result = SmallIntSet::try_from_iter(vec![0, 100]);
        assert!(result.is_none()); // range > 64
    }

    #[test]
    fn test_try_from_iter_exact_64_range() {
        let result = SmallIntSet::try_from_iter(vec![0, 63]);
        assert!(result.is_some());
        let s = result.unwrap();
        assert!(s.contains(0));
        assert!(s.contains(63));
        assert!(!s.contains(32));
    }

    #[test]
    fn test_try_from_iter_just_over_64_range() {
        let result = SmallIntSet::try_from_iter(vec![0, 64]);
        assert!(result.is_none());
    }

    #[test]
    fn test_full_capacity() {
        let mut s = SmallIntSet::new(0);
        for i in 0..64 {
            s.insert(i).unwrap();
        }
        assert_eq!(s.len(), 64);
        for i in 0..64 {
            assert!(s.contains(i));
        }
        assert!(!s.contains(64));
    }

    #[test]
    fn test_ord() {
        let mut a = SmallIntSet::new(0);
        a.insert(1).unwrap();
        a.insert(2).unwrap();
        let mut b = SmallIntSet::new(0);
        b.insert(1).unwrap();
        b.insert(3).unwrap();
        // {1,2} < {1,3} because at the second element, 2 < 3
        assert!(a < b);
    }

    #[test]
    fn test_ord_different_sizes() {
        let mut a = SmallIntSet::new(0);
        a.insert(1).unwrap();
        let mut b = SmallIntSet::new(0);
        b.insert(1).unwrap();
        b.insert(2).unwrap();
        // len 1 < len 2
        assert!(a < b);
    }

    #[test]
    fn test_debug_display() {
        let mut s = SmallIntSet::new(0);
        s.insert(1).unwrap();
        s.insert(3).unwrap();
        assert_eq!(format!("{s}"), "{1, 3}");
        assert_eq!(format!("{s:?}"), "{1, 3}");
    }

    #[test]
    fn test_clone_independence() {
        let mut a = SmallIntSet::new(0);
        a.insert(1).unwrap();
        let mut b = a;
        b.insert(2).unwrap();
        assert!(!a.contains(2));
        assert!(b.contains(2));
    }

    #[test]
    fn test_eq_hash() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut a = SmallIntSet::new(0);
        a.insert(1).unwrap();
        a.insert(3).unwrap();
        let mut b = SmallIntSet::new(0);
        b.insert(3).unwrap();
        b.insert(1).unwrap(); // same elements, different insertion order
        assert_eq!(a, b);

        let hash = |s: &SmallIntSet| {
            let mut h = DefaultHasher::new();
            s.hash(&mut h);
            h.finish()
        };
        assert_eq!(hash(&a), hash(&b));
    }

    #[test]
    fn test_remove_nonexistent() {
        let mut s = SmallIntSet::new(0);
        assert!(!s.remove(0));
        assert!(!s.remove(100)); // out of range
    }

    #[test]
    fn test_can_represent() {
        let s = SmallIntSet::new(10);
        assert!(s.can_represent(10));
        assert!(s.can_represent(73)); // 10 + 63
        assert!(!s.can_represent(9));
        assert!(!s.can_represent(74));
    }

    #[test]
    fn test_into_iter() {
        let mut s = SmallIntSet::new(0);
        s.insert(2).unwrap();
        s.insert(4).unwrap();
        let vals: Vec<i128> = s.into_iter().collect();
        assert_eq!(vals, vec![2, 4]);
    }

    #[test]
    fn test_ref_into_iter() {
        let mut s = SmallIntSet::new(0);
        s.insert(2).unwrap();
        s.insert(4).unwrap();
        let vals: Vec<i128> = (&s).into_iter().collect();
        assert_eq!(vals, vec![2, 4]);
        // s is still usable
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn test_eq_same_offset() {
        let mut a = SmallIntSet::new(0);
        a.insert(1).unwrap();
        a.insert(3).unwrap();
        let mut b = SmallIntSet::new(0);
        b.insert(1).unwrap();
        b.insert(3).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn test_eq_different_offset_same_elements() {
        // {4} with offset=3 (e.g. from {3,4}.remove(3))
        let mut a = SmallIntSet::new(3);
        a.insert(4).unwrap();
        // {4} with offset=4
        let mut b = SmallIntSet::new(4);
        b.insert(4).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn test_eq_both_empty_different_offset() {
        let a = SmallIntSet::new(0);
        let b = SmallIntSet::new(100);
        assert_eq!(a, b);
    }

    #[test]
    fn test_ne_different_elements() {
        let mut a = SmallIntSet::new(0);
        a.insert(1).unwrap();
        let mut b = SmallIntSet::new(0);
        b.insert(2).unwrap();
        assert_ne!(a, b);
    }

    #[test]
    fn test_eq_offset_shift_multiple_elements() {
        // {10, 12} with offset=10
        let mut a = SmallIntSet::new(10);
        a.insert(10).unwrap();
        a.insert(12).unwrap();
        // {10, 12} with offset=8
        let mut b = SmallIntSet::new(8);
        b.insert(10).unwrap();
        b.insert(12).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn test_hash_consistent_with_eq() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut a = SmallIntSet::new(3);
        a.insert(4).unwrap();
        let mut b = SmallIntSet::new(4);
        b.insert(4).unwrap();
        assert_eq!(a, b);

        let hash_a = {
            let mut h = DefaultHasher::new();
            a.hash(&mut h);
            h.finish()
        };
        let hash_b = {
            let mut h = DefaultHasher::new();
            b.hash(&mut h);
            h.finish()
        };
        assert_eq!(hash_a, hash_b, "equal sets must have equal hashes");
    }
}
