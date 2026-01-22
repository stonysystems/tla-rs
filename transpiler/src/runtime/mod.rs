//! Runtime support traits for generated code.
//!
//! This module provides base traits that generated exec types should implement
//! to integrate with the Verus verification framework.
//!
//! # Design Philosophy
//!
//! The transpiler generates two kinds of types:
//! - **Spec types** (L-prefixed): Used in specifications, ghost code, proofs
//! - **Exec types** (C-prefixed): Used in executable code, verified to match spec
//!
//! The traits in this module define the interface between spec and exec types,
//! enabling the verification of exec code against spec predicates.

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// Trait for types that have a specification-level view.
///
/// This corresponds to Verus's `View` trait. Every exec type implements
/// this to provide a ghost view of its state for verification purposes.
///
/// # Example
///
/// ```ignore
/// impl View for CAcceptor {
///     type V = LAcceptor;
///
///     fn view(&self) -> LAcceptor {
///         LAcceptor {
///             max_bal: self.max_bal.view(),
///             votes: self.votes.view(),
///         }
///     }
/// }
/// ```
pub trait View {
    /// The spec-level type that this exec type views as
    type V;

    /// Get the specification-level view of this value
    fn view(&self) -> Self::V;
}

/// Trait for spec types with validity predicates.
///
/// Every spec type has a `well_formed` predicate that defines
/// what states are valid. This is used in ensures clauses to
/// guarantee that generated exec code produces valid states.
pub trait SpecType: Sized {
    /// Check if this value is well-formed (valid)
    fn well_formed(&self) -> bool;
}

/// Trait for executable types that correspond to spec types.
///
/// Exec types must:
/// - Implement `Clone` for functional-style updates
/// - Have a corresponding spec type via `View`
/// - Be able to validate their own well-formedness
pub trait ExecType: Clone + View {
    /// Check if this exec value is well-formed
    fn well_formed(&self) -> bool;
}

/// Trait for types that support deep cloning.
///
/// Unlike `Clone`, `DeepClone` ensures that all nested structures
/// are fully copied, with no shared references. This is important
/// for functional-style updates where the original must be preserved.
pub trait DeepClone: Sized {
    /// Create a deep copy of this value
    fn deep_clone(&self) -> Self;
}

// ============================================================================
// Standard Library View Implementations
// ============================================================================

impl<T: Clone> View for Vec<T>
where
    T: View,
{
    type V = Vec<T::V>;

    fn view(&self) -> Vec<T::V> {
        self.iter().map(|x| x.view()).collect()
    }
}

impl<K, V> View for HashMap<K, V>
where
    K: Clone + Eq + Hash + View,
    V: Clone + View,
    K::V: Eq + Hash,
{
    type V = HashMap<K::V, V::V>;

    fn view(&self) -> HashMap<K::V, V::V> {
        self.iter().map(|(k, v)| (k.view(), v.view())).collect()
    }
}

impl<T> View for HashSet<T>
where
    T: Clone + Eq + Hash + View,
    T::V: Eq + Hash,
{
    type V = HashSet<T::V>;

    fn view(&self) -> HashSet<T::V> {
        self.iter().map(|x| x.view()).collect()
    }
}

impl<T: Clone> View for Option<T>
where
    T: View,
{
    type V = Option<T::V>;

    fn view(&self) -> Option<T::V> {
        self.as_ref().map(|x| x.view())
    }
}

// Primitive type views (identity)
macro_rules! impl_view_identity {
    ($($ty:ty),*) => {
        $(
            impl View for $ty {
                type V = $ty;
                fn view(&self) -> $ty { *self }
            }
        )*
    };
}

impl_view_identity!(bool, i8, i16, i32, i64, i128, u8, u16, u32, u64, u128, usize, isize);

impl View for String {
    type V = String;
    fn view(&self) -> String {
        self.clone()
    }
}

// ============================================================================
// DeepClone implementations
// ============================================================================

impl<T: DeepClone> DeepClone for Vec<T> {
    fn deep_clone(&self) -> Self {
        self.iter().map(|x| x.deep_clone()).collect()
    }
}

impl<K, V> DeepClone for HashMap<K, V>
where
    K: Clone + Eq + Hash,
    V: DeepClone,
{
    fn deep_clone(&self) -> Self {
        self.iter()
            .map(|(k, v)| (k.clone(), v.deep_clone()))
            .collect()
    }
}

impl<T> DeepClone for HashSet<T>
where
    T: DeepClone + Eq + Hash,
{
    fn deep_clone(&self) -> Self {
        self.iter().map(|x| x.deep_clone()).collect()
    }
}

impl<T: DeepClone> DeepClone for Option<T> {
    fn deep_clone(&self) -> Self {
        self.as_ref().map(|x| x.deep_clone())
    }
}

// Primitive DeepClone (same as Clone)
macro_rules! impl_deep_clone_copy {
    ($($ty:ty),*) => {
        $(
            impl DeepClone for $ty {
                fn deep_clone(&self) -> $ty { *self }
            }
        )*
    };
}

impl_deep_clone_copy!(bool, i8, i16, i32, i64, i128, u8, u16, u32, u64, u128, usize, isize);

impl DeepClone for String {
    fn deep_clone(&self) -> String {
        self.clone()
    }
}

// ============================================================================
// Helper Types
// ============================================================================

/// A wrapper for exec types that tracks whether they are well-formed.
///
/// This can be used to add runtime well-formedness checking to
/// generated code during development/debugging.
#[derive(Debug, Clone)]
pub struct Validated<T> {
    value: T,
    is_valid: bool,
}

impl<T: ExecType> Validated<T> {
    /// Create a new validated wrapper, checking well-formedness
    pub fn new(value: T) -> Self {
        let is_valid = value.well_formed();
        Self { value, is_valid }
    }

    /// Get the inner value, panicking if invalid
    pub fn unwrap(self) -> T {
        assert!(self.is_valid, "Validated::unwrap called on invalid value");
        self.value
    }

    /// Get the inner value, returning None if invalid
    pub fn ok(self) -> Option<T> {
        if self.is_valid {
            Some(self.value)
        } else {
            None
        }
    }

    /// Check if the wrapped value is valid
    pub fn is_valid(&self) -> bool {
        self.is_valid
    }

    /// Get a reference to the inner value
    pub fn get(&self) -> &T {
        &self.value
    }
}

impl<T: ExecType> View for Validated<T> {
    type V = T::V;

    fn view(&self) -> T::V {
        self.value.view()
    }
}

/// Result type for exec functions that might fail validation
pub type ValidatedResult<T, E = String> = Result<Validated<T>, E>;

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_view_primitive() {
        let x: i32 = 42;
        assert_eq!(x.view(), 42);

        let b: bool = true;
        assert!(b.view());
    }

    #[test]
    fn test_view_vec() {
        let v: Vec<i32> = vec![1, 2, 3];
        assert_eq!(v.view(), vec![1, 2, 3]);
    }

    #[test]
    fn test_view_hashmap() {
        let mut m: HashMap<i32, i32> = HashMap::new();
        m.insert(1, 10);
        m.insert(2, 20);
        let view = m.view();
        assert_eq!(view.get(&1), Some(&10));
        assert_eq!(view.get(&2), Some(&20));
    }

    #[test]
    fn test_view_option() {
        let some: Option<i32> = Some(42);
        assert_eq!(some.view(), Some(42));

        let none: Option<i32> = None;
        assert_eq!(none.view(), None);
    }

    #[test]
    fn test_deep_clone_primitive() {
        let x: i32 = 42;
        assert_eq!(x.deep_clone(), 42);
    }

    #[test]
    fn test_deep_clone_vec() {
        let v: Vec<i32> = vec![1, 2, 3];
        let cloned = v.deep_clone();
        assert_eq!(cloned, vec![1, 2, 3]);
    }

    #[test]
    fn test_deep_clone_hashmap() {
        let mut m: HashMap<i32, String> = HashMap::new();
        m.insert(1, "one".to_string());
        m.insert(2, "two".to_string());
        let cloned = m.deep_clone();
        assert_eq!(cloned.get(&1), Some(&"one".to_string()));
    }

    // Test Validated wrapper
    #[derive(Debug, Clone)]
    struct TestExec {
        value: i32,
    }

    impl View for TestExec {
        type V = i32;
        fn view(&self) -> i32 {
            self.value
        }
    }

    impl ExecType for TestExec {
        fn well_formed(&self) -> bool {
            self.value >= 0 // Only non-negative values are valid
        }
    }

    #[test]
    fn test_validated_valid() {
        let v = Validated::new(TestExec { value: 42 });
        assert!(v.is_valid());
        assert_eq!(v.unwrap().value, 42);
    }

    #[test]
    fn test_validated_invalid() {
        let v = Validated::new(TestExec { value: -1 });
        assert!(!v.is_valid());
        assert!(v.ok().is_none());
    }

    #[test]
    fn test_validated_view() {
        let v = Validated::new(TestExec { value: 42 });
        assert_eq!(v.view(), 42);
    }
}
