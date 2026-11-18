//! Laws an element type must obey before a generic collection helper may
//! describe its result structurally.
//!
//! The trusted helpers in hashsets.rs and vecs.rs build their results with
//! `clone`, `==` and hashing. Their postconditions speak of structural
//! equality, which only holds when cloning returns an equal value and `==` is
//! structural equality (stonysystems/tla-rs#17). The helpers are bounded by the
//! traits below, so every element type proves (or, for the few derived impls
//! Verus cannot see, states) the laws once, instead of the helpers assuming
//! them for every type.
use std::hash::Hash;
use vstd::prelude::*;
use vstd::std_specs::hash::obeys_key_model;

verus! {

/// `T::clone` returns a value equal to the original (vstd's `obeys_clone_eq`
/// on newer vstd releases, stated here so older releases can use it too).
pub open spec fn clone_is_eq<T: Clone>() -> bool {
    forall |a: T, b: T| #[trigger] vstd::pervasive::cloned(a, b) ==> a == b
}

/// Cloning returns an equal value.
pub trait CloneIsEq: Clone + Sized {
    proof fn lemma_clone_is_eq()
        ensures clone_is_eq::<Self>();
}

/// `==` is structural equality and also view equality.
pub trait ViewEq: PartialEq + View + Sized {
    proof fn lemma_view_eq()
        ensures
            vstd::laws_eq::obeys_concrete_eq::<Self>(),
            vstd::laws_eq::obeys_view_eq::<Self>();
}

/// A hash-table element that obeys vstd's key model and clones to equal
/// values: enough to read a table's elements back out.
pub trait HashKeyModel: Clone + Eq + Hash + Sized {
    proof fn lemma_hash_key_model()
        ensures
            obeys_key_model::<Self>(),
            clone_is_eq::<Self>();
}

/// A `HashKeyModel` element whose `==` is structural equality, so inserting
/// it into a table behaves as set insertion: enough to build a table.
pub trait HashKey: HashKeyModel {
    proof fn lemma_hash_key()
        ensures vstd::laws_eq::obeys_concrete_eq::<Self>();
}

pub broadcast proof fn lemma_u64_clone_is_eq()
    ensures #[trigger] clone_is_eq::<u64>(),
{
}

impl CloneIsEq for u64 {
    proof fn lemma_clone_is_eq() {
    }
}

impl HashKeyModel for u64 {
    proof fn lemma_hash_key_model() {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
    }
}

impl HashKey for u64 {
    proof fn lemma_hash_key() {
        broadcast use vstd::laws_eq::group_laws_eq;
    }
}

} // verus!
