use crate::common::collections::comparable::*;
use std::collections::*;
use std::hash::Hash;
use vstd::prelude::*;
use vstd::std_specs::hash::*;
use vstd::view::*;
verus! {
    /// Extension trait providing well_formed for HashSet
    /// For HashSet, well_formed is always true since it's a standard library type
    pub trait HashSetWellFormed {
        spec fn well_formed(&self) -> bool;
    }

    impl<T> HashSetWellFormed for HashSet<T> {
        #[verifier(inline)]
        open spec fn well_formed(&self) -> bool {
            true
        }
    }
    #[verifier(external_body)]
    pub fn union_sets<T>(s1:&HashSet<T>, s2:&HashSet<T>) -> (res:HashSet<T>)
    where
        T: Clone + Eq + Hash
    ensures
        res@ == s1@.union(s2@),
    {
        let mut result = HashSet::new();
        for elem in s1 {
            result.insert(elem.clone());
        }
        for elem in s2 {
            result.insert(elem.clone());
        }
        result
    }

    #[verifier(external_body)]
    pub fn clone_hashset<T>(s:&HashSet<T>) -> (res:HashSet<T>)
    where
            T: Clone + Eq + Hash
    ensures
        res@ == s@,
    {
        let mut res = HashSet::new();
        for elem in s {
            res.insert(elem.clone());
        }
        res
    }

    #[verifier(external_body)]
    pub fn hashset_to_vec<T>(s:&HashSet<T>) -> (res:Vec<T>)
    where
            T: Clone + Eq + Hash
    {
        s.iter().cloned().collect()
    }

    // ══════════════════════════════════════════════════════════════════
    // Trusted primitives: Set::map cardinality lemmas (Phase 30)
    // ══════════════════════════════════════════════════════════════════
    //
    // These lemmas bridge exec-level HashSet<T>.len() to spec-level
    // Set<U>.len() when the spec view uses Set::map(f) to change the
    // element type (e.g., Set<u64>.map(|x| x as int) → Set<int>).
    //
    // Sound because the view/cast functions used are always injective:
    // distinct concrete values map to distinct abstract values.

    /// Core lemma: Set::map with an injective function preserves cardinality.
    ///
    /// This is the fundamental primitive. All assume sites involving
    /// `HashSet.len() vs Set.map(f).len()` reduce to this lemma.
    ///
    /// Soundness: follows from the definition of Set::map and injectivity —
    /// injective f establishes a bijection between s and s.map(f), so they
    /// have equal cardinality.
    #[verifier::external_body]
    pub proof fn lemma_set_map_injective_len<T, U>(s: Set<T>, f: spec_fn(T) -> U)
    requires
        forall |x1: T, x2: T| #![trigger f(x1), f(x2)] f(x1) == f(x2) ==> x1 == x2,
    ensures
        s.map(f).len() == s.len(),
    {
    }

    /// Convenience: u64-to-int cast preserves set cardinality.
    ///
    /// Used in Raft (votes_granted: HashSet<u64>, spec uses Set<int>).
    pub proof fn lemma_set_u64_to_int_len(s: Set<u64>)
    ensures
        s.map(|x: u64| x as int).len() == s.len(),
    {
        let f = |x: u64| x as int;
        assert forall |x1: u64, x2: u64| #![trigger f(x1), f(x2)] f(x1) == f(x2) implies x1 == x2 by {};
        lemma_set_map_injective_len::<u64, int>(s, f);
    }

    /// Bridges exec HashSet<u64>.len() to spec Set<int>.len() after view mapping.
    ///
    /// Combines vstd's group_hash_axioms (HashSet.len() == s@.len()) with
    /// lemma_set_u64_to_int_len (s@.map(|x| x as int).len() == s@.len()) to
    /// prove: HashSet<u64>.len() as int == s@.map(|x: u64| x as int).len().
    ///
    /// This is the exact lemma needed at Raft assume sites (votes_granted).
    pub proof fn lemma_hashset_u64_len_eq_mapped(s: &HashSet<u64>)
    ensures
        s@.map(|x: u64| x as int).len() == s.len(),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        assert(s@.len() == s.len());
        lemma_set_u64_to_int_len(s@);
    }
}
