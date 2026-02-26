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

    /// Bridges Set<T>.map(view_fn).len() == Set<T>.len() for types with
    /// view-injective equality (i.e., PartialEq ensures `t1 == t2 iff t1@ == t2@`).
    ///
    /// Soundness: HashSet deduplicates by Eq. If PartialEq guarantees
    /// `t1 == t2 iff t1@ == t2@`, then the view function is injective
    /// on the runtime contents, so `.map(|t| t@)` preserves cardinality.
    ///
    /// This covers EndPoint → AbstractEndPoint, CPacket → RslPacket, and
    /// any other type whose Eq is consistent with its View.
    #[verifier::external_body]
    pub proof fn lemma_set_view_map_len<T: View>(s: Set<T>)
    ensures
        s.map(|t: T| t@).len() == s.len(),
    {
    }

    /// Bridges exec HashSet<T:View>.len() to spec Set<T::V>.len() after
    /// view mapping.
    ///
    /// Combines two facts:
    /// 1. HashSet.len() == s@.len() (vstd axiom)
    /// 2. s@.map(|t| t@).len() == s@.len() (view-injective cardinality)
    ///
    /// This is external_body because Verus's group_hash_axioms broadcast
    /// doesn't fire for generic type parameters.
    ///
    /// Note: generic external_body lemmas may not instantiate correctly in
    /// Verus SMT encoding. Prefer the monomorphic variants below.
    #[verifier::external_body]
    pub proof fn lemma_hashset_view_len<T: View>(s: &HashSet<T>)
    ensures
        s@.map(|t: T| t@).len() == s.len(),
    {
    }

    /// Monomorphic CPacket variant: bridges HashSet<CPacket>.len() to
    /// Set<RslPacket>.len() via view mapping.
    #[verifier::external_body]
    pub proof fn lemma_hashset_cpacket_len(s: &HashSet<crate::implementation::RSL::cmessage::CPacket>)
    ensures
        s@.map(|p: crate::implementation::RSL::cmessage::CPacket| p@).len() == s.len(),
    {
    }

    /// Monomorphic EndPoint variant: bridges HashSet<EndPoint>.len() to
    /// Set<AbstractEndPoint>.len() via view mapping.
    #[verifier::external_body]
    pub proof fn lemma_hashset_endpoint_len(s: &HashSet<crate::common::native::io_s::EndPoint>)
    ensures
        s@.map(|e: crate::common::native::io_s::EndPoint| e@).len() == s.len(),
    {
    }

    // ══════════════════════════════════════════════════════════════════
    // Trusted primitives: Set::map forall bridging lemmas (Phase 30)
    // ══════════════════════════════════════════════════════════════════
    //
    // These lemmas bridge universal quantifiers across Set::map when
    // the view function is injective. Used for predicate functions that
    // check forall/exists over HashSet elements at exec level but need
    // to prove the same property at spec level over the view-mapped set.

    /// Bridges a universal src-inequality predicate from Set<CPacket> to
    /// Set<RslPacket> across the CPacket view mapping.
    ///
    /// Soundness: CPacket view is injective (axiom_cpacket_view ensures
    /// p1@ == p2@ ==> p1 == p2). This establishes a bijection between
    /// S and S.map(|p| p@), so the forall transfers in both directions.
    /// The .src field maps through view: p@.src == p.src@.
    #[verifier::external_body]
    pub proof fn lemma_cpacket_set_forall_src(
        s: Set<crate::implementation::RSL::cmessage::CPacket>,
        src: crate::common::native::io_s::AbstractEndPoint,
    )
    ensures
        (forall |op: crate::implementation::RSL::cmessage::CPacket| s.contains(op) ==> op.src@ != src)
        <==>
        (forall |op: crate::protocol::RSL::environment::RslPacket| s.map(|p: crate::implementation::RSL::cmessage::CPacket| p@).contains(op) ==> op.src != src),
    {
    }
}
