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
    ensures
        forall |i: int| 0 <= i < res@.len() ==> s@.contains(#[trigger] res@[i]),
        forall |x: T| s@.contains(x) ==> (exists |i: int| 0 <= i < res@.len() && res@[i] == x),
    {
        s.iter().cloned().collect()
    }

    /// Convert HashMap keys to a Vec, analogous to hashset_to_vec.
    /// Ensures: every element in the result is a key of the map,
    /// and every key of the map appears in the result.
    #[verifier(external_body)]
    pub fn hashmap_keys_to_vec<K, V>(m: &HashMap<K, V>) -> (res: Vec<K>)
    where
            K: Clone + Eq + Hash
    ensures
        forall |i: int| 0 <= i < res@.len() ==> m@.contains_key(#[trigger] res@[i]),
        forall |k: K| m@.contains_key(k) ==> (exists |i: int| 0 <= i < res@.len() && res@[i] == k),
    {
        m.keys().cloned().collect()
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
    pub proof fn lemma_set_map_injective_len<T, U>(s: Set<T>, f: spec_fn(T) -> U)
    requires
        forall |x1: T, x2: T| #![trigger f(x1), f(x2)] f(x1) == f(x2) ==> x1 == x2,
    ensures
        s.map(f).len() == s.len(),
    decreases s.len(),
    {
        broadcast use vstd::set::group_set_lemmas;
        if s.len() == 0 {
            assert(s =~= Set::<T>::empty());
            assert(s.map(f) =~= Set::<U>::empty());
        } else {
            let a = s.choose();
            let s_prime = s.remove(a);
            // Induction hypothesis (s_prime is finite and smaller)
            lemma_set_map_injective_len(s_prime, f);

            // s == s_prime.insert(a)
            assert(s =~= s_prime.insert(a));

            // s.map(f) =~= s_prime.map(f).insert(f(a))
            s_prime.lemma_set_map_insert_commute(a, f);
            assert(s.map(f) =~= s_prime.map(f).insert(f(a)));

            // f(a) not in s_prime.map(f) by injectivity
            assert(!s_prime.map(f).contains(f(a))) by {
                if s_prime.map(f).contains(f(a)) {
                    let b = choose |b: T| s_prime.contains(b) && f(b) == f(a);
                    assert(s_prime.contains(b) && f(b) == f(a));
                    assert(b == a);  // injectivity
                    assert(false);   // contradicts a not in s_prime
                }
            };

            // Set::map preserves finiteness.
        }
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

    /// Monomorphic CPacket variant: bridges HashSet<CPacket>.len() to
    /// Set<RslPacket>.len() via view mapping.
    pub proof fn lemma_hashset_cpacket_len(s: &HashSet<crate::implementation::RSL::cmessage::CPacket>)
    ensures
        s@.map(|p: crate::implementation::RSL::cmessage::CPacket| p@).len() == s.len(),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use crate::implementation::RSL::cmessage::axiom_cpacket_key_model;
        broadcast use crate::implementation::RSL::cmessage::axiom_cpacket_view;
        assert(s@.len() == s.len());
        let f = |p: crate::implementation::RSL::cmessage::CPacket| p@;
        assert forall |p1: crate::implementation::RSL::cmessage::CPacket, p2: crate::implementation::RSL::cmessage::CPacket|
            #![trigger f(p1), f(p2)] f(p1) == f(p2) implies p1 == p2 by {};
        lemma_set_map_injective_len(s@, f);
    }

    /// Monomorphic EndPoint variant: bridges HashSet<EndPoint>.len() to
    /// Set<AbstractEndPoint>.len() via view mapping.
    pub proof fn lemma_hashset_endpoint_len(s: &HashSet<crate::common::native::io_s::EndPoint>)
    ensures
        s@.map(|e: crate::common::native::io_s::EndPoint| e@).len() == s.len(),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
        broadcast use crate::common::native::io_s::axiom_endpoint_view;
        assert(s@.len() == s.len());
        let f = |e: crate::common::native::io_s::EndPoint| e@;
        assert forall |e1: crate::common::native::io_s::EndPoint, e2: crate::common::native::io_s::EndPoint|
            #![trigger f(e1), f(e2)] f(e1) == f(e2) implies e1 == e2 by {};
        lemma_set_map_injective_len(s@, f);
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
    /// CPacket view is open spec, so p@.src == p.src@ definitionally.
    /// Set::map is open spec, so membership transfers via existential witnesses.
    pub proof fn lemma_cpacket_set_forall_src(
        s: Set<crate::implementation::RSL::cmessage::CPacket>,
        src: crate::common::native::io_s::AbstractEndPoint,
    )
    ensures
        (forall |op: crate::implementation::RSL::cmessage::CPacket| #![trigger s.contains(op)]
            s.contains(op) ==> op.src@ != src)
        <==>
        // NOTE: no explicit trigger here. Verus auto-chooses
        // `s.map(<closure>).contains(op)`, and a trigger may not contain a
        // lambda ("triggers cannot contain let/forall/exists/lambda/choose"),
        // so the term it picks cannot be written by hand. Hoisting the closure
        // into a named spec fn would change this ensures clause, whose only
        // caller is generated code (src/generated/RSL/replica_gen.rs).
        // Tracked as a deliberate exception in reports/triggers/exceptions.md.
        (forall |op: crate::protocol::RSL::environment::RslPacket|
            s.map(|p: crate::implementation::RSL::cmessage::CPacket| p@).contains(op) ==> op.src != src),
    {
        let f = |p: crate::implementation::RSL::cmessage::CPacket| p@;

        // Forward: CPacket src-inequality → RslPacket src-inequality
        // For any RslPacket in s.map(f), its preimage CPacket in s has src@ != src,
        // and p@.src == p.src@ definitionally, so the RslPacket inherits the property.
        assert forall |rsl_op: crate::protocol::RSL::environment::RslPacket|
            #![trigger s.map(f).contains(rsl_op)]
            (forall |op: crate::implementation::RSL::cmessage::CPacket| #![trigger s.contains(op)]
                s.contains(op) ==> op.src@ != src) &&
            s.map(f).contains(rsl_op)
            implies rsl_op.src != src by {
            let q = choose |q: crate::implementation::RSL::cmessage::CPacket| s.contains(q) && f(q) == rsl_op;
            // q.src@ != src (from hypothesis, since s.contains(q))
            // rsl_op == q@ == LPacket { dst: q.dst@, src: q.src@, msg: q.msg@ }
            // so rsl_op.src == q.src@ != src
        };

        // Backward: RslPacket src-inequality → CPacket src-inequality
        // For any CPacket in s, its view op@ is in s.map(f), and
        // op@.src == op.src@ definitionally, so the CPacket inherits the property.
        assert forall |op: crate::implementation::RSL::cmessage::CPacket|
            #![trigger s.contains(op)]
            (forall |rsl_op: crate::protocol::RSL::environment::RslPacket| #![trigger s.map(f).contains(rsl_op)]
                s.map(f).contains(rsl_op) ==> rsl_op.src != src) &&
            s.contains(op)
            implies op.src@ != src by {
            // op ∈ s means f(op) = op@ ∈ s.map(f)
            assert(s.map(f).contains(f(op)));
            // op@.src != src (from hypothesis)
            // op@.src == op.src@ definitionally
        };
    }

    // ══════════════════════════════════════════════════════════════════
    // Trusted primitive: HashSet view is always finite (Phase 30)
    // ══════════════════════════════════════════════════════════════════
    //
    /// Verified clone for HashSet<u64>.
    ///
    /// Unlike the generic `clone_hashset<T>` (which is `external_body` because
    /// Verus cannot verify HashSet iteration), this monomorphic version uses
    /// `hashset_to_vec` + a while loop to build a proven-equal copy.
    pub fn clone_hashset_u64(s: &HashSet<u64>) -> (res: HashSet<u64>)
    ensures
        res@ == s@,
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let vec = hashset_to_vec(s);
        let mut cloned: HashSet<u64> = HashSet::new();
        let mut i: usize = 0;
        while i < vec.len()
            invariant
                0 <= i <= vec.len(),
                forall |j: int| 0 <= j < vec@.len() ==> s@.contains(#[trigger] vec@[j]),
                forall |x: u64| cloned@.contains(x) ==> s@.contains(x),
                forall |j: int| 0 <= j < i ==> cloned@.contains(#[trigger] vec@[j]),
            decreases vec.len() - i,
        {
            let val = vec[i];
            assert(s@.contains(vec@[i as int]));
            cloned.insert(val);
            i += 1;
        }
        proof {
            assert forall |x: u64| s@.contains(x) implies cloned@.contains(x) by {
                let j = choose |j: int| 0 <= j < vec@.len() && vec@[j] == x;
                assert(cloned@.contains(vec@[j]));
            };
            assert(cloned@ =~= s@);
        }
        cloned
    }
}
