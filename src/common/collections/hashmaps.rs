use std::collections::HashMap;
use std::hash::Hash;
use vstd::prelude::*;
use vstd::std_specs::hash::*;
verus! {
    // ══════════════════════════════════════════════════════════════════
    // Trusted primitives: HashMap lemmas (Phase 30)
    // ══════════════════════════════════════════════════════════════════
    //
    // These lemmas bridge exec-level HashMap operations to spec-level Map
    // properties. They provide the minimal trust boundary for HashMap
    // iteration patterns used in RSL acceptor, proposer, and replica.

    /// After iterating a HashMap and filtering entries by a predicate on keys,
    /// the resulting HashMap's view satisfies the spec-level filter.
    ///
    /// This is the core primitive for CRemoveVotesBeforeLogTruncationPoint
    /// and similar HashMap filtering operations.
    #[verifier::external_body]
    pub proof fn lemma_hashmap_filter_by_key<K: Hash + Eq, V>(
        m: &HashMap<K, V>,
        result: &HashMap<K, V>,
        pred: spec_fn(K) -> bool,
    )
    requires
        forall |k: K| result@.contains_key(k) <==> (m@.contains_key(k) && pred(k)),
        forall |k: K| result@.contains_key(k) ==> result@[k] == m@[k],
    ensures
        result@.dom().finite(),
        result@.len() <= m@.len(),
    {
    }

    /// After iterating all entries of a HashMap, every key in the domain
    /// has been visited.
    ///
    /// Soundness: HashMap::iter() yields every (key, value) pair exactly once.
    #[verifier::external_body]
    pub proof fn lemma_hashmap_iter_complete<K: Hash + Eq, V>(
        m: &HashMap<K, V>,
    )
    ensures
        m@.dom().finite(),
        m@.len() == m.len(),
    {
    }
}
