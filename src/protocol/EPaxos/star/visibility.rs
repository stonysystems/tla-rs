//! Every pair of conflicting committed commands has a dependency edge.
use super::types::*;
use super::model::*;
use super::behavior::*;
use super::knowledge::*;
use super::validation_evidence::*;
use super::dependency_certificates::*;
use super::agreement::*;
use super::quorum::*;
use vstd::prelude::*;

verus! {

#[verifier::opaque]
pub open spec fn visibility(s: State, c: Constants) -> bool {
    forall |p: Packet, q: Packet| #![trigger s.network.contains(p), s.network.contains(q)]
        s.network.contains(p) && s.network.contains(q) && p.kind is Commit && q.kind is Commit
        && p.instance != q.instance && !(p.attrs.payload is Nop) && !(q.attrs.payload is Nop)
        && conflicts(c, p.attrs.payload, q.attrs.payload) ==> covers(p.instance, p.attrs, q.instance, q.attrs)
}

pub proof fn lemma_no_compatible_commit(s: State, p: Packet, other: Instance)
    requires agreement(s), s.network.contains(p), p.kind is Commit,
        !(p.attrs.payload is Nop), !p.attrs.deps.contains(other)
    ensures !compatible_commit(s, p.instance, other)
{
    reveal(agreement);
    if compatible_commit(s, p.instance, other) {
        let q = choose |q: Packet| #[trigger] s.network.contains(q) && q.kind is Commit
            && q.instance == p.instance && (q.attrs.payload is Nop || q.attrs.deps.contains(other));
        assert(p.attrs == q.attrs);
    }
}

pub proof fn lemma_initial_pair_visibility(s: State, c: Constants, id: Instance, attrs: Attributes,
    batch: Map<int, Packet>, other: Instance, other_attrs: Attributes, other_batch: Map<int, Packet>)
    requires valid_constants(c), knowledge(s, c), id != other, conflicts(c, attrs.payload, other_attrs.payload),
        initial_dependency_certificate(s, c, id, attrs, batch),
        initial_dependency_certificate(s, c, other, other_attrs, other_batch)
    ensures covers(id, attrs, other, other_attrs)
{
    reveal(knowledge);
    let node = lemma_majorities_intersect(c, batch.dom(), other_batch.dom());
    let p = batch[node];
    let q = other_batch[node];
    assert(s.network.contains(p));
    assert(s.network.contains(q));
    assert(covers(p.instance, p.attrs, q.instance, q.attrs));
}

pub proof fn lemma_mixed_pair_visibility(s: State, c: Constants, p: Packet, q: Packet,
    initial: Map<int, Packet>, node: int, b: int, validated: Map<int, Packet>)
    requires valid_constants(c), agreement(s), validation_evidence(s, c),
        s.network.contains(p), p.kind is Commit, p.instance != q.instance,
        !(p.attrs.payload is Nop), conflicts(c, p.attrs.payload, q.attrs.payload),
        initial_dependency_certificate(s, c, p.instance, p.attrs, initial),
        validated_dependency_certificate(s, c, q.instance, q.attrs, node, b, validated)
    ensures covers(p.instance, p.attrs, q.instance, q.attrs)
{
    reveal(validation_evidence);
    if !covers(p.instance, p.attrs, q.instance, q.attrs) {
        lemma_no_compatible_commit(s, p, q.instance);
        let intersection = lemma_majorities_intersect(c, initial.dom(), validated.dom());
        let initial_reply = initial[intersection];
        let validated_reply = validated[intersection];
        assert(s.network.contains(initial_reply));
        assert(s.network.contains(validated_reply));
        assert(!covers(q.instance, q.attrs, p.instance, initial_reply.attrs));
        assert(invalidates_id(validated_reply, p.instance) || compatible_commit(s, p.instance, q.instance));
        let i = choose |i: Invalidation| #[trigger] validated_reply.invalidating.contains(i) && i.instance == p.instance;
        assert(compatible_commit(s, i.instance, q.instance));
    }
}

pub proof fn lemma_validated_pair_visibility(s: State, c: Constants, p: Packet, q: Packet,
    node: int, b: int, batch: Map<int, Packet>, other_node: int, other_b: int, other_batch: Map<int, Packet>)
    requires valid_constants(c), agreement(s), validation_evidence(s, c),
        s.network.contains(p), s.network.contains(q), p.kind is Commit, q.kind is Commit,
        p.instance != q.instance, !(p.attrs.payload is Nop), !(q.attrs.payload is Nop),
        conflicts(c, p.attrs.payload, q.attrs.payload),
        validated_dependency_certificate(s, c, p.instance, p.attrs, node, b, batch),
        validated_dependency_certificate(s, c, q.instance, q.attrs, other_node, other_b, other_batch)
    ensures covers(p.instance, p.attrs, q.instance, q.attrs)
{
    reveal(validation_evidence);
    if !covers(p.instance, p.attrs, q.instance, q.attrs) {
        lemma_no_compatible_commit(s, p, q.instance);
        lemma_no_compatible_commit(s, q, p.instance);
        let intersection = lemma_majorities_intersect(c, batch.dom(), other_batch.dom());
        let first = batch[intersection];
        let second = other_batch[intersection];
        assert(s.network.contains(first));
        assert(s.network.contains(second));
        assert(invalidates_id(first, q.instance) || invalidates_id(second, p.instance));
        if invalidates_id(first, q.instance) {
            let i = choose |i: Invalidation| #[trigger] first.invalidating.contains(i) && i.instance == q.instance;
            assert(compatible_commit(s, i.instance, p.instance));
        } else {
            let i = choose |i: Invalidation| #[trigger] second.invalidating.contains(i) && i.instance == p.instance;
            assert(compatible_commit(s, i.instance, q.instance));
        }
    }
}

pub proof fn lemma_committed_visibility(s: State, c: Constants, p: Packet, q: Packet)
    requires valid_constants(c), agreement(s), knowledge(s, c), validation_evidence(s, c), dependency_certificates(s, c),
        s.network.contains(p), s.network.contains(q), p.kind is Commit, q.kind is Commit,
        p.instance != q.instance, !(p.attrs.payload is Nop), !(q.attrs.payload is Nop),
        conflicts(c, p.attrs.payload, q.attrs.payload)
    ensures covers(p.instance, p.attrs, q.instance, q.attrs)
{
    reveal(dependency_certificates);
    assert(dependency_certificate(s, c, p.instance, p.attrs));
    assert(dependency_certificate(s, c, q.instance, q.attrs));
    reveal(dependency_certificate);
    if exists |batch: Map<int, Packet>| initial_dependency_certificate(s, c, p.instance, p.attrs, batch) {
        let batch = choose |batch: Map<int, Packet>| initial_dependency_certificate(s, c, p.instance, p.attrs, batch);
        if exists |other_batch: Map<int, Packet>| initial_dependency_certificate(s, c, q.instance, q.attrs, other_batch) {
            let other_batch = choose |other_batch: Map<int, Packet>| initial_dependency_certificate(s, c, q.instance, q.attrs, other_batch);
            lemma_initial_pair_visibility(s, c, p.instance, p.attrs, batch, q.instance, q.attrs, other_batch);
        } else {
            let (node, b, validated) = choose |node: int, b: int, validated: Map<int, Packet>|
                validated_dependency_certificate(s, c, q.instance, q.attrs, node, b, validated);
            lemma_mixed_pair_visibility(s, c, p, q, batch, node, b, validated);
        }
    } else {
        let (node, b, batch) = choose |node: int, b: int, batch: Map<int, Packet>|
            validated_dependency_certificate(s, c, p.instance, p.attrs, node, b, batch);
        if exists |initial: Map<int, Packet>| initial_dependency_certificate(s, c, q.instance, q.attrs, initial) {
            let initial = choose |initial: Map<int, Packet>| initial_dependency_certificate(s, c, q.instance, q.attrs, initial);
            lemma_mixed_pair_visibility(s, c, q, p, initial, node, b, batch);
        } else {
            let (other_node, other_b, other_batch) = choose |other_node: int, other_b: int, other_batch: Map<int, Packet>|
                validated_dependency_certificate(s, c, q.instance, q.attrs, other_node, other_b, other_batch);
            lemma_validated_pair_visibility(s, c, p, q, node, b, batch, other_node, other_b, other_batch);
        }
    }
}

pub proof fn lemma_behavior_visibility(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures visibility(states[i], c)
{
    reveal(behavior);
    lemma_behavior_agreement(states, c, i);
    lemma_behavior_knowledge(states, c, i);
    lemma_behavior_validation_evidence(states, c, i);
    lemma_behavior_dependency_certificates(states, c, i);
    reveal(visibility);
    assert forall |p: Packet, q: Packet| #![trigger covers(p.instance, p.attrs, q.instance, q.attrs)] states[i].network.contains(p) && states[i].network.contains(q)
        && p.kind is Commit && q.kind is Commit && p.instance != q.instance
        && !(p.attrs.payload is Nop) && !(q.attrs.payload is Nop) && conflicts(c, p.attrs.payload, q.attrs.payload)
        implies covers(p.instance, p.attrs, q.instance, q.attrs) by {
        lemma_committed_visibility(states[i], c, p, q);
    }
}

} // verus!
