//! Meaning of validation replies. These are derived from local handlers,
//! including replies retained in the network after their sender reboots.
use super::types::*;
use super::model::*;
use super::recovery::*;
use super::behavior::*;
use super::invariants::*;
use super::identities::*;
use super::progress::*;
use super::coordinator::*;
use super::validity::*;
use super::knowledge::*;
use super::evidence::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn committed_without_edge(s: State, id: Instance, other: Instance) -> bool {
    exists |p: Packet| #[trigger] s.network.contains(p) && p.kind is Commit
        && p.instance == other && !(p.attrs.payload is Nop) && !p.attrs.deps.contains(id)
}

pub open spec fn compatible_commit(s: State, id: Instance, other: Instance) -> bool {
    exists |p: Packet| #[trigger] s.network.contains(p) && p.kind is Commit
        && p.instance == id && (p.attrs.payload is Nop || p.attrs.deps.contains(other))
}

pub open spec fn invalidates_id(p: Packet, id: Instance) -> bool {
    exists |i: Invalidation| #[trigger] p.invalidating.contains(i) && i.instance == id
}

pub open spec fn invalidation_sound(s: State, c: Constants, id: Instance, i: Invalidation) -> bool {
    &&& id != i.instance
    &&& !s.submitted[id].deps.contains(i.instance)
    &&& conflicts(c, s.submitted[id].payload, s.submitted[i.instance].payload)
    &&& i.committed ==> committed_without_edge(s, id, i.instance)
    &&& !i.committed ==> !s.submitted[i.instance].deps.contains(id)
}

#[verifier::opaque]
pub open spec fn validation_evidence(s: State, c: Constants) -> bool {
    &&& forall |p: Packet, i: Invalidation| #![trigger invalidation_sound(s, c, p.instance, i)] s.network.contains(p) && p.kind is ValidateOk
        && p.invalidating.contains(i) ==> invalidation_sound(s, c, p.instance, i)
    &&& forall |node: int, id: Instance, i: Invalidation| member(c, node)
        && s.nodes[node].attempts.dom().contains(id) && s.nodes[node].attempts[id].invalidating.contains(i)
        ==> invalidation_sound(s, c, id, i)
    &&& forall |node: int, id: Instance, i: Invalidation| member(c, node)
        && s.nodes[node].attempts.dom().contains(id) && s.nodes[node].attempts[id].stage is Waiting
        && #[trigger] s.nodes[node].attempts[id].invalidating.contains(i) ==> !i.committed
    &&& forall |p: Packet, q: Packet| #![trigger s.network.contains(p), s.network.contains(q)]
        s.network.contains(p) && s.network.contains(q) && p.src == q.src && p.instance != q.instance
        && p.kind is ValidateOk && q.kind is PreAcceptOk
        && conflicts(c, s.submitted[p.instance].payload, q.attrs.payload)
        && !covers(p.instance, s.submitted[p.instance], q.instance, q.attrs)
        ==> invalidates_id(p, q.instance) || compatible_commit(s, q.instance, p.instance)
    &&& forall |p: Packet, q: Packet| #![trigger s.network.contains(p), s.network.contains(q)]
        s.network.contains(p) && s.network.contains(q) && p.src == q.src && p.instance != q.instance
        && p.kind is ValidateOk && q.kind is ValidateOk
        && conflicts(c, s.submitted[p.instance].payload, s.submitted[q.instance].payload)
        && !covers(p.instance, s.submitted[p.instance], q.instance, s.submitted[q.instance])
        ==> invalidates_id(p, q.instance) || invalidates_id(q, p.instance)
            || compatible_commit(s, p.instance, q.instance) || compatible_commit(s, q.instance, p.instance)
}

pub proof fn lemma_initial_validation_evidence(s: State, c: Constants)
    requires init(s, c)
    ensures validation_evidence(s, c)
{
    reveal(validation_evidence);
}

pub proof fn lemma_local_invalidation_sound(s: State, c: Constants, node: int,
    id: Instance, attrs: Attributes)
    requires valid_constants(c), references_known(s, c), validity(s, c), evidence(s, c),
        member(c, node), s.submitted.dom().contains(id), attrs == s.submitted[id]
    ensures forall |i: Invalidation| #[trigger] invalidations(c, s.nodes[node], id, attrs).contains(i)
        ==> invalidation_sound(s, c, id, i)
{
    broadcast use group_set_lib_default;
    reveal(references_known);
    reveal(validity);
    reveal(evidence);
    assert forall |i: Invalidation| #[trigger] invalidations(c, s.nodes[node], id, attrs).contains(i)
        implies invalidation_sound(s, c, id, i) by {
        let other = i.instance;
        let r = record(s.nodes[node], other);
        assert(s.nodes[node].log.dom().contains(other));
        assert(invalidates(c, s.nodes[node], id, attrs, other));
        assert(record_valid(r, s.submitted[other]));
        assert(record_evidence(s, other, r));
        if i.committed {
            let p = choose |p: Packet| #[trigger] s.network.contains(p)
                && p.instance == other && p.ballot == r.accepted_ballot && p.attrs == r.attrs
                && if r.phase is Committed { p.kind is Commit } else { p.kind is Accept };
            assert(committed_without_edge(s, id, other));
        }
    }
}

pub proof fn lemma_validate_against_known(s: State, c: Constants, node: int,
    id: Instance, attrs: Attributes, q: Packet, other_attrs: Attributes)
    requires valid_constants(c), references_known(s, c), validity(s, c), evidence(s, c), knowledge(s, c),
        member(c, node), s.submitted.dom().contains(id), attrs == s.submitted[id],
        s.network.contains(q), q.src == node, q.instance != id,
        (q.kind is PreAcceptOk && other_attrs == q.attrs)
            || (q.kind is ValidateOk && other_attrs == s.submitted[q.instance]),
        conflicts(c, attrs.payload, other_attrs.payload), !covers(id, attrs, q.instance, other_attrs)
    ensures
        (exists |i: Invalidation| #[trigger] invalidations(c, s.nodes[node], id, attrs).contains(i)
            && i.instance == q.instance) || compatible_commit(s, q.instance, id)
{
    broadcast use group_set_lib_default;
    reveal(references_known);
    reveal(validity);
    reveal(evidence);
    reveal(knowledge);
    assert(recorded_knowledge(s, q));
    let other = q.instance;
    let r = record(s.nodes[node], other);
    assert(s.nodes[node].log.dom().contains(other));
    assert(record_valid(r, s.submitted[other]));
    if r.phase is Committed && (r.attrs.payload is Nop || r.attrs.deps.contains(id)) {
        assert(record_evidence(s, other, r));
        let p = choose |p: Packet| #[trigger] s.network.contains(p)
            && p.instance == other && p.ballot == r.accepted_ballot && p.attrs == r.attrs
            && if r.phase is Committed { p.kind is Commit } else { p.kind is Accept };
        assert(compatible_commit(s, other, id));
    } else {
        assert(invalidates(c, s.nodes[node], id, attrs, other));
        let bad = s.nodes[node].log.dom().filter(|other: Instance| invalidates(c, s.nodes[node], id, attrs, other));
        let f = |other: Instance| Invalidation { instance: other, committed: s.nodes[node].log[other].phase is Committed };
        let i = f(other);
        assert(bad.contains(other));
        bad.lemma_map_contains(f, i);
        assert(bad.map(f).contains(i));
        assert(invalidations(c, s.nodes[node], id, attrs).contains(i));
    }
}

pub proof fn lemma_step_validation_evidence(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        coordinator_invariant(s, c), same_ballot_agreement(s), validity(s, c), knowledge(s, c),
        evidence(s, c), validation_evidence(s, c), step(s, s_, c, a)
    ensures validation_evidence(s_, c)
{
    broadcast use group_set_lib_default;
    broadcast use group_set_properties;
    lemma_step_progress(s, s_, c, a);
    reveal(step);
    reveal(references_known);
    reveal(validity);
    reveal(knowledge);
    reveal(evidence);
    reveal(validation_evidence);
    assert forall |p: Packet, i: Invalidation| #![trigger invalidation_sound(s_, c, p.instance, i)] s_.network.contains(p) && p.kind is ValidateOk
        && p.invalidating.contains(i) implies invalidation_sound(s_, c, p.instance, i) by {
        if s.network.contains(p) {
            assert(invalidation_sound(s, c, p.instance, i));
        }
    }
    match a {
        Action::Validate { packet: p } => {
            lemma_local_invalidation_sound(s, c, p.dst, p.instance, p.attrs);
        },
        Action::FinishRecovery { node, id, ballot, batch, selected } => {
            if maximal_committed(batch).len() == 0 && maximal_accepted(batch).len() == 0
                && pending_support(batch).len() >= batch.dom().len() - c.e {
                assert(s.network.contains(batch[selected]));
                lemma_local_invalidation_sound(s, c, node, id, batch[selected].snapshot.attrs);
            }
        },
        _ => {},
    }
    assert forall |node: int, id: Instance, i: Invalidation| member(c, node)
        && s_.nodes[node].attempts.dom().contains(id) && s_.nodes[node].attempts[id].invalidating.contains(i)
        implies invalidation_sound(s_, c, id, i) by {
        if s.nodes[node].attempts.dom().contains(id) && s.nodes[node].attempts[id].invalidating.contains(i) {
            assert(invalidation_sound(s, c, id, i));
        }
    }
    assert forall |node: int, id: Instance, i: Invalidation| member(c, node)
        && s_.nodes[node].attempts.dom().contains(id) && s_.nodes[node].attempts[id].stage is Waiting
        && s_.nodes[node].attempts[id].invalidating.contains(i) implies !i.committed by {
        if let Action::FinishValidation { node: actor, id: target, ballot, batch } = a {
            if node == actor && id == target {
                let invalidating = batch.dom().map(|q: int| batch[q].invalidating).flatten();
                let committed = invalidating.filter(|entry: Invalidation| entry.committed);
                assert(committed.len() == 0);
                assert(!committed.contains(i));
            }
        }
    }
    assert forall |p: Packet, q: Packet| #![trigger invalidates_id(p, q.instance)] s_.network.contains(p) && s_.network.contains(q)
        && p.src == q.src && p.instance != q.instance && p.kind is ValidateOk && q.kind is PreAcceptOk
        && conflicts(c, s_.submitted[p.instance].payload, q.attrs.payload)
        && !covers(p.instance, s_.submitted[p.instance], q.instance, q.attrs)
        implies invalidates_id(p, q.instance) || compatible_commit(s_, q.instance, p.instance) by {
        if s.network.contains(p) { assert(recorded_knowledge(s, p)); }
        if s.network.contains(q) { assert(recorded_knowledge(s, q)); }
        if !s.network.contains(p) && s.network.contains(q) {
            assert(s.submitted.dom().contains(p.instance));
            assert(p.invalidating == invalidations(c, s.nodes[p.src], p.instance, s.submitted[p.instance]));
            lemma_validate_against_known(s, c, p.src, p.instance, s.submitted[p.instance], q, q.attrs);
        }
    }
    assert forall |p: Packet, q: Packet| #![trigger invalidates_id(p, q.instance)] #![trigger invalidates_id(q, p.instance)] s_.network.contains(p) && s_.network.contains(q)
        && p.src == q.src && p.instance != q.instance && p.kind is ValidateOk && q.kind is ValidateOk
        && conflicts(c, s_.submitted[p.instance].payload, s_.submitted[q.instance].payload)
        && !covers(p.instance, s_.submitted[p.instance], q.instance, s_.submitted[q.instance])
        implies invalidates_id(p, q.instance) || invalidates_id(q, p.instance)
            || compatible_commit(s_, p.instance, q.instance) || compatible_commit(s_, q.instance, p.instance) by {
        if s.network.contains(p) { assert(recorded_knowledge(s, p)); }
        if s.network.contains(q) { assert(recorded_knowledge(s, q)); }
        if !s.network.contains(p) && s.network.contains(q) {
            assert(s.submitted.dom().contains(p.instance));
            assert(p.invalidating == invalidations(c, s.nodes[p.src], p.instance, s.submitted[p.instance]));
            lemma_validate_against_known(s, c, p.src, p.instance, s.submitted[p.instance], q, s.submitted[q.instance]);
        }
        if s.network.contains(p) && !s.network.contains(q) {
            assert(s.submitted.dom().contains(q.instance));
            assert(q.invalidating == invalidations(c, s.nodes[q.src], q.instance, s.submitted[q.instance]));
            lemma_validate_against_known(s, c, q.src, q.instance, s.submitted[q.instance], p, s.submitted[p.instance]);
        }
    }
}

pub proof fn lemma_behavior_validation_evidence(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures validation_evidence(states[i], c)
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_validation_evidence(states[0], c);
    } else {
        lemma_behavior_validation_evidence(states, c, i - 1);
        lemma_behavior_bounds(states, c, i - 1);
        lemma_behavior_references(states, c, i - 1);
        lemma_behavior_coordinator(states, c, i - 1);
        lemma_behavior_validity(states, c, i - 1);
        lemma_behavior_knowledge(states, c, i - 1);
        lemma_behavior_evidence(states, c, i - 1);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_validation_evidence(states[i - 1], states[i], c, a);
    }
}

} // verus!
