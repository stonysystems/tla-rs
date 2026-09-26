//! Preservation of a baseline fast-path decision through arbitrary recovery.
use super::types::*;
use super::model::*;
use super::recovery::*;
use super::behavior::*;
use super::coordinator::*;
use super::validity::*;
use super::knowledge::*;
use super::evidence::*;
use super::preaccept_evidence::*;
use super::recovery_certificates::*;
use super::proposal_origins::*;
use super::support::*;
use super::slow_agreement::*;
use super::quorum::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn fast_certificate(s: State, c: Constants, id: Instance,
    attrs: Attributes, batch: Map<int, Packet>) -> bool {
    &&& attrs == s.submitted[id]
    &&& attrs.payload is Command
    &&& replies(s, c, id.owner, id, 0, Kind::PreAcceptOk, batch)
    &&& fast_quorum(c, batch.dom())
    &&& forall |q: int| #[trigger] batch.dom().contains(q) ==> batch[q].attrs == attrs
}

pub proof fn lemma_no_stable_max_means_no_stable(s: State, c: Constants,
    node: int, id: Instance, b: int, batch: Map<int, Packet>)
    requires valid_constants(c), evidence(s, c), replies(s, c, node, id, b, Kind::RecoverOk, batch),
        majority(c, batch.dom()), stable_max(batch).len() == 0
    ensures forall |q: int| #[trigger] batch.dom().contains(q) ==> !stable(batch[q].snapshot)
{
    broadcast use group_set_properties;
    reveal(evidence);
    let max = lemma_maximum_snapshot(batch, batch.dom());
    assert(stable_max(batch) =~= Set::<int>::empty());
    assert(!stable_max(batch).contains(max));
    assert(maximal(batch, max));
    assert(snapshot_evidence(s, batch[max]));
    assert(!stable(batch[max].snapshot));
    assert(batch[max].snapshot.accepted_ballot == 0);
    assert forall |q: int| #[trigger] batch.dom().contains(q) implies !stable(batch[q].snapshot) by {
        assert(snapshot_evidence(s, batch[q]));
        assert(batch[q].snapshot.accepted_ballot == 0);
        assert(maximal(batch, q));
        assert(!stable_max(batch).contains(q));
    }
}

pub proof fn lemma_fast_prevents_abandon(s: State, c: Constants, id: Instance,
    attrs: Attributes, fast: Map<int, Packet>, node: int, b: int)
    requires valid_constants(c), validity(s, c), evidence(s, c), preaccept_evidence(s, c),
        fast_certificate(s, c, id, attrs, fast)
    ensures !abandoned_pending(s, c, node, id, b)
{
    broadcast use group_set_properties;
    reveal(abandoned_pending);
    reveal(preaccept_evidence);
    reveal(validity);
    if abandoned_pending(s, c, node, id, b) {
        let batch = choose |batch: Map<int, Packet>| {
            &&& #[trigger] replies(s, c, node, id, b, Kind::RecoverOk, batch)
            &&& majority(c, batch.dom())
            &&& stable_max(batch).len() == 0
            &&& pending_support(batch).len() < batch.dom().len() - c.e
        };
        lemma_no_stable_max_means_no_stable(s, c, node, id, b, batch);
        let overlap = fast.dom().intersect(batch.dom());
        assert forall |q: int| #[trigger] overlap.contains(q) implies pending_support(batch).contains(q) by {
            assert(s.network.contains(batch[q]));
            assert(s.network.contains(fast[q]));
            assert(batch[q].snapshot.phase is PreAccepted);
            assert(batch[q].snapshot.attrs == attrs);
            assert(batch[q].snapshot.original == attrs.payload);
            assert(batch[q].snapshot.initial_deps == attrs.deps);
        }
        assert(overlap.subset_of(pending_support(batch)));
        lemma_len_subset(overlap, pending_support(batch));
        lemma_fast_recovery_overlap(c, fast.dom(), batch.dom());
    }
}

pub proof fn lemma_fast_prevents_conflict_abort(s: State, c: Constants, id: Instance,
    attrs: Attributes, fast: Map<int, Packet>, p: Packet)
    requires valid_constants(c), knowledge(s, c), support_invariant(s, c),
        fast_certificate(s, c, id, attrs, fast)
    ensures !conflict_abort(s, c, id, p)
{
    reveal(support_invariant);
    if conflict_abort(s, c, id, p) {
        assert(supported(s, c, p.instance, p.attrs));
        lemma_fast_support_visibility(s, c, fast, id.owner, id, attrs, p.instance, p.attrs);
    }
}

pub proof fn lemma_fast_quorum_preserved(s: State, c: Constants, chosen: Packet,
    fast: Map<int, Packet>, p: Packet)
    requires
        valid_constants(c), same_ballot_agreement(s), validity(s, c), knowledge(s, c),
        evidence(s, c), preaccept_evidence(s, c), support_invariant(s, c), origins(s, c),
        s.network.contains(chosen), proposal(chosen), chosen.ballot == 0,
        fast_certificate(s, c, chosen.instance, chosen.attrs, fast),
        s.network.contains(p), proposal(p), p.instance == chosen.instance, p.ballot >= 0,
    ensures p.attrs == chosen.attrs
    decreases p.ballot
{
    reveal(same_ballot_agreement);
    if p.ballot == 0 {
        assert(p.attrs == chosen.attrs);
    } else {
        reveal(origins);
        assert(origin(s, c, p.src, p.instance, p.ballot, p.attrs));
        reveal(origin);
        if exists |earlier: Packet| #[trigger] s.network.contains(earlier) && proposal(earlier)
            && earlier.instance == p.instance && 0 <= earlier.ballot < p.ballot && earlier.attrs == p.attrs {
            let earlier = choose |earlier: Packet| #[trigger] s.network.contains(earlier) && proposal(earlier)
                && earlier.instance == p.instance && 0 <= earlier.ballot < p.ballot && earlier.attrs == p.attrs;
            lemma_fast_quorum_preserved(s, c, chosen, fast, earlier);
        } else {
            lemma_fast_prevents_abandon(s, c, chosen.instance, chosen.attrs, fast, p.src, p.ballot);
            assert forall |conflicting: Packet| !conflict_abort(s, c, chosen.instance, conflicting) by {
                lemma_fast_prevents_conflict_abort(s, c, chosen.instance, chosen.attrs, fast, conflicting);
            }
        }
    }
}

pub proof fn lemma_behavior_fast_quorum_preserved(states: Seq<State>, c: Constants, i: int,
    chosen: Packet, fast: Map<int, Packet>, p: Packet)
    requires behavior(states, c), 0 <= i < states.len(),
        states[i].network.contains(chosen), proposal(chosen), chosen.ballot == 0,
        fast_certificate(states[i], c, chosen.instance, chosen.attrs, fast),
        states[i].network.contains(p), proposal(p), p.instance == chosen.instance, p.ballot >= 0
    ensures p.attrs == chosen.attrs
{
    reveal(behavior);
    lemma_behavior_coordinator(states, c, i);
    lemma_behavior_validity(states, c, i);
    lemma_behavior_knowledge(states, c, i);
    lemma_behavior_evidence(states, c, i);
    lemma_behavior_preaccept_evidence(states, c, i);
    lemma_behavior_support(states, c, i);
    lemma_behavior_origins(states, c, i);
    lemma_fast_quorum_preserved(states[i], c, chosen, fast, p);
}

} // verus!
