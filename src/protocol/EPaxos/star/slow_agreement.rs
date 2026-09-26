//! Preservation of a value accepted by a slow quorum, at every higher ballot.
use super::types::*;
use super::model::*;
use super::recovery::*;
use super::behavior::*;
use super::coordinator::*;
use super::evidence::*;
use super::recovery_certificates::*;
use super::quorum::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn slow_chosen(s: State, c: Constants, id: Instance,
    b: int, attrs: Attributes, votes: Map<int, Packet>, coordinator: int) -> bool {
    &&& b >= 0
    &&& majority(c, votes.dom())
    &&& replies(s, c, coordinator, id, b, Kind::AcceptOk, votes)
    &&& forall |q: int| #[trigger] votes.dom().contains(q) ==> votes[q].attrs == attrs
}

pub proof fn lemma_maximum_snapshot(batch: Map<int, Packet>, candidates: Set<int>) -> (q: int)
    requires candidates.subset_of(batch.dom()), candidates.len() > 0
    ensures candidates.contains(q),
        forall |other: int| #[trigger] candidates.contains(other)
            ==> batch[other].snapshot.accepted_ballot <= batch[q].snapshot.accepted_ballot
    decreases candidates.len()
{
    broadcast use group_set_properties;
    let head = candidates.choose();
    let rest = candidates.remove(head);
    if rest.len() == 0 {
        head
    } else {
        let tail = lemma_maximum_snapshot(batch, rest);
        if batch[head].snapshot.accepted_ballot >= batch[tail].snapshot.accepted_ballot {
            head
        } else {
            tail
        }
    }
}

pub proof fn lemma_slow_quorum_preserved(s: State, c: Constants, id: Instance, b: int,
    attrs: Attributes, votes: Map<int, Packet>, coordinator: int, p: Packet)
    requires
        valid_constants(c), same_ballot_agreement(s), evidence(s, c), recovery_certificates(s, c),
        slow_chosen(s, c, id, b, attrs, votes, coordinator),
        s.network.contains(p), proposal(p), p.instance == id, p.ballot >= b,
    ensures p.attrs == attrs
    decreases p.ballot - b
{
    broadcast use group_set_properties;
    reveal(evidence);
    reveal(same_ballot_agreement);
    if p.ballot == b {
        assert(votes.dom().len() > 0);
        let voter = votes.dom().choose();
        let vote = votes[voter];
        assert(s.network.contains(vote));
        assert(vote_evidence(s, vote));
        let original = choose |q: Packet| #[trigger] s.network.contains(q)
            && q.kind is Accept && q.instance == vote.instance && q.ballot == vote.ballot
            && q.attrs == vote.attrs && q.src == vote.dst;
        assert(original.attrs == p.attrs);
    } else {
        reveal(recovery_certificates);
        assert(recovery_certificate(s, c, p.src, id, p.ballot, p.attrs));
        reveal(recovery_certificate);
        let batch = choose |batch: Map<int, Packet>| {
            &&& #[trigger] replies(s, c, p.src, id, p.ballot, Kind::RecoverOk, batch)
            &&& majority(c, batch.dom())
            &&& stable_max(batch).len() > 0 ==> selected_from_max(batch, p.attrs)
        };
        let intersection = lemma_majorities_intersect(c, votes.dom(), batch.dom());
        let vote = votes[intersection];
        let response = batch[intersection];
        assert(s.network.contains(vote));
        assert(s.network.contains(response));
        assert(snapshot_covers_vote(response, vote));
        let max = lemma_maximum_snapshot(batch, batch.dom());
        assert(maximal(batch, max));
        assert(snapshot_evidence(s, batch[max]));
        if batch[max].snapshot.accepted_ballot == response.snapshot.accepted_ballot {
            assert(stable_max(batch).contains(intersection));
        } else {
            assert(batch[max].snapshot.accepted_ballot > 0);
            assert(stable_max(batch).contains(max));
        }
        assert(stable_max(batch).len() > 0);
        assert(selected_from_max(batch, p.attrs));
        let selected = choose |q: int| #[trigger] stable_max(batch).contains(q)
            && batch[q].snapshot.attrs == p.attrs;
        let snapshot = batch[selected];
        assert(snapshot_evidence(s, snapshot));
        assert(b <= snapshot.snapshot.accepted_ballot < p.ballot);
        assert(record_evidence(s, id, snapshot.snapshot));
        let earlier = choose |q: Packet| #[trigger] s.network.contains(q)
            && q.instance == id && q.ballot == snapshot.snapshot.accepted_ballot
            && q.attrs == snapshot.snapshot.attrs
            && if snapshot.snapshot.phase is Committed { q.kind is Commit } else { q.kind is Accept };
        lemma_slow_quorum_preserved(s, c, id, b, attrs, votes, coordinator, earlier);
    }
}

/// This theorem concerns any value accepted by a quorum. It includes higher
/// ballots reached through validation, Nop selection, and reboot. Fast-only
/// decisions require a separate preservation theorem.
pub proof fn lemma_behavior_slow_quorum_preserved(states: Seq<State>, c: Constants, i: int,
    id: Instance, b: int, attrs: Attributes, votes: Map<int, Packet>, coordinator: int, p: Packet)
    requires behavior(states, c), 0 <= i < states.len(),
        slow_chosen(states[i], c, id, b, attrs, votes, coordinator),
        states[i].network.contains(p), proposal(p), p.instance == id, p.ballot >= b
    ensures p.attrs == attrs
{
    reveal(behavior);
    lemma_behavior_coordinator(states, c, i);
    lemma_behavior_evidence(states, c, i);
    lemma_behavior_recovery_certificates(states, c, i);
    lemma_slow_quorum_preserved(states[i], c, id, b, attrs, votes, coordinator, p);
}

} // verus!
