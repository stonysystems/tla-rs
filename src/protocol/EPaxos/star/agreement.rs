//! Distributed agreement for committed instance attributes.
use super::types::*;
use super::behavior::*;
use super::coordinator::*;
use super::validity::*;
use super::knowledge::*;
use super::evidence::*;
use super::preaccept_evidence::*;
use super::support::*;
use super::proposal_origins::*;
use super::recovery_certificates::*;
use super::fast_agreement::*;
use super::slow_agreement::*;
use super::decisions::*;
use vstd::prelude::*;

verus! {

#[verifier::opaque]
pub open spec fn agreement_invariant(s: State, c: Constants) -> bool {
    &&& valid_constants(c)
    &&& coordinator_invariant(s, c)
    &&& same_ballot_agreement(s)
    &&& validity(s, c)
    &&& knowledge(s, c)
    &&& evidence(s, c)
    &&& preaccept_evidence(s, c)
    &&& support_invariant(s, c)
    &&& origins(s, c)
    &&& recovery_certificates(s, c)
    &&& decisions(s, c)
}

#[verifier::opaque]
pub open spec fn agreement(s: State) -> bool {
    forall |p: Packet, q: Packet| #![trigger s.network.contains(p), s.network.contains(q)]
        s.network.contains(p) && s.network.contains(q) && p.kind is Commit && q.kind is Commit
        && p.instance == q.instance ==> p.attrs == q.attrs
}

pub proof fn lemma_behavior_agreement_invariant(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures agreement_invariant(states[i], c)
{
    reveal(behavior);
    reveal(agreement_invariant);
    lemma_behavior_coordinator(states, c, i);
    lemma_behavior_validity(states, c, i);
    lemma_behavior_knowledge(states, c, i);
    lemma_behavior_evidence(states, c, i);
    lemma_behavior_preaccept_evidence(states, c, i);
    lemma_behavior_support(states, c, i);
    lemma_behavior_origins(states, c, i);
    lemma_behavior_recovery_certificates(states, c, i);
    lemma_behavior_decisions(states, c, i);
}

pub proof fn lemma_slow_chosen_agrees_with_commit(s: State, c: Constants, id: Instance, b: int,
    attrs: Attributes, votes: Map<int, Packet>, coordinator: int, q: Packet)
    requires agreement_invariant(s, c), slow_chosen(s, c, id, b, attrs, votes, coordinator),
        s.network.contains(q), q.kind is Commit, q.instance == id
    ensures q.attrs == attrs
    decreases q.ballot
{
    reveal(agreement_invariant);
    reveal(coordinator_invariant);
    reveal(decisions);
    assert(decision(s, c, id, q.ballot, q.attrs));
    if q.ballot >= b {
        lemma_slow_quorum_preserved(s, c, id, b, attrs, votes, coordinator, q);
    } else {
        reveal(decision);
        let accepted = lemma_slow_vote_has_proposal(s, c, id, b, attrs, votes, coordinator);
        if q.ballot == 0 && exists |fast: Map<int, Packet>| fast_certificate(s, c, id, q.attrs, fast) {
            let fast = choose |fast: Map<int, Packet>| fast_certificate(s, c, id, q.attrs, fast);
            lemma_fast_quorum_preserved(s, c, q, fast, accepted);
        } else if exists |other_votes: Map<int, Packet>, other_coordinator: int|
            slow_chosen(s, c, id, q.ballot, q.attrs, other_votes, other_coordinator) {
            let (other_votes, other_coordinator) = choose |other_votes: Map<int, Packet>, other_coordinator: int|
                slow_chosen(s, c, id, q.ballot, q.attrs, other_votes, other_coordinator);
            lemma_slow_quorum_preserved(s, c, id, q.ballot, q.attrs, other_votes, other_coordinator, accepted);
        } else {
            let earlier = choose |p: Packet| #[trigger] s.network.contains(p) && p.kind is Commit
                && p.instance == id && 0 <= p.ballot < q.ballot && p.attrs == q.attrs;
            lemma_slow_chosen_agrees_with_commit(s, c, id, b, attrs, votes, coordinator, earlier);
        }
    }
}

pub proof fn lemma_commits_agree(s: State, c: Constants, p: Packet, q: Packet)
    requires agreement_invariant(s, c), s.network.contains(p), s.network.contains(q),
        p.kind is Commit, q.kind is Commit, p.instance == q.instance
    ensures p.attrs == q.attrs
    decreases p.ballot
{
    reveal(agreement_invariant);
    reveal(coordinator_invariant);
    reveal(decisions);
    assert(decision(s, c, p.instance, p.ballot, p.attrs));
    reveal(decision);
    if p.ballot == 0 && exists |fast: Map<int, Packet>| fast_certificate(s, c, p.instance, p.attrs, fast) {
        let fast = choose |fast: Map<int, Packet>| fast_certificate(s, c, p.instance, p.attrs, fast);
        lemma_fast_quorum_preserved(s, c, p, fast, q);
    } else if exists |votes: Map<int, Packet>, coordinator: int|
        slow_chosen(s, c, p.instance, p.ballot, p.attrs, votes, coordinator) {
        let (votes, coordinator) = choose |votes: Map<int, Packet>, coordinator: int|
            slow_chosen(s, c, p.instance, p.ballot, p.attrs, votes, coordinator);
        lemma_slow_chosen_agrees_with_commit(s, c, p.instance, p.ballot, p.attrs, votes, coordinator, q);
    } else {
        let earlier = choose |earlier: Packet| #[trigger] s.network.contains(earlier) && earlier.kind is Commit
            && earlier.instance == p.instance && 0 <= earlier.ballot < p.ballot && earlier.attrs == p.attrs;
        lemma_commits_agree(s, c, earlier, q);
    }
}

/// All finite behaviors, all cluster sizes satisfying the baseline bounds,
/// arbitrary instances and ballots, including any number of reboot steps.
pub proof fn lemma_behavior_agreement(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures agreement(states[i])
{
    lemma_behavior_agreement_invariant(states, c, i);
    reveal(agreement);
    assert forall |p: Packet, q: Packet| #![trigger states[i].network.contains(p), states[i].network.contains(q)] states[i].network.contains(p) && states[i].network.contains(q)
        && p.kind is Commit && q.kind is Commit && p.instance == q.instance implies p.attrs == q.attrs by {
        lemma_commits_agree(states[i], c, p, q);
    }
}

} // verus!
