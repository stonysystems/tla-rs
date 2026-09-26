//! Every Commit is backed by a fast quorum, a slow quorum, or an older Commit.
use super::types::*;
use super::model::*;
use super::recovery::*;
use super::behavior::*;
use super::invariants::*;
use super::identities::*;
use super::progress::*;
use super::coordinator::*;
use super::validity::*;
use super::evidence::*;
use super::fast_agreement::*;
use super::slow_agreement::*;
use super::recovery_certificates::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

#[verifier::opaque]
pub open spec fn decision(s: State, c: Constants, id: Instance, b: int, attrs: Attributes) -> bool {
    ||| b == 0 && exists |batch: Map<int, Packet>| fast_certificate(s, c, id, attrs, batch)
    ||| exists |batch: Map<int, Packet>, coordinator: int| slow_chosen(s, c, id, b, attrs, batch, coordinator)
    ||| exists |p: Packet| #[trigger] s.network.contains(p) && p.kind is Commit
        && p.instance == id && 0 <= p.ballot < b && p.attrs == attrs
}

#[verifier::opaque]
pub open spec fn decisions(s: State, c: Constants) -> bool {
    forall |p: Packet| #[trigger] s.network.contains(p) && p.kind is Commit
        ==> decision(s, c, p.instance, p.ballot, p.attrs)
}

pub proof fn lemma_initial_decisions(s: State, c: Constants)
    requires init(s, c)
    ensures decisions(s, c)
{
    reveal(decisions);
}

pub proof fn lemma_decision_persists(s: State, s_: State, c: Constants,
    id: Instance, b: int, attrs: Attributes)
    requires s.network.subset_of(s_.network), s.submitted[id] == s_.submitted[id], decision(s, c, id, b, attrs)
    ensures decision(s_, c, id, b, attrs)
{
    reveal(decision);
    if exists |batch: Map<int, Packet>| fast_certificate(s, c, id, attrs, batch) {
        let batch = choose |batch: Map<int, Packet>| fast_certificate(s, c, id, attrs, batch);
        lemma_replies_persist(s, s_, c, id.owner, id, 0, Kind::PreAcceptOk, batch);
        assert(fast_certificate(s_, c, id, attrs, batch));
    }
    if exists |batch: Map<int, Packet>, coordinator: int| slow_chosen(s, c, id, b, attrs, batch, coordinator) {
        let (batch, coordinator) = choose |batch: Map<int, Packet>, coordinator: int|
            slow_chosen(s, c, id, b, attrs, batch, coordinator);
        lemma_replies_persist(s, s_, c, coordinator, id, b, Kind::AcceptOk, batch);
        assert(slow_chosen(s_, c, id, b, attrs, batch, coordinator));
    }
}

pub proof fn lemma_union_identical_replies(batch: Map<int, Packet>, deps: Set<Instance>)
    requires batch.dom().len() > 0,
        forall |q: int| #[trigger] batch.dom().contains(q) ==> batch[q].attrs.deps == deps
    ensures union_reply_deps(batch) == deps
{
    broadcast use group_set_lib_default;
    broadcast use group_set_properties;
    let q = batch.dom().choose();
    let sets = batch.dom().map(|q: int| batch[q].attrs.deps);
    batch.dom().lemma_map_contains(|q: int| batch[q].attrs.deps, deps);
    assert(sets.contains(deps));
    assert forall |id: Instance| #![trigger deps.contains(id)] deps.contains(id) implies union_reply_deps(batch).contains(id) by {
        sets.lemma_flatten_contains(id);
    }
    assert(union_reply_deps(batch) =~= deps);
}

pub proof fn lemma_fast_decision(s: State, s_: State, c: Constants, node: int, id: Instance, batch: Map<int, Packet>)
    requires valid_constants(c), references_known(s, c), validity(s, c), finish_preaccept(s, s_, c, node, id, batch)
    ensures record(s_.nodes[node], id).phase is Committed
        ==> decision(s_, c, id, 0, record(s_.nodes[node], id).attrs)
{
    reveal(references_known);
    reveal(validity);
    reveal(decision);
    let r = record(s.nodes[node], id);
    if record(s_.nodes[node], id).phase is Committed {
        lemma_union_identical_replies(batch, r.initial_deps);
        lemma_replies_persist(s, s_, c, node, id, 0, Kind::PreAcceptOk, batch);
        assert(fast_certificate(s_, c, id, record(s_.nodes[node], id).attrs, batch));
    }
}

pub proof fn lemma_slow_vote_has_proposal(s: State, c: Constants, id: Instance, b: int,
    attrs: Attributes, votes: Map<int, Packet>, coordinator: int) -> (p: Packet)
    requires valid_constants(c), evidence(s, c), slow_chosen(s, c, id, b, attrs, votes, coordinator)
    ensures s.network.contains(p), p.kind is Accept, p.instance == id, p.ballot == b, p.attrs == attrs
{
    broadcast use group_set_properties;
    reveal(evidence);
    assert(votes.dom().len() > 0);
    let voter = votes.dom().choose();
    let vote = votes[voter];
    assert(vote_evidence(s, vote));
    choose |p: Packet| #[trigger] s.network.contains(p)
        && p.kind is Accept && p.instance == vote.instance && p.ballot == vote.ballot
        && p.attrs == vote.attrs && p.src == vote.dst
}

pub proof fn lemma_slow_decision(s: State, s_: State, c: Constants, node: int,
    id: Instance, b: int, batch: Map<int, Packet>)
    requires bounds(s, c), evidence(s, c), same_ballot_agreement(s), finish_accept(s, s_, c, node, id, b, batch)
    ensures decision(s_, c, id, b, record(s_.nodes[node], id).attrs)
{
    reveal(evidence);
    reveal(same_ballot_agreement);
    reveal(decision);
    let r = record(s.nodes[node], id);
    assert(record_bounds(r));
    assert(record_evidence(s, id, r));
    let proposal = choose |p: Packet| #[trigger] s.network.contains(p)
        && p.instance == id && p.ballot == r.accepted_ballot && p.attrs == r.attrs
        && if r.phase is Committed { p.kind is Commit } else { p.kind is Accept };
    assert forall |q: int| #[trigger] batch.dom().contains(q) implies batch[q].attrs == r.attrs by {
        let vote = batch[q];
        assert(vote_evidence(s, vote));
        let original = choose |p: Packet| #[trigger] s.network.contains(p)
            && p.kind is Accept && p.instance == vote.instance && p.ballot == vote.ballot
            && p.attrs == vote.attrs && p.src == vote.dst;
        assert(original.attrs == proposal.attrs);
    }
    lemma_replies_persist(s, s_, c, node, id, b, Kind::AcceptOk, batch);
    assert(slow_chosen(s_, c, id, b, r.attrs, batch, node));
}

pub proof fn lemma_recovered_decision(s: State, s_: State, c: Constants, node: int,
    id: Instance, b: int, batch: Map<int, Packet>, q: int)
    requires evidence(s, c), finish_recovery(s, s_, c, node, id, b, batch, q)
    ensures maximal_committed(batch).len() > 0
        ==> decision(s_, c, id, b, record(s_.nodes[node], id).attrs)
{
    reveal(evidence);
    reveal(decision);
    if maximal_committed(batch).len() > 0 {
        let response = batch[q];
        assert(snapshot_evidence(s, response));
        let r = response.snapshot;
        let earlier = choose |p: Packet| #[trigger] s.network.contains(p)
            && p.instance == id && p.ballot == r.accepted_ballot && p.attrs == r.attrs
            && if r.phase is Committed { p.kind is Commit } else { p.kind is Accept };
        assert(s_.network.contains(earlier));
    }
}

pub proof fn lemma_step_decisions(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        same_ballot_agreement(s), validity(s, c), evidence(s, c), decisions(s, c), step(s, s_, c, a)
    ensures decisions(s_, c)
{
    broadcast use group_set_lib_default;
    lemma_step_progress(s, s_, c, a);
    reveal(step);
    reveal(references_known);
    reveal(decisions);
    match a {
        Action::FinishPreAccept { node, id, batch } => lemma_fast_decision(s, s_, c, node, id, batch),
        Action::FinishAccept { node, id, ballot, batch } => lemma_slow_decision(s, s_, c, node, id, ballot, batch),
        Action::FinishRecovery { node, id, ballot, batch, selected } => lemma_recovered_decision(s, s_, c, node, id, ballot, batch, selected),
        _ => {},
    }
    assert forall |p: Packet| #[trigger] s_.network.contains(p) && p.kind is Commit
        implies decision(s_, c, p.instance, p.ballot, p.attrs) by {
        if s.network.contains(p) {
            lemma_decision_persists(s, s_, c, p.instance, p.ballot, p.attrs);
        }
    }
}

pub proof fn lemma_behavior_decisions(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures decisions(states[i], c)
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_decisions(states[0], c);
    } else {
        lemma_behavior_decisions(states, c, i - 1);
        lemma_behavior_bounds(states, c, i - 1);
        lemma_behavior_references(states, c, i - 1);
        lemma_behavior_coordinator(states, c, i - 1);
        lemma_behavior_validity(states, c, i - 1);
        lemma_behavior_evidence(states, c, i - 1);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_decisions(states[i - 1], states[i], c, a);
    }
}

} // verus!
