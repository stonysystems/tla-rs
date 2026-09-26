//! Historical phase-one certificates, used to reason about higher ballots.
use super::types::*;
use super::model::*;
use super::recovery::*;
use super::behavior::*;
use super::invariants::*;
use super::identities::*;
use super::progress::*;
use super::coordinator::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn stable_max(batch: Map<int, Packet>) -> Set<int> {
    batch.dom().filter(|q: int| maximal(batch, q) && stable(batch[q].snapshot))
}

pub open spec fn selected_from_max(batch: Map<int, Packet>, attrs: Attributes) -> bool {
    exists |q: int| #[trigger] stable_max(batch).contains(q) && batch[q].snapshot.attrs == attrs
}

#[verifier::opaque]
pub open spec fn recovery_certificate(s: State, c: Constants, node: int,
    id: Instance, b: int, attrs: Attributes) -> bool {
    exists |batch: Map<int, Packet>| {
        &&& #[trigger] replies(s, c, node, id, b, Kind::RecoverOk, batch)
        &&& majority(c, batch.dom())
        &&& stable_max(batch).len() > 0 ==> selected_from_max(batch, attrs)
    }
}

#[verifier::opaque]
pub open spec fn empty_recovery(s: State, c: Constants, node: int, id: Instance, b: int) -> bool {
    exists |batch: Map<int, Packet>| {
        &&& #[trigger] replies(s, c, node, id, b, Kind::RecoverOk, batch)
        &&& majority(c, batch.dom())
        &&& stable_max(batch).len() == 0
    }
}

#[verifier::opaque]
pub open spec fn recovery_certificates(s: State, c: Constants) -> bool {
    &&& forall |p: Packet| #[trigger] s.network.contains(p) && proposal(p) && p.ballot > 0
        ==> recovery_certificate(s, c, p.src, p.instance, p.ballot, p.attrs)
    &&& forall |node: int, id: Instance| member(c, node) && #[trigger] s.nodes[node].attempts.dom().contains(id) ==> {
        let a = s.nodes[node].attempts[id];
        &&& (a.stage is Validating || a.stage is Waiting) ==> empty_recovery(s, c, node, id, a.ballot)
        &&& (final_stage(a.stage) && a.ballot > 0) ==> recovery_certificate(s, c, node, id, a.ballot, a.candidate)
    }
}

pub proof fn lemma_initial_recovery_certificates(s: State, c: Constants)
    requires init(s, c)
    ensures recovery_certificates(s, c)
{
    reveal(recovery_certificates);
}

pub proof fn lemma_replies_persist(s: State, s_: State, c: Constants,
    node: int, id: Instance, b: int, kind: Kind, batch: Map<int, Packet>)
    requires s.network.subset_of(s_.network), replies(s, c, node, id, b, kind, batch)
    ensures replies(s_, c, node, id, b, kind, batch)
{
}

pub proof fn lemma_certificate_persists(s: State, s_: State, c: Constants,
    node: int, id: Instance, b: int, attrs: Attributes)
    requires s.network.subset_of(s_.network), recovery_certificate(s, c, node, id, b, attrs)
    ensures recovery_certificate(s_, c, node, id, b, attrs)
{
    reveal(recovery_certificate);
    let batch = choose |batch: Map<int, Packet>| {
        &&& #[trigger] replies(s, c, node, id, b, Kind::RecoverOk, batch)
        &&& majority(c, batch.dom())
        &&& stable_max(batch).len() > 0 ==> selected_from_max(batch, attrs)
    };
    lemma_replies_persist(s, s_, c, node, id, b, Kind::RecoverOk, batch);
}

pub proof fn lemma_empty_recovery_persists(s: State, s_: State, c: Constants,
    node: int, id: Instance, b: int, attrs: Attributes)
    requires s.network.subset_of(s_.network), empty_recovery(s, c, node, id, b)
    ensures empty_recovery(s_, c, node, id, b), recovery_certificate(s_, c, node, id, b, attrs)
{
    reveal(empty_recovery);
    reveal(recovery_certificate);
    let batch = choose |batch: Map<int, Packet>| {
        &&& #[trigger] replies(s, c, node, id, b, Kind::RecoverOk, batch)
        &&& majority(c, batch.dom())
        &&& stable_max(batch).len() == 0
    };
    lemma_replies_persist(s, s_, c, node, id, b, Kind::RecoverOk, batch);
}

pub proof fn lemma_recovery_branch_certificate(s: State, s_: State, c: Constants,
    node: int, id: Instance, b: int, batch: Map<int, Packet>, q: int)
    requires finish_recovery(s, s_, c, node, id, b, batch, q)
    ensures
        (s_.nodes[node].attempts[id].stage is Validating)
            ==> empty_recovery(s_, c, node, id, b),
        final_stage(s_.nodes[node].attempts[id].stage)
            ==> recovery_certificate(s_, c, node, id, b, s_.nodes[node].attempts[id].candidate),
{
    broadcast use group_set_properties;
    reveal(empty_recovery);
    reveal(recovery_certificate);
    assert(s.network.subset_of(s_.network));
    lemma_replies_persist(s, s_, c, node, id, b, Kind::RecoverOk, batch);
    assert(stable_max(batch) =~= maximal_committed(batch).union(maximal_accepted(batch)));
    if maximal_committed(batch).len() > 0 || maximal_accepted(batch).len() > 0 {
        assert(stable_max(batch).contains(q));
        assert(selected_from_max(batch, batch[q].snapshot.attrs));
    } else {
        assert(stable_max(batch).len() == 0);
    }
}

pub proof fn lemma_step_recovery_certificates(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        coordinator_invariant(s, c), same_ballot_agreement(s), recovery_certificates(s, c), step(s, s_, c, a)
    ensures recovery_certificates(s_, c)
{
    broadcast use group_set_lib_default;
    lemma_step_progress(s, s_, c, a);
    lemma_step_coordinator(s, s_, c, a);
    reveal(step);
    reveal(recovery_certificates);
    reveal(coordinator_invariant);
    if let Action::FinishRecovery { node, id, ballot, batch, selected } = a {
        lemma_recovery_branch_certificate(s, s_, c, node, id, ballot, batch, selected);
    }
    assert forall |node: int, id: Instance| member(c, node) && #[trigger] s.nodes[node].attempts.dom().contains(id) implies {
        let a = s.nodes[node].attempts[id];
        &&& (a.stage is Validating || a.stage is Waiting) ==> empty_recovery(s_, c, node, id, a.ballot)
        &&& (a.stage is Validating || a.stage is Waiting) ==> recovery_certificate(s_, c, node, id, a.ballot, a.candidate)
        &&& (a.stage is Validating || a.stage is Waiting) ==> recovery_certificate(s_, c, node, id, a.ballot, nop_attrs())
        &&& (final_stage(a.stage) && a.ballot > 0) ==> recovery_certificate(s_, c, node, id, a.ballot, a.candidate)
    } by {
        let a = s.nodes[node].attempts[id];
        if a.stage is Validating || a.stage is Waiting {
            lemma_empty_recovery_persists(s, s_, c, node, id, a.ballot, a.candidate);
            lemma_empty_recovery_persists(s, s_, c, node, id, a.ballot, nop_attrs());
        }
        if final_stage(a.stage) && a.ballot > 0 {
            lemma_certificate_persists(s, s_, c, node, id, a.ballot, a.candidate);
        }
    }
    assert forall |node: int, id: Instance| member(c, node) && #[trigger] s_.nodes[node].attempts.dom().contains(id) implies {
        let a = s_.nodes[node].attempts[id];
        &&& (a.stage is Validating || a.stage is Waiting) ==> empty_recovery(s_, c, node, id, a.ballot)
        &&& (final_stage(a.stage) && a.ballot > 0) ==> recovery_certificate(s_, c, node, id, a.ballot, a.candidate)
    } by {
    }
    assert forall |p: Packet| #[trigger] s_.network.contains(p) && proposal(p) && p.ballot > 0
        implies recovery_certificate(s_, c, p.src, p.instance, p.ballot, p.attrs) by {
        if s.network.contains(p) {
            lemma_certificate_persists(s, s_, c, p.src, p.instance, p.ballot, p.attrs);
        }
    }
}

pub proof fn lemma_behavior_recovery_certificates(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures recovery_certificates(states[i], c)
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_recovery_certificates(states[0], c);
    } else {
        lemma_behavior_recovery_certificates(states, c, i - 1);
        lemma_behavior_bounds(states, c, i - 1);
        lemma_behavior_references(states, c, i - 1);
        lemma_behavior_coordinator(states, c, i - 1);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_recovery_certificates(states[i - 1], states[i], c, a);
    }
}

} // verus!
