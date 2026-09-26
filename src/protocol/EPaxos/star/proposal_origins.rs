//! Why a recovery proposes the original command, an inherited value, or Nop.
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
use super::knowledge::*;
use super::validation_evidence::*;
use super::recovery_certificates::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn conflict_abort(s: State, c: Constants, id: Instance, p: Packet) -> bool {
    &&& s.network.contains(p)
    &&& p.kind is Commit || p.kind is Waiting
    &&& p.instance != id
    &&& !(p.attrs.payload is Nop)
    &&& conflicts(c, s.submitted[id].payload, p.attrs.payload)
    &&& !covers(id, s.submitted[id], p.instance, p.attrs)
}

#[verifier::opaque]
pub open spec fn abandoned_pending(s: State, c: Constants, node: int, id: Instance, b: int) -> bool {
    exists |batch: Map<int, Packet>| {
        &&& #[trigger] replies(s, c, node, id, b, Kind::RecoverOk, batch)
        &&& majority(c, batch.dom())
        &&& stable_max(batch).len() == 0
        &&& pending_support(batch).len() < batch.dom().len() - c.e
    }
}

#[verifier::opaque]
pub open spec fn origin(s: State, c: Constants, node: int, id: Instance, b: int, attrs: Attributes) -> bool {
    ||| b == 0
    ||| attrs == s.submitted[id]
    ||| exists |p: Packet| #[trigger] s.network.contains(p) && proposal(p)
        && p.instance == id && 0 <= p.ballot < b && p.attrs == attrs
    ||| attrs == nop_attrs() && (abandoned_pending(s, c, node, id, b)
        || exists |p: Packet| conflict_abort(s, c, id, p))
}

#[verifier::opaque]
pub open spec fn origins(s: State, c: Constants) -> bool {
    &&& forall |p: Packet| #[trigger] s.network.contains(p) && proposal(p)
        ==> origin(s, c, p.src, p.instance, p.ballot, p.attrs)
    &&& forall |node: int, id: Instance| member(c, node) && #[trigger] s.nodes[node].attempts.dom().contains(id) ==> {
        let a = s.nodes[node].attempts[id];
        final_stage(a.stage) ==> origin(s, c, node, id, a.ballot, a.candidate)
    }
}

pub proof fn lemma_initial_origins(s: State, c: Constants)
    requires init(s, c)
    ensures origins(s, c)
{
    reveal(origins);
}

pub proof fn lemma_origin_persists(s: State, s_: State, c: Constants,
    node: int, id: Instance, b: int, attrs: Attributes)
    requires s.network.subset_of(s_.network), s.submitted[id] == s_.submitted[id],
        origin(s, c, node, id, b, attrs)
    ensures origin(s_, c, node, id, b, attrs)
{
    reveal(origin);
    reveal(abandoned_pending);
    if abandoned_pending(s, c, node, id, b) {
        let batch = choose |batch: Map<int, Packet>| {
            &&& #[trigger] replies(s, c, node, id, b, Kind::RecoverOk, batch)
            &&& majority(c, batch.dom())
            &&& stable_max(batch).len() == 0
            &&& pending_support(batch).len() < batch.dom().len() - c.e
        };
        lemma_replies_persist(s, s_, c, node, id, b, Kind::RecoverOk, batch);
    }
    if exists |p: Packet| conflict_abort(s, c, id, p) {
        let p = choose |p: Packet| conflict_abort(s, c, id, p);
        assert(conflict_abort(s_, c, id, p));
    }
}

pub proof fn lemma_snapshot_origin(s: State, c: Constants, node: int,
    id: Instance, b: int, p: Packet)
    requires evidence(s, c), s.network.contains(p), p.kind is RecoverOk,
        p.instance == id, p.ballot == b, stable(p.snapshot)
    ensures origin(s, c, node, id, b, p.snapshot.attrs)
{
    reveal(evidence);
    reveal(origin);
    assert(snapshot_evidence(s, p));
    let earlier = choose |q: Packet| #[trigger] s.network.contains(q)
        && q.instance == id && q.ballot == p.snapshot.accepted_ballot && q.attrs == p.snapshot.attrs
        && if p.snapshot.phase is Committed { q.kind is Commit } else { q.kind is Accept };
}

pub proof fn lemma_committed_invalidator_origin(s: State, c: Constants,
    node: int, id: Instance, b: int, i: Invalidation)
    requires references_known(s, c), validity(s, c), invalidation_sound(s, c, id, i), i.committed
    ensures origin(s, c, node, id, b, nop_attrs())
{
    reveal(references_known);
    reveal(validity);
    reveal(origin);
    let p = choose |p: Packet| #[trigger] s.network.contains(p) && p.kind is Commit
        && p.instance == i.instance && !(p.attrs.payload is Nop) && !p.attrs.deps.contains(id);
    assert(conflict_abort(s, c, id, p));
}

pub proof fn lemma_recovery_origin(s: State, s_: State, c: Constants, node: int,
    id: Instance, b: int, batch: Map<int, Packet>, q: int)
    requires evidence(s, c), finish_recovery(s, s_, c, node, id, b, batch, q)
    ensures final_stage(s_.nodes[node].attempts[id].stage)
        ==> origin(s_, c, node, id, b, s_.nodes[node].attempts[id].candidate)
{
    broadcast use group_set_properties;
    if maximal_committed(batch).len() > 0 || maximal_accepted(batch).len() > 0 {
        assert(s.network.contains(batch[q]));
        lemma_snapshot_origin(s, c, node, id, b, batch[q]);
        lemma_origin_persists(s, s_, c, node, id, b, batch[q].snapshot.attrs);
    } else {
        reveal(origin);
        reveal(abandoned_pending);
        assert(stable_max(batch) =~= maximal_committed(batch).union(maximal_accepted(batch)));
        assert(stable_max(batch).len() == 0);
        lemma_replies_persist(s, s_, c, node, id, b, Kind::RecoverOk, batch);
    }
}

pub proof fn lemma_validation_origin(s: State, s_: State, c: Constants,
    node: int, id: Instance, ballot: int, batch: Map<int, Packet>)
    requires references_known(s, c), validity(s, c), validation_evidence(s, c),
        finish_validation(s, s_, c, node, id, ballot, batch)
    ensures final_stage(s_.nodes[node].attempts[id].stage)
        ==> origin(s_, c, node, id, ballot, s_.nodes[node].attempts[id].candidate)
{
    broadcast use group_set_lib_default;
    broadcast use group_set_properties;
    reveal(references_known);
    reveal(validity);
    reveal(validation_evidence);
    let invalidating = batch.dom().map(|q: int| batch[q].invalidating).flatten();
    let committed = invalidating.filter(|i: Invalidation| i.committed);
    if committed.len() > 0 {
        let i = committed.choose();
        assert(invalidation_sound(s, c, id, i));
        lemma_committed_invalidator_origin(s, c, node, id, ballot, i);
        lemma_origin_persists(s, s_, c, node, id, ballot, nop_attrs());
    }
    reveal(origin);
}

pub proof fn lemma_waiting_origin(s: State, s_: State, c: Constants,
    node: int, id: Instance, ballot: int, resolution: Resolution)
    requires references_known(s, c), validity(s, c), evidence(s, c), validation_evidence(s, c),
        resolve_waiting(s, s_, c, node, id, ballot, resolution)
    ensures origin(s_, c, node, id, ballot, s_.nodes[node].attempts[id].candidate)
{
    broadcast use group_set_lib_default;
    reveal(references_known);
    reveal(validity);
    reveal(evidence);
    reveal(validation_evidence);
    let attempt = s.nodes[node].attempts[id];
    match resolution {
        Resolution::Ready => {},
        Resolution::Waiting { packet: p } => {
            let i = choose |i: Invalidation| #[trigger] attempt.invalidating.contains(i) && i.instance == p.instance;
            assert(invalidation_sound(s, c, id, i));
            assert(conflict_abort(s, c, id, p));
            assert(conflict_abort(s_, c, id, p));
        },
        Resolution::Invalidated { instance: other } => {
            let i = choose |i: Invalidation| #[trigger] attempt.invalidating.contains(i) && i.instance == other;
            assert(invalidation_sound(s, c, id, i));
            let r = record(s.nodes[node], other);
            assert(record_evidence(s, other, r));
            let p = choose |p: Packet| #[trigger] s.network.contains(p)
                && p.instance == other && p.ballot == r.accepted_ballot && p.attrs == r.attrs
                && if r.phase is Committed { p.kind is Commit } else { p.kind is Accept };
            assert(conflict_abort(s, c, id, p));
            assert(conflict_abort(s_, c, id, p));
        },
    }
    reveal(origin);
}

pub proof fn lemma_zero_origin(s: State, c: Constants, node: int, id: Instance, attrs: Attributes)
    ensures origin(s, c, node, id, 0, attrs)
{
    reveal(origin);
}

pub proof fn lemma_step_origins(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        coordinator_invariant(s, c), same_ballot_agreement(s), validity(s, c), evidence(s, c), validation_evidence(s, c),
        origins(s, c), step(s, s_, c, a)
    ensures origins(s_, c)
{
    broadcast use group_set_lib_default;
    broadcast use group_set_properties;
    lemma_step_progress(s, s_, c, a);
    lemma_step_coordinator(s, s_, c, a);
    reveal(step);
    reveal(references_known);
    reveal(coordinator_invariant);
    reveal(origins);
    match a {
        Action::FinishPreAccept { node, id, batch } => {
            lemma_zero_origin(s_, c, node, id, s_.nodes[node].attempts[id].candidate);
        },
        Action::FinishRecovery { node, id, ballot, batch, selected } => {
            lemma_recovery_origin(s, s_, c, node, id, ballot, batch, selected);
        },
        Action::FinishValidation { node, id, ballot, batch } => {
            lemma_validation_origin(s, s_, c, node, id, ballot, batch);
        },
        Action::ResolveWaiting { node, id, ballot, resolution } => {
            lemma_waiting_origin(s, s_, c, node, id, ballot, resolution);
        },
        _ => {},
    }
    assert forall |node: int, id: Instance| member(c, node) && #[trigger] s_.nodes[node].attempts.dom().contains(id) implies {
        let a = s_.nodes[node].attempts[id];
        final_stage(a.stage) ==> origin(s_, c, node, id, a.ballot, a.candidate)
    } by {
        if s.nodes[node].attempts.dom().contains(id) && final_stage(s.nodes[node].attempts[id].stage) {
            let old = s.nodes[node].attempts[id];
            lemma_origin_persists(s, s_, c, node, id, old.ballot, old.candidate);
        }
    }
    assert forall |p: Packet| #[trigger] s_.network.contains(p) && proposal(p)
        implies origin(s_, c, p.src, p.instance, p.ballot, p.attrs) by {
        if s.network.contains(p) {
            lemma_origin_persists(s, s_, c, p.src, p.instance, p.ballot, p.attrs);
        } else {
            assert(s_.nodes[p.src].attempts.dom().contains(p.instance));
            let a = s_.nodes[p.src].attempts[p.instance];
            assert(a.ballot == p.ballot);
            assert(final_stage(a.stage));
            assert(a.candidate == p.attrs);
            assert(origin(s_, c, p.src, p.instance, a.ballot, a.candidate));
        }
    }
}

pub proof fn lemma_behavior_origins(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures origins(states[i], c)
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_origins(states[0], c);
    } else {
        lemma_behavior_origins(states, c, i - 1);
        lemma_behavior_bounds(states, c, i - 1);
        lemma_behavior_references(states, c, i - 1);
        lemma_behavior_coordinator(states, c, i - 1);
        lemma_behavior_validity(states, c, i - 1);
        lemma_behavior_evidence(states, c, i - 1);
        lemma_behavior_validation_evidence(states, c, i - 1);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_origins(states[i - 1], states[i], c, a);
    }
}

} // verus!
