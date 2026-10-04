//! Accepted records and recovery snapshots are backed by actual sent proposals.
use super::types::*;
use super::model::*;
use super::behavior::*;
use super::invariants::*;
use super::identities::*;
use super::progress::*;
use super::coordinator::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn record_evidence(s: State, id: Instance, r: Record) -> bool {
    stable(r) ==> exists |p: Packet| #[trigger] s.network.contains(p)
        && p.instance == id && p.ballot == r.accepted_ballot && p.attrs == r.attrs
        && if r.phase is Committed { p.kind is Commit } else { p.kind is Accept }
}

pub open spec fn vote_evidence(s: State, p: Packet) -> bool {
    let r = record(s.nodes[p.src], p.instance);
    &&& r.promise >= p.ballot
    &&& r.accepted_ballot >= p.ballot
    &&& stable(r)
    &&& r.accepted_ballot == p.ballot ==> r.attrs == p.attrs
    &&& exists |q: Packet| #[trigger] s.network.contains(q)
        && q.kind is Accept && q.instance == p.instance && q.ballot == p.ballot
        && q.attrs == p.attrs && q.src == p.dst
}

pub open spec fn snapshot_evidence(s: State, p: Packet) -> bool {
    let r = record(s.nodes[p.src], p.instance);
    &&& record_bounds(p.snapshot)
    &&& p.snapshot.promise == p.ballot
    &&& p.snapshot.accepted_ballot < p.ballot
    &&& r.promise >= p.ballot
    &&& r.accepted_ballot >= p.snapshot.accepted_ballot
    &&& stable(p.snapshot) ==> stable(r)
    &&& (stable(p.snapshot) && r.accepted_ballot == p.snapshot.accepted_ballot) ==> r.attrs == p.snapshot.attrs
    &&& record_evidence(s, p.instance, p.snapshot)
}

pub open spec fn snapshot_covers_vote(snapshot: Packet, vote: Packet) -> bool {
    &&& snapshot.snapshot.accepted_ballot >= vote.ballot
    &&& stable(snapshot.snapshot)
    &&& snapshot.snapshot.accepted_ballot == vote.ballot ==> snapshot.snapshot.attrs == vote.attrs
}

#[verifier::opaque]
pub open spec fn evidence(s: State, c: Constants) -> bool {
    &&& forall |node: int, id: Instance| member(c, node)
        ==> record_evidence(s, id, #[trigger] record(s.nodes[node], id))
    &&& forall |p: Packet| #[trigger] s.network.contains(p) ==> {
        &&& p.kind is AcceptOk ==> vote_evidence(s, p)
        &&& p.kind is RecoverOk ==> snapshot_evidence(s, p)
    }
    &&& forall |p: Packet, q: Packet| #![trigger s.network.contains(p), s.network.contains(q)]
        s.network.contains(p) && s.network.contains(q)
        && p.kind is RecoverOk && q.kind is AcceptOk && p.src == q.src && p.instance == q.instance
        && q.ballot < p.ballot ==> snapshot_covers_vote(p, q)
}

pub proof fn lemma_initial_evidence(s: State, c: Constants)
    requires init(s, c)
    ensures evidence(s, c)
{
    reveal(evidence);
}

pub proof fn lemma_publish_record_evidence(s: State, c: Constants, node: int, id: Instance,
    b: int, attrs: Attributes, commit: bool)
    requires member(c, node), s.nodes.len() == c.n
    ensures record_evidence(publish(s, c, node, id, b, attrs, commit), id,
        record(publish(s, c, node, id, b, attrs, commit).nodes[node], id)),
        !commit ==> vote_evidence(publish(s, c, node, id, b, attrs, commit),
            packet(Kind::AcceptOk, node, node, id, b, attrs)),
{
    broadcast use group_set_lib_default;
    let p = packet(if commit { Kind::Commit } else { Kind::Accept }, node, node, id, b, attrs);
    assert(members(c).contains(node));
    let f = |dst: int| Packet { dst, ..p };
    assert(p == f(node));
    members(c).lemma_map_contains(f, p);
    assert(broadcast(c, p).contains(p));
    assert(publish(s, c, node, id, b, attrs, commit).network.contains(p));
}

// lemma_step_evidence is split into one lemma per conjunct of `evidence`,
// with each conjunct passed as a raw quantified hypothesis instead of
// revealing the whole predicate: reveal(evidence) is all-or-nothing, and the
// pairwise packet quantifiers a sub-proof does not use dominate the solver
// bill if they are in scope at all.

#[verifier::spinoff_prover]
proof fn lemma_step_record_evidence(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        // same_ballot_agreement stays opaque here: lemma_step_coordinator
        // needs the fact, the proof below never needs its body.
        coordinator_invariant(s, c), same_ballot_agreement(s), step(s, s_, c, a),
        forall |node: int, id: Instance| member(c, node)
            ==> record_evidence(s, id, #[trigger] record(s.nodes[node], id)),
    ensures forall |node: int, id: Instance| member(c, node)
        ==> record_evidence(s_, id, #[trigger] record(s_.nodes[node], id))
{
    broadcast use group_set_lib_default;
    lemma_step_progress(s, s_, c, a);
    lemma_step_coordinator(s, s_, c, a);
    reveal(step);
    assert forall |node: int, id: Instance| member(c, node)
        implies record_evidence(s_, id, #[trigger] record(s_.nodes[node], id)) by {
        assert(record_evidence(s, id, record(s.nodes[node], id)));
        match a {
            Action::FinishPreAccept { node: actor, id: target, batch } => {
                let r = record(s.nodes[actor], target);
                let attrs = Attributes { payload: r.attrs.payload, deps: union_reply_deps(batch) };
                let fast = fast_quorum(c, batch.dom()) && forall |q: int| #[trigger] batch.dom().contains(q)
                    ==> batch[q].attrs.deps == r.initial_deps;
                lemma_publish_record_evidence(s, c, actor, target, 0, attrs, fast);
            },
            Action::FinishAccept { node: actor, id: target, ballot, batch } => {
                lemma_publish_record_evidence(s, c, actor, target, ballot, record(s.nodes[actor], target).attrs, true);
            },
            Action::FinishRecovery { node: actor, id: target, ballot, batch, selected } => {
                if batch.dom().contains(selected) {
                    lemma_publish_record_evidence(s, c, actor, target, ballot, batch[selected].snapshot.attrs, true);
                    lemma_publish_record_evidence(s, c, actor, target, ballot, batch[selected].snapshot.attrs, false);
                }
                lemma_publish_record_evidence(s, c, actor, target, ballot, nop_attrs(), false);
            },
            Action::FinishValidation { node: actor, id: target, ballot, batch } => {
                lemma_publish_record_evidence(s, c, actor, target, ballot, s.nodes[actor].attempts[target].candidate, false);
                lemma_publish_record_evidence(s, c, actor, target, ballot, nop_attrs(), false);
            },
            Action::ResolveWaiting { node: actor, id: target, ballot, resolution } => {
                lemma_publish_record_evidence(s, c, actor, target, ballot, s.nodes[actor].attempts[target].candidate, false);
                lemma_publish_record_evidence(s, c, actor, target, ballot, nop_attrs(), false);
            },
            _ => {},
        }
    }
}

// rlimit 150: measured, not padded. This single-packet query must hold the
// revealed step relation together with same_ballot_agreement's pairwise
// packet quantifier (both load-bearing: the proof fails without either), and
// that combination sits just above the default budget on the pinned release
// while fitting comfortably on 0.2026.10.04. Every surrounding obligation
// was split off first; see the lemmas around this one.
#[verifier::spinoff_prover]
#[verifier::rlimit(150)]
proof fn lemma_step_vote_evidence_one(s: State, s_: State, c: Constants, a: Action, p: Packet)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        coordinator_invariant(s, c), same_ballot_agreement(s), step(s, s_, c, a),
        s_.network.contains(p), p.kind is AcceptOk,
        s.network.contains(p) ==> vote_evidence(s, p),
        forall |node: int, id: Instance| member(c, node)
            ==> record_evidence(s_, id, #[trigger] record(s_.nodes[node], id)),
    ensures vote_evidence(s_, p)
{
    broadcast use group_set_lib_default;
    lemma_step_progress(s, s_, c, a);
    lemma_step_coordinator(s, s_, c, a);
    reveal(step);
    if let Action::Submit { node, value } = a {
        lemma_submission_fresh(s, c, node);
    }
    reveal(coordinator_invariant);
    reveal(same_ballot_agreement);
    assert(record_bounds(record(s.nodes[p.src], p.instance)));
    assert(record_evidence(s_, p.instance, record(s_.nodes[p.src], p.instance)));
    let r = record(s_.nodes[p.src], p.instance);
    assert(r.promise >= p.ballot);
    assert(r.accepted_ballot >= p.ballot);
    assert(stable(r));
    assert(r.accepted_ballot == p.ballot ==> r.attrs == p.attrs);
    assert(exists |q: Packet| #[trigger] s_.network.contains(q)
        && q.kind is Accept && q.instance == p.instance && q.ballot == p.ballot
        && q.attrs == p.attrs && q.src == p.dst);
    assert(vote_evidence(s_, p));
}

proof fn lemma_step_vote_evidence(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        coordinator_invariant(s, c), same_ballot_agreement(s), step(s, s_, c, a),
        forall |p: Packet| #[trigger] s.network.contains(p) ==>
            (p.kind is AcceptOk ==> vote_evidence(s, p)),
        forall |node: int, id: Instance| member(c, node)
            ==> record_evidence(s_, id, #[trigger] record(s_.nodes[node], id)),
    ensures forall |p: Packet| #[trigger] s_.network.contains(p) ==>
        (p.kind is AcceptOk ==> vote_evidence(s_, p))
{
    assert forall |p: Packet| #[trigger] s_.network.contains(p) && p.kind is AcceptOk
        implies vote_evidence(s_, p) by {
        lemma_step_vote_evidence_one(s, s_, c, a, p);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_step_snapshot_evidence(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        coordinator_invariant(s, c), same_ballot_agreement(s), step(s, s_, c, a),
        forall |p: Packet| #[trigger] s.network.contains(p) ==>
            (p.kind is RecoverOk ==> snapshot_evidence(s, p)),
        forall |node: int, id: Instance| member(c, node)
            ==> record_evidence(s_, id, #[trigger] record(s_.nodes[node], id)),
    ensures forall |p: Packet| #[trigger] s_.network.contains(p) ==>
        (p.kind is RecoverOk ==> snapshot_evidence(s_, p))
{
    broadcast use group_set_lib_default;
    lemma_step_progress(s, s_, c, a);
    lemma_step_coordinator(s, s_, c, a);
    reveal(step);
    if let Action::Submit { node, value } = a {
        lemma_submission_fresh(s, c, node);
    }
    reveal(coordinator_invariant);
    reveal(same_ballot_agreement);
    assert forall |p: Packet| #[trigger] s_.network.contains(p) && p.kind is RecoverOk
        implies snapshot_evidence(s_, p) by {
        assert(record_bounds(record(s.nodes[p.src], p.instance)));
        assert(record_evidence(s_, p.instance, record(s_.nodes[p.src], p.instance)));
        if s.network.contains(p) {
            assert(snapshot_evidence(s, p));
        }
        assert(snapshot_evidence(s_, p));
    }
}

proof fn lemma_step_packet_evidence(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        coordinator_invariant(s, c), same_ballot_agreement(s), step(s, s_, c, a),
        forall |p: Packet| #[trigger] s.network.contains(p) ==> {
            &&& p.kind is AcceptOk ==> vote_evidence(s, p)
            &&& p.kind is RecoverOk ==> snapshot_evidence(s, p)
        },
        forall |node: int, id: Instance| member(c, node)
            ==> record_evidence(s_, id, #[trigger] record(s_.nodes[node], id)),
    ensures forall |p: Packet| #[trigger] s_.network.contains(p) ==> {
        &&& p.kind is AcceptOk ==> vote_evidence(s_, p)
        &&& p.kind is RecoverOk ==> snapshot_evidence(s_, p)
    }
{
    lemma_step_vote_evidence(s, s_, c, a);
    lemma_step_snapshot_evidence(s, s_, c, a);
}

#[verifier::spinoff_prover]
proof fn lemma_step_snapshot_covers(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        coordinator_invariant(s, c), same_ballot_agreement(s), step(s, s_, c, a),
        forall |p: Packet| #[trigger] s.network.contains(p) ==> {
            &&& p.kind is AcceptOk ==> vote_evidence(s, p)
            &&& p.kind is RecoverOk ==> snapshot_evidence(s, p)
        },
        forall |p: Packet, q: Packet| #![trigger s.network.contains(p), s.network.contains(q)]
            s.network.contains(p) && s.network.contains(q)
            && p.kind is RecoverOk && q.kind is AcceptOk && p.src == q.src && p.instance == q.instance
            && q.ballot < p.ballot ==> snapshot_covers_vote(p, q),
    ensures forall |p: Packet, q: Packet| #![trigger s_.network.contains(p), s_.network.contains(q)]
        s_.network.contains(p) && s_.network.contains(q)
        && p.kind is RecoverOk && q.kind is AcceptOk && p.src == q.src && p.instance == q.instance
        && q.ballot < p.ballot ==> snapshot_covers_vote(p, q)
{
    broadcast use group_set_lib_default;
    lemma_step_progress(s, s_, c, a);
    lemma_step_coordinator(s, s_, c, a);
    reveal(step);
    reveal(references_known);
    reveal(coordinator_invariant);
    reveal(same_ballot_agreement);
    assert forall |p: Packet, q: Packet| s_.network.contains(p) && s_.network.contains(q)
        && p.kind is RecoverOk && q.kind is AcceptOk && p.src == q.src && p.instance == q.instance
        && q.ballot < p.ballot implies snapshot_covers_vote(p, q) by {
        if s.network.contains(p) {
            assert(snapshot_evidence(s, p));
        }
        if s.network.contains(q) {
            assert(vote_evidence(s, q));
        }
    }
}

pub proof fn lemma_step_evidence(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        coordinator_invariant(s, c), same_ballot_agreement(s), evidence(s, c), step(s, s_, c, a)
    ensures evidence(s_, c)
{
    reveal(evidence);
    lemma_step_record_evidence(s, s_, c, a);
    lemma_step_packet_evidence(s, s_, c, a);
    lemma_step_snapshot_covers(s, s_, c, a);
}

pub proof fn lemma_behavior_evidence(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures evidence(states[i], c)
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_evidence(states[0], c);
    } else {
        lemma_behavior_evidence(states, c, i - 1);
        lemma_behavior_bounds(states, c, i - 1);
        lemma_behavior_references(states, c, i - 1);
        lemma_behavior_coordinator(states, c, i - 1);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_evidence(states[i - 1], states[i], c, a);
    }
}

} // verus!
