//! Same-ballot uniqueness, including loss of volatile coordinator state.
use super::types::*;
use super::model::*;
use super::behavior::*;
use super::invariants::*;
use super::identities::*;
use super::progress::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn proposal(p: Packet) -> bool { p.kind is Accept || p.kind is Commit }
pub open spec fn final_stage(stage: Stage) -> bool { stage is Accepting || stage is Done }

pub open spec fn attempt_owned(n: Node, c: Constants, node: int, id: Instance) -> bool {
    let a = n.attempts[id];
    let r = record(n, id);
    &&& 0 <= a.ballot <= r.promise
    &&& owns_ballot(c, node, id, a.ballot)
    &&& (a.ballot == r.promise && final_stage(a.stage)) ==> {
        stable(r) && r.accepted_ballot == a.ballot && r.attrs == a.candidate
    }
}

pub open spec fn proposal_recorded(s: State, c: Constants, p: Packet) -> bool {
    let n = s.nodes[p.src];
    &&& owns_ballot(c, p.src, p.instance, p.ballot)
    &&& record(n, p.instance).promise >= p.ballot
    &&& (n.attempts.dom().contains(p.instance) && n.attempts[p.instance].ballot == p.ballot) ==> {
        final_stage(n.attempts[p.instance].stage) && n.attempts[p.instance].candidate == p.attrs
    }
}

#[verifier::opaque]
pub open spec fn coordinator_invariant(s: State, c: Constants) -> bool {
    &&& s.nodes.len() == c.n
    &&& forall |node: int, id: Instance| member(c, node)
        && #[trigger] s.nodes[node].attempts.dom().contains(id) ==> attempt_owned(s.nodes[node], c, node, id)
    &&& forall |p: Packet| #[trigger] s.network.contains(p) ==> {
        &&& member(c, p.src)
        &&& member(c, p.dst)
        &&& member(c, p.instance.owner)
        &&& p.ballot >= 0
        &&& proposal(p) ==> proposal_recorded(s, c, p)
    }
}

#[verifier::opaque]
pub open spec fn same_ballot_agreement(s: State) -> bool {
    forall |p: Packet, q: Packet| #![trigger s.network.contains(p), s.network.contains(q)]
        s.network.contains(p) && s.network.contains(q)
        && proposal(p) && proposal(q) && p.instance == q.instance && p.ballot == q.ballot
        ==> p.attrs == q.attrs
}

pub proof fn lemma_initial_coordinator(s: State, c: Constants)
    requires init(s, c)
    ensures coordinator_invariant(s, c), same_ballot_agreement(s)
{
    reveal(coordinator_invariant);
    reveal(same_ballot_agreement);
}

// This induction checks every handler and both old/new proposal pairs.
// Keep its solver budget local so the standard build can check the proof.
#[verifier::rlimit(40)]
pub proof fn lemma_step_coordinator(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        coordinator_invariant(s, c), same_ballot_agreement(s), step(s, s_, c, a)
    ensures coordinator_invariant(s_, c), same_ballot_agreement(s_)
{
    broadcast use group_set_lib_default;
    lemma_step_progress(s, s_, c, a);
    reveal(step);
    if let Action::Submit { node, value } = a {
        lemma_submission_fresh(s, c, node);
    }
    reveal(coordinator_invariant);
    reveal(references_known);
    reveal(allocated);
    assert forall |node: int, id: Instance| member(c, node)
        && #[trigger] s_.nodes[node].attempts.dom().contains(id)
        implies attempt_owned(s_.nodes[node], c, node, id) by {
        if s.nodes[node].attempts.dom().contains(id) {
            assert(attempt_owned(s.nodes[node], c, node, id));
        }
        assert(record_bounds(record(s.nodes[node], id)));
        match a {
            Action::Submit { node, value } => {},
            Action::PreAccept { packet } => {},
            Action::FinishPreAccept { node, id, batch } => {},
            Action::Accept { packet } => {},
            Action::FinishAccept { node, id, ballot, batch } => {},
            Action::Learn { packet } => {},
            Action::BeginRecovery { node, id, ballot } => {},
            Action::Recover { packet } => {},
            Action::FinishRecovery { node, id, ballot, batch, selected } => {},
            Action::Validate { packet } => {},
            Action::FinishValidation { node, id, ballot, batch } => {},
            Action::ResolveWaiting { node, id, ballot, resolution } => {},
            Action::Execute { node, component } => {},
            Action::Reboot { node } => {},
            Action::Stutter => {},
        }
    }
    assert forall |p: Packet| #[trigger] s_.network.contains(p) implies {
        &&& member(c, p.src)
        &&& member(c, p.dst)
        &&& member(c, p.instance.owner)
        &&& p.ballot >= 0
        &&& proposal(p) ==> proposal_recorded(s_, c, p)
    } by {
        if s.network.contains(p) {
            if proposal(p) {
                assert(proposal_recorded(s, c, p));
            }
        }
        match a {
            Action::Submit { node, value } => {},
            Action::PreAccept { packet } => {},
            Action::FinishPreAccept { node, id, batch } => {},
            Action::Accept { packet } => {},
            Action::FinishAccept { node, id, ballot, batch } => {},
            Action::Learn { packet } => {},
            Action::BeginRecovery { node, id, ballot } => {},
            Action::Recover { packet } => {},
            Action::FinishRecovery { node, id, ballot, batch, selected } => {},
            Action::Validate { packet } => {},
            Action::FinishValidation { node, id, ballot, batch } => {},
            Action::ResolveWaiting { node, id, ballot, resolution } => {},
            Action::Execute { node, component } => {},
            Action::Reboot { node } => {},
            Action::Stutter => {},
        }
    }
    reveal(same_ballot_agreement);
    assert forall |p: Packet, q: Packet| #![trigger proposal(p), proposal(q)] s_.network.contains(p) && s_.network.contains(q)
        && proposal(p) && proposal(q) && p.instance == q.instance && p.ballot == q.ballot
        implies p.attrs == q.attrs by {
        assert(proposal_recorded(s_, c, p));
        assert(proposal_recorded(s_, c, q));
        assert(p.src == q.src);
        if s.network.contains(p) && s.network.contains(q) {
            assert(p.attrs == q.attrs);
        }
        match a {
            Action::Submit { node, value } => {},
            Action::PreAccept { packet } => {},
            Action::FinishPreAccept { node, id, batch } => {},
            Action::Accept { packet } => {},
            Action::FinishAccept { node, id, ballot, batch } => {},
            Action::Learn { packet } => {},
            Action::BeginRecovery { node, id, ballot } => {},
            Action::Recover { packet } => {},
            Action::FinishRecovery { node, id, ballot, batch, selected } => {},
            Action::Validate { packet } => {},
            Action::FinishValidation { node, id, ballot, batch } => {},
            Action::ResolveWaiting { node, id, ballot, resolution } => {},
            Action::Execute { node, component } => {},
            Action::Reboot { node } => {},
            Action::Stutter => {},
        }
    }
}

pub proof fn lemma_behavior_coordinator(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures coordinator_invariant(states[i], c), same_ballot_agreement(states[i])
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_coordinator(states[0], c);
    } else {
        lemma_behavior_coordinator(states, c, i - 1);
        lemma_behavior_bounds(states, c, i - 1);
        lemma_behavior_references(states, c, i - 1);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_coordinator(states[i - 1], states[i], c, a);
    }
}

} // verus!
