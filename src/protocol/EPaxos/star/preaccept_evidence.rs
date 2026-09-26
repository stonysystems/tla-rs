use super::types::*;
use super::model::*;
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

pub open spec fn preaccept_recorded(s: State, node: int, id: Instance, attrs: Attributes) -> bool {
    exists |p: Packet| #[trigger] s.network.contains(p) && p.kind is PreAcceptOk
        && p.src == node && p.instance == id && p.attrs == attrs
}

#[verifier::opaque]
pub open spec fn preaccept_evidence(s: State, c: Constants) -> bool {
    &&& forall |node: int, id: Instance| member(c, node) && (#[trigger] record(s.nodes[node], id)).phase is PreAccepted
        ==> preaccept_recorded(s, node, id, record(s.nodes[node], id).attrs)
    &&& forall |p: Packet| #[trigger] s.network.contains(p) && p.kind is RecoverOk
        && p.snapshot.phase is PreAccepted ==> preaccept_recorded(s, p.src, p.instance, p.snapshot.attrs)
    &&& forall |p: Packet, q: Packet| #![trigger s.network.contains(p), s.network.contains(q)]
        s.network.contains(p) && s.network.contains(q) && p.kind is RecoverOk && q.kind is PreAcceptOk
        && p.src == q.src && p.instance == q.instance ==> {
            stable(p.snapshot) || (p.snapshot.phase is PreAccepted && p.snapshot.attrs == q.attrs)
        }
}

pub proof fn lemma_initial_preaccept_evidence(s: State, c: Constants)
    requires init(s, c)
    ensures preaccept_evidence(s, c)
{
    reveal(preaccept_evidence);
}

pub proof fn lemma_step_preaccept_evidence(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        coordinator_invariant(s, c), same_ballot_agreement(s), validity(s, c), knowledge(s, c),
        evidence(s, c), preaccept_evidence(s, c), step(s, s_, c, a)
    ensures preaccept_evidence(s_, c)
{
    broadcast use group_set_lib_default;
    lemma_step_progress(s, s_, c, a);
    reveal(step);
    if let Action::Submit { node, value } = a {
        lemma_submission_fresh(s, c, node);
    }
    reveal(references_known);
    reveal(validity);
    reveal(knowledge);
    reveal(evidence);
    reveal(preaccept_evidence);
    assert forall |node: int, id: Instance| member(c, node) && (#[trigger] record(s_.nodes[node], id)).phase is PreAccepted
        implies preaccept_recorded(s_, node, id, record(s_.nodes[node], id).attrs) by {
        if record(s.nodes[node], id).phase is PreAccepted {
            assert(s.nodes[node].log.dom().contains(id));
            assert(record_valid(record(s.nodes[node], id), s.submitted[id]));
            assert(preaccept_recorded(s, node, id, record(s.nodes[node], id).attrs));
        }
        match a {
            Action::Submit { node: actor, value } => {
                if node == actor && id == (Instance { owner: actor, slot: s.nodes[actor].next_slot }) {
                    let p = packet(Kind::PreAcceptOk, actor, actor, id, 0, record(s_.nodes[actor], id).attrs);
                    assert(s_.network.contains(p));
                }
            },
            Action::PreAccept { packet: request } => {
                if node == request.dst && id == request.instance {
                    let p = packet(Kind::PreAcceptOk, node, request.src, id, 0, record(s_.nodes[node], id).attrs);
                    assert(s_.network.contains(p));
                }
            },
            _ => {},
        }
    }
    assert forall |p: Packet| #[trigger] s_.network.contains(p) && p.kind is RecoverOk
        && p.snapshot.phase is PreAccepted implies preaccept_recorded(s_, p.src, p.instance, p.snapshot.attrs) by {
        if s.network.contains(p) {
            assert(preaccept_recorded(s, p.src, p.instance, p.snapshot.attrs));
        }
    }
    assert forall |p: Packet, q: Packet| #![trigger s_.network.contains(p), s_.network.contains(q)] s_.network.contains(p) && s_.network.contains(q)
        && p.kind is RecoverOk && q.kind is PreAcceptOk && p.src == q.src && p.instance == q.instance implies {
            stable(p.snapshot) || (p.snapshot.phase is PreAccepted && p.snapshot.attrs == q.attrs)
        } by {
        if s.network.contains(p) {
            assert(snapshot_evidence(s, p));
        }
        if s.network.contains(q) {
            assert(recorded_knowledge(s, q));
        }
    }
}

pub proof fn lemma_behavior_preaccept_evidence(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures preaccept_evidence(states[i], c)
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_preaccept_evidence(states[0], c);
    } else {
        lemma_behavior_preaccept_evidence(states, c, i - 1);
        lemma_behavior_bounds(states, c, i - 1);
        lemma_behavior_references(states, c, i - 1);
        lemma_behavior_coordinator(states, c, i - 1);
        lemma_behavior_validity(states, c, i - 1);
        lemma_behavior_knowledge(states, c, i - 1);
        lemma_behavior_evidence(states, c, i - 1);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_preaccept_evidence(states[i - 1], states[i], c, a);
    }
}

} // verus!
