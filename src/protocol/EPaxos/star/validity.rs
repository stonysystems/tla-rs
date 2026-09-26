use super::types::*;
use super::model::*;
use super::behavior::*;
use super::invariants::*;
use super::identities::*;
use super::coordinator::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn payload_valid(p: Payload, original: Attributes) -> bool {
    p is Unknown || p is Nop || p == original.payload
}

pub open spec fn record_valid(r: Record, original: Attributes) -> bool {
    &&& payload_valid(r.attrs.payload, original)
    &&& r.original is Unknown || r.original == original.payload
    &&& !(r.original is Unknown) ==> r.initial_deps == original.deps
    &&& stable(r) ==> !(r.attrs.payload is Unknown)
    &&& r.phase is PreAccepted ==> r.attrs.payload == original.payload && r.original == original.payload
}

#[verifier::opaque]
pub open spec fn validity(s: State, c: Constants) -> bool {
    &&& forall |id: Instance| #[trigger] s.submitted.dom().contains(id)
        ==> s.submitted[id].payload is Command
    &&& forall |node: int, id: Instance| member(c, node) && #[trigger] s.nodes[node].log.dom().contains(id)
        ==> record_valid(s.nodes[node].log[id], s.submitted[id])
    &&& forall |node: int, id: Instance| member(c, node) && #[trigger] s.nodes[node].attempts.dom().contains(id) ==> {
        let a = s.nodes[node].attempts[id];
        &&& payload_valid(a.candidate.payload, s.submitted[id])
        &&& (a.stage is Initial || a.stage is Validating || a.stage is Waiting) ==> a.candidate == s.submitted[id]
        &&& final_stage(a.stage) ==> !(a.candidate.payload is Unknown)
    }
    &&& forall |p: Packet| #[trigger] s.network.contains(p) ==> {
        &&& payload_valid(p.attrs.payload, s.submitted[p.instance])
        &&& record_valid(p.snapshot, s.submitted[p.instance])
        &&& (p.kind is PreAccept || p.kind is Validate || p.kind is Waiting) ==> p.attrs == s.submitted[p.instance]
        &&& p.kind is PreAcceptOk ==> p.attrs.payload == s.submitted[p.instance].payload
            && s.submitted[p.instance].deps.subset_of(p.attrs.deps)
        &&& proposal(p) ==> !(p.attrs.payload is Unknown)
    }
}

pub proof fn lemma_initial_validity(s: State, c: Constants)
    requires init(s, c)
    ensures validity(s, c)
{
    reveal(validity);
}

pub proof fn lemma_step_validity(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), references_known(s, c), allocated(s, c), validity(s, c),
        step(s, s_, c, a)
    ensures validity(s_, c)
{
    broadcast use group_set_lib_default;
    reveal(step);
    if let Action::Submit { node, value } = a {
        lemma_submission_fresh(s, c, node);
    }
    reveal(references_known);
    reveal(validity);
    assert forall |node: int, id: Instance| member(c, node) && #[trigger] s_.nodes[node].log.dom().contains(id)
        implies record_valid(s_.nodes[node].log[id], s_.submitted[id]) by {
        if s.nodes[node].log.dom().contains(id) {
            assert(record_valid(s.nodes[node].log[id], s.submitted[id]));
        } else {
            assert(record(s.nodes[node], id) == empty_record());
        }
    }
    assert forall |node: int, id: Instance| member(c, node) && #[trigger] s_.nodes[node].attempts.dom().contains(id) implies {
        let a = s_.nodes[node].attempts[id];
        &&& payload_valid(a.candidate.payload, s_.submitted[id])
        &&& (a.stage is Initial || a.stage is Validating || a.stage is Waiting) ==> a.candidate == s_.submitted[id]
        &&& final_stage(a.stage) ==> !(a.candidate.payload is Unknown)
    } by {
        if s.nodes[node].attempts.dom().contains(id) {
            assert(payload_valid(s.nodes[node].attempts[id].candidate.payload, s.submitted[id]));
        }
    }
    assert forall |p: Packet| #[trigger] s_.network.contains(p) implies {
        &&& payload_valid(p.attrs.payload, s_.submitted[p.instance])
        &&& record_valid(p.snapshot, s_.submitted[p.instance])
        &&& (p.kind is PreAccept || p.kind is Validate || p.kind is Waiting) ==> p.attrs == s_.submitted[p.instance]
        &&& p.kind is PreAcceptOk ==> p.attrs.payload == s_.submitted[p.instance].payload
            && s_.submitted[p.instance].deps.subset_of(p.attrs.deps)
        &&& proposal(p) ==> !(p.attrs.payload is Unknown)
    } by {
        if s.network.contains(p) {
            assert(payload_valid(p.attrs.payload, s.submitted[p.instance]));
        }
    }
}

pub proof fn lemma_behavior_validity(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures validity(states[i], c)
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_validity(states[0], c);
    } else {
        lemma_behavior_validity(states, c, i - 1);
        lemma_behavior_references(states, c, i - 1);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_validity(states[i - 1], states[i], c, a);
    }
}

} // verus!
