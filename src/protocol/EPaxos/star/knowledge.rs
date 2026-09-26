//! Durable command knowledge and the dependency edge between two local
//! pre-acceptances of conflicting commands.
use super::types::*;
use super::model::*;
use super::behavior::*;
use super::invariants::*;
use super::identities::*;
use super::validity::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn recorded_knowledge(s: State, p: Packet) -> bool {
    let r = record(s.nodes[p.src], p.instance);
    &&& !(r.attrs.payload is Unknown)
    &&& r.original == s.submitted[p.instance].payload
    &&& r.initial_deps == s.submitted[p.instance].deps
    &&& p.kind is PreAcceptOk ==> (r.phase is PreAccepted || stable(r))
    &&& (p.kind is PreAcceptOk && r.phase is PreAccepted) ==> r.attrs == p.attrs
}

pub open spec fn covers(a: Instance, attrs_a: Attributes, b: Instance, attrs_b: Attributes) -> bool {
    attrs_a.deps.contains(b) || attrs_b.deps.contains(a)
}

#[verifier::opaque]
pub open spec fn knowledge(s: State, c: Constants) -> bool {
    &&& forall |p: Packet| #[trigger] s.network.contains(p)
        && (p.kind is PreAcceptOk || p.kind is ValidateOk) ==> recorded_knowledge(s, p)
    &&& forall |p: Packet, q: Packet| #![trigger s.network.contains(p), s.network.contains(q)]
        s.network.contains(p) && s.network.contains(q)
        && p.kind is PreAcceptOk && q.kind is PreAcceptOk && p.src == q.src
        && p.instance != q.instance && conflicts(c, p.attrs.payload, q.attrs.payload)
        ==> covers(p.instance, p.attrs, q.instance, q.attrs)
    &&& forall |p: Packet, q: Packet| #![trigger s.network.contains(p), s.network.contains(q)]
        s.network.contains(p) && s.network.contains(q)
        && p.kind is PreAcceptOk && q.kind is PreAcceptOk && p.src == q.src && p.instance == q.instance
        ==> p == q
}

pub proof fn lemma_initial_knowledge(s: State, c: Constants)
    requires init(s, c)
    ensures knowledge(s, c)
{
    reveal(knowledge);
}

pub proof fn lemma_step_knowledge(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        validity(s, c), knowledge(s, c), step(s, s_, c, a)
    ensures knowledge(s_, c)
{
    broadcast use group_set_lib_default;
    reveal(step);
    if let Action::Submit { node, value } = a {
        lemma_submission_fresh(s, c, node);
    }
    lemma_step_validity(s, s_, c, a);
    reveal(references_known);
    reveal(validity);
    reveal(knowledge);
    assert forall |p: Packet| #[trigger] s_.network.contains(p)
        && (p.kind is PreAcceptOk || p.kind is ValidateOk) implies recorded_knowledge(s_, p) by {
        if s.network.contains(p) {
            assert(recorded_knowledge(s, p));
        }
    }
    assert forall |p: Packet, q: Packet| #![trigger covers(p.instance, p.attrs, q.instance, q.attrs)] s_.network.contains(p) && s_.network.contains(q)
        && p.kind is PreAcceptOk && q.kind is PreAcceptOk && p.src == q.src
        && p.instance != q.instance && conflicts(c, p.attrs.payload, q.attrs.payload)
        implies covers(p.instance, p.attrs, q.instance, q.attrs) by {
        if s.network.contains(p) {
            assert(recorded_knowledge(s, p));
        }
        if s.network.contains(q) {
            assert(recorded_knowledge(s, q));
        }
    }
    assert forall |p: Packet, q: Packet| #![trigger s_.network.contains(p), s_.network.contains(q)] s_.network.contains(p) && s_.network.contains(q)
        && p.kind is PreAcceptOk && q.kind is PreAcceptOk && p.src == q.src && p.instance == q.instance
        implies p == q by {
        if s.network.contains(p) {
            assert(recorded_knowledge(s, p));
        }
        if s.network.contains(q) {
            assert(recorded_knowledge(s, q));
        }
    }
}

pub proof fn lemma_behavior_knowledge(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures knowledge(states[i], c)
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_knowledge(states[0], c);
    } else {
        lemma_behavior_knowledge(states, c, i - 1);
        lemma_behavior_bounds(states, c, i - 1);
        lemma_behavior_references(states, c, i - 1);
        lemma_behavior_validity(states, c, i - 1);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_knowledge(states[i - 1], states[i], c, a);
    }
}

} // verus!
