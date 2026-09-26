use super::types::*;
use super::model::*;
use super::recovery::*;
use super::behavior::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn record_bounds(r: Record) -> bool {
    &&& 0 <= r.accepted_ballot <= r.promise
    &&& r.accepted_ballot > 0 ==> stable(r)
}

pub open spec fn bounds(s: State, c: Constants) -> bool {
    &&& s.nodes.len() == c.n
    &&& forall |node: int, id: Instance| member(c, node)
        ==> record_bounds(#[trigger] record(s.nodes[node], id))
}

pub proof fn lemma_initial_bounds(s: State, c: Constants)
    requires init(s, c)
    ensures bounds(s, c)
{
}

pub proof fn lemma_step_bounds(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), step(s, s_, c, a)
    ensures bounds(s_, c)
{
    reveal(step);
    assert forall |node: int, id: Instance| member(c, node)
        implies record_bounds(#[trigger] record(s_.nodes[node], id)) by {
        assert(record_bounds(record(s.nodes[node], id)));
        match a {
            Action::Submit { node: actor, value } => {},
            Action::PreAccept { packet: p } => {},
            Action::FinishPreAccept { node: actor, id: target, batch } => {},
            Action::Accept { packet: p } => {},
            Action::FinishAccept { node: actor, id: target, ballot, batch } => {},
            Action::Learn { packet: p } => {},
            Action::BeginRecovery { node: actor, id: target, ballot } => {},
            Action::Recover { packet: p } => {},
            Action::FinishRecovery { node: actor, id: target, ballot, batch, selected } => {},
            Action::Validate { packet: p } => {},
            Action::FinishValidation { node: actor, id: target, ballot, batch } => {},
            Action::ResolveWaiting { node: actor, id: target, ballot, resolution } => {},
            Action::Execute { node: actor, component } => {},
            Action::Reboot { node: actor } => {},
            Action::Stutter => {},
        }
    }
}

pub proof fn lemma_behavior_bounds(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures bounds(states[i], c)
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_bounds(states[0], c);
    } else {
        lemma_behavior_bounds(states, c, i - 1);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_bounds(states[i - 1], states[i], c, a);
    }
}

pub open spec fn durable_equal(s: State, s_: State) -> bool {
    &&& s.nodes.len() == s_.nodes.len()
    &&& s.network == s_.network
    &&& s.submitted == s_.submitted
    &&& forall |node: int| 0 <= node < s.nodes.len() ==> {
        &&& #[trigger] s.nodes[node].log == s_.nodes[node].log
        &&& s.nodes[node].next_slot == s_.nodes[node].next_slot
        &&& s.nodes[node].executed == s_.nodes[node].executed
    }
}

pub proof fn lemma_reboot_preserves_durable_state(s: State, s_: State, c: Constants, node: int)
    requires reboot(s, s_, c, node)
    ensures
        durable_equal(s, s_),
        s_.nodes[node].attempts == Map::<Instance, Attempt>::empty(),
        forall |id: Instance| !s_.nodes[node].attempts.dom().contains(id),
{
    assert(s.network.union(Set::empty()) =~= s.network);
}

pub proof fn lemma_reboot_requires_fresh_recovery(s: State, s_: State, after: State,
    c: Constants, node: int, id: Instance, b: int)
    requires reboot(s, s_, c, node), begin_recovery(s_, after, c, node, id, b)
    ensures b > record(s.nodes[node], id).promise,
        record(after.nodes[node], id).promise == b,
        record(after.nodes[node], id).accepted_ballot == record(s.nodes[node], id).accepted_ballot,
        record(after.nodes[node], id).attrs == record(s.nodes[node], id).attrs,
{
}

pub proof fn lemma_reboot_discards_active_attempts(s: State, s_: State, c: Constants, node: int)
    requires reboot(s, s_, c, node)
    ensures forall |id: Instance, b: int, stage: Stage| !active(s_, node, id, b, stage)
{
}

pub proof fn lemma_stable_record_rejects_validation(s: State, c: Constants, p: Packet, s_: State)
    requires stable(record(s.nodes[p.dst], p.instance))
    ensures !validate(s, s_, c, p)
{
}

pub proof fn lemma_reply_binding(s: State, c: Constants, node: int, id: Instance,
    b: int, kind: Kind, batch: Map<int, Packet>, sender: int)
    requires replies(s, c, node, id, b, kind, batch), batch.dom().contains(sender)
    ensures
        batch[sender].instance == id, batch[sender].ballot == b,
        batch[sender].src == sender, batch[sender].dst == node,
        batch[sender].kind == kind, s.network.contains(batch[sender]),
{
}

} // verus!
