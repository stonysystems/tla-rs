use super::types::*;
use super::model::*;
use super::recovery::*;
use super::execution::*;
use vstd::prelude::*;

verus! {

pub enum Action {
    Submit { node: int, value: int },
    PreAccept { packet: Packet },
    FinishPreAccept { node: int, id: Instance, batch: Map<int, Packet> },
    Accept { packet: Packet },
    FinishAccept { node: int, id: Instance, ballot: int, batch: Map<int, Packet> },
    Learn { packet: Packet },
    BeginRecovery { node: int, id: Instance, ballot: int },
    Recover { packet: Packet },
    FinishRecovery { node: int, id: Instance, ballot: int, batch: Map<int, Packet>, selected: int },
    Validate { packet: Packet },
    FinishValidation { node: int, id: Instance, ballot: int, batch: Map<int, Packet> },
    ResolveWaiting { node: int, id: Instance, ballot: int, resolution: Resolution },
    Execute { node: int, component: Seq<Instance> },
    Reboot { node: int },
    Stutter,
}

#[verifier::opaque]
pub open spec fn step(s: State, s_: State, c: Constants, a: Action) -> bool {
    match a {
        Action::Submit { node, value } => submit(s, s_, c, node, value),
        Action::PreAccept { packet } => preaccept(s, s_, c, packet),
        Action::FinishPreAccept { node, id, batch } => finish_preaccept(s, s_, c, node, id, batch),
        Action::Accept { packet } => accept(s, s_, c, packet),
        Action::FinishAccept { node, id, ballot, batch } => finish_accept(s, s_, c, node, id, ballot, batch),
        Action::Learn { packet } => learn(s, s_, c, packet),
        Action::BeginRecovery { node, id, ballot } => begin_recovery(s, s_, c, node, id, ballot),
        Action::Recover { packet } => recover(s, s_, c, packet),
        Action::FinishRecovery { node, id, ballot, batch, selected } =>
            finish_recovery(s, s_, c, node, id, ballot, batch, selected),
        Action::Validate { packet } => validate(s, s_, c, packet),
        Action::FinishValidation { node, id, ballot, batch } =>
            finish_validation(s, s_, c, node, id, ballot, batch),
        Action::ResolveWaiting { node, id, ballot, resolution } =>
            resolve_waiting(s, s_, c, node, id, ballot, resolution),
        Action::Execute { node, component } => execute(s, s_, c, node, component),
        Action::Reboot { node } => reboot(s, s_, c, node),
        Action::Stutter => s_ == s,
    }
}

#[verifier::opaque]
pub open spec fn next(s: State, s_: State, c: Constants) -> bool {
    exists |a: Action| #[trigger] step(s, s_, c, a)
}

#[verifier::opaque]
pub open spec fn behavior(states: Seq<State>, c: Constants) -> bool {
    &&& states.len() > 0
    &&& init(states[0], c)
    &&& forall |i: int| 0 <= i < states.len() - 1 ==> #[trigger] next(states[i], states[i + 1], c)
}

pub proof fn lemma_behavior_step(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len() - 1
    ensures next(states[i], states[i + 1], c)
{
    reveal(behavior);
}

} // verus!
