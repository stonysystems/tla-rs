use super::types::*;
use super::model::*;
use super::behavior::*;
use super::invariants::*;
use super::identities::*;
use vstd::prelude::*;

verus! {

pub open spec fn progress(s: State, s_: State, c: Constants) -> bool {
    &&& s_.nodes.len() == s.nodes.len()
    &&& s.network.subset_of(s_.network)
    &&& s.submitted.dom().subset_of(s_.submitted.dom())
    &&& forall |id: Instance| #[trigger] s.submitted.dom().contains(id)
        ==> s_.submitted[id] == s.submitted[id]
    &&& forall |node: int| member(c, node) ==> {
        &&& #[trigger] s_.nodes[node].next_slot >= s.nodes[node].next_slot
        &&& s.nodes[node].executed.is_prefix_of(s_.nodes[node].executed)
    }
    &&& forall |node: int, id: Instance| member(c, node) ==> {
        let before = record(s.nodes[node], id);
        let after = #[trigger] record(s_.nodes[node], id);
        &&& after.promise >= before.promise
        &&& after.accepted_ballot >= before.accepted_ballot
        &&& stable(before) ==> stable(after)
    }
}

pub proof fn lemma_step_progress(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        step(s, s_, c, a)
    ensures progress(s, s_, c)
{
    reveal(step);
    if let Action::Submit { node, value } = a {
        lemma_submission_fresh(s, c, node);
    }
    assert forall |node: int, id: Instance| member(c, node) implies {
        let before = record(s.nodes[node], id);
        let after = #[trigger] record(s_.nodes[node], id);
        &&& after.promise >= before.promise
        &&& after.accepted_ballot >= before.accepted_ballot
        &&& stable(before) ==> stable(after)
    } by {
        assert(record_bounds(record(s.nodes[node], id)));
        match a {
            Action::Submit { node: actor, value } => {},
            Action::PreAccept { packet } => {},
            Action::FinishPreAccept { node: actor, id: target, batch } => {},
            Action::Accept { packet } => {},
            Action::FinishAccept { node: actor, id: target, ballot, batch } => {},
            Action::Learn { packet } => {},
            Action::BeginRecovery { node: actor, id: target, ballot } => {},
            Action::Recover { packet } => {},
            Action::FinishRecovery { node: actor, id: target, ballot, batch, selected } => {},
            Action::Validate { packet } => {},
            Action::FinishValidation { node: actor, id: target, ballot, batch } => {},
            Action::ResolveWaiting { node: actor, id: target, ballot, resolution } => {},
            Action::Execute { node: actor, component } => {},
            Action::Reboot { node: actor } => {},
            Action::Stutter => {},
        }
    }
}

pub proof fn lemma_behavior_step_progress(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len() - 1
    ensures progress(states[i], states[i + 1], c)
{
    reveal(behavior);
    lemma_behavior_bounds(states, c, i);
    lemma_behavior_references(states, c, i);
    lemma_behavior_step(states, c, i);
    reveal(next);
    let a = choose |a: Action| #[trigger] step(states[i], states[i + 1], c, a);
    lemma_step_progress(states[i], states[i + 1], c, a);
}

} // verus!
