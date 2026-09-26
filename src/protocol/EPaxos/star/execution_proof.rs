use super::types::*;
use super::model::*;
use super::execution::*;
use super::behavior::*;
use super::identities::*;
use super::validity::*;
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

pub open spec fn at_most_once(s: State, c: Constants) -> bool {
    forall |node: int| member(c, node) ==> #[trigger] s.nodes[node].executed.no_duplicates()
}

pub proof fn lemma_initial_at_most_once(s: State, c: Constants)
    requires init(s, c)
    ensures at_most_once(s, c)
{
}

pub proof fn lemma_execute_at_most_once(s: State, s_: State, c: Constants,
    node: int, component: Seq<Instance>)
    requires at_most_once(s, c), execute(s, s_, c, node, component)
    ensures at_most_once(s_, c)
{
    let before = s.nodes[node].executed;
    let after = before + component;
    assert(before.no_duplicates());
    assert forall |i: int, j: int| 0 <= i < j < after.len() implies after[i] != after[j] by {
        if j < before.len() {
            assert(before[i] != before[j]);
        } else if i >= before.len() {
            assert(component[i - before.len()] != component[j - before.len()]);
        } else {
            assert(!before.contains(component[j - before.len()]));
        }
    }
    assert(after.no_duplicates());
}

pub proof fn lemma_step_at_most_once(s: State, s_: State, c: Constants, a: Action)
    requires at_most_once(s, c), step(s, s_, c, a)
    ensures at_most_once(s_, c)
{
    reveal(step);
    if let Action::Execute { node, component } = a {
        lemma_execute_at_most_once(s, s_, c, node, component);
    }
}

pub proof fn lemma_behavior_at_most_once(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures at_most_once(states[i], c)
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_at_most_once(states[0], c);
    } else {
        lemma_behavior_at_most_once(states, c, i - 1);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_at_most_once(states[i - 1], states[i], c, a);
    }
}

/// No-op records participate in graph execution but produce no application
/// operation. Every non-no-op component member has its submitted payload.
pub proof fn lemma_execution_validity(s: State, s_: State, c: Constants,
    node: int, component: Seq<Instance>, i: int)
    requires references_known(s, c), validity(s, c), execute(s, s_, c, node, component),
        0 <= i < component.len()
    ensures
        s.submitted.dom().contains(component[i]),
        record(s.nodes[node], component[i]).phase is Committed,
        record(s.nodes[node], component[i]).attrs.payload is Nop
            || record(s.nodes[node], component[i]).attrs.payload == s.submitted[component[i]].payload,
{
    reveal(references_known);
    reveal(validity);
}

} // verus!
