use vstd::prelude::*;
use super::vc::*;
use super::types::*;
use super::model::*;

verus! {

pub enum Action {
    Write { client: int, server: int, key: int, value: int, gvc: VC },
    Propagate { src: int, mid: Server, after: Server },
    Read { client: int, server: int, key: int, after: Server, result: Entry },
    Start { client: int },
    Fork { parent: int, child: int },
    Stutter,
}

#[verifier::opaque]
pub open spec fn step(c: Constants, s: State, s2: State, a: Action) -> bool {
    match a {
        Action::Write { client, server, key, value, gvc } => client_write(c, s, s2, client, server, key, value, gvc),
        Action::Propagate { src, mid, after } => propagate(c, s, s2, src, mid, after),
        Action::Read { client, server, key, after, result } => client_read(c, s, s2, client, server, key, after, result),
        Action::Start { client } => start_client(s, s2, client),
        Action::Fork { parent, child } => fork(s, s2, parent, child),
        Action::Stutter => s2 == s,
    }
}

#[verifier::opaque]
pub open spec fn next(c: Constants, s: State, s2: State) -> bool {
    exists|a: Action| #[trigger] step(c, s, s2, a)
}

#[verifier::opaque]
pub open spec fn behavior(c: Constants, states: Seq<State>) -> bool {
    &&& states.len() > 0
    &&& init(c, states[0])
    &&& forall|i: int| 0 <= i < states.len() - 1 ==> #[trigger] next(c, states[i], states[i + 1])
}

pub proof fn lemma_behavior_step(c: Constants, states: Seq<State>, i: int)
    requires behavior(c, states), 0 <= i < states.len() - 1
    ensures next(c, states[i], states[i + 1])
{
    reveal(behavior);
}

pub proof fn lemma_extend(c: Constants, states: Seq<State>, s2: State, a: Action) -> (after: Seq<State>)
    requires behavior(c, states), step(c, states.last(), s2, a)
    ensures behavior(c, after), after == states.push(s2)
{
    reveal(behavior);
    reveal(next);
    let after = states.push(s2);
    assert(next(c, states.last(), s2));
    assert forall|i: int| 0 <= i < after.len() - 1 implies #[trigger] next(c, after[i], after[i + 1]) by {
        if i < states.len() - 1 { assert(next(c, states[i], states[i + 1])); }
    }
    after
}

} // verus!
