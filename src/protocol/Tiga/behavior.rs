use super::types::*;
use super::normal::*;
use super::recovery::*;
use vstd::prelude::*;

verus! {

pub enum Action {
    Submit { id: int, txn: Txn, ts: int },
    Tick { node: int, time: int },
    Receive { p: Packet },
    Release { node: int, id: int },
    Agree { node: int, id: int, replies: Map<int, Packet>, ts: int },
    Sync { p: Packet },
    Complete { id: int, leaders: Map<int, Packet>, votes: Map<int, Map<int, Packet>>, ts: int },
    NewView { views: Seq<nat> },
    EnterView { p: Packet, pending: Seq<Entry> },
    Rebuild { node: int, replies: Map<int, Packet>, selected: int, log: Seq<Entry> },
    Install { node: int, replies: Map<int, Packet>, log: Seq<Entry> },
    Start { p: Packet },
    Crash { node: int },
    Stutter,
}

#[verifier::opaque]
pub open spec fn enabled(s: State, c: Constants, a: Action) -> bool {
    match a {
        Action::Submit { id, txn, ts } => can_submit(s, c, id, txn, ts),
        Action::Tick { node, time } => member(c, node) && !(s.nodes[node].status is Down) && time >= s.nodes[node].clock,
        Action::Receive { p } => can_receive(s, c, p),
        Action::Release { node, id } => can_release(s, c, node, id),
        Action::Agree { node, id, replies, ts } => can_agree(s, c, node, id, replies, ts),
        Action::Sync { p } => can_sync(s, c, p),
        Action::Complete { id, leaders, votes, ts } => can_complete(s, c, id, leaders, votes, ts),
        Action::NewView { views } => can_new_view(s, c, views),
        Action::EnterView { p, pending } => can_enter_view(s, c, p, pending),
        Action::Rebuild { node, replies, selected, log } => can_rebuild(s, c, node, replies, selected, log),
        Action::Install { node, replies, log } => can_install(s, c, node, replies, log),
        Action::Start { p } => can_start(s, c, p),
        Action::Crash { node } => member(c, node) && !(s.nodes[node].status is Down)
            && shard_members(c, shard(c, node)).filter(|n: int| s.nodes[n].status is Down).len() < c.f,
        Action::Stutter => true,
    }
}

#[verifier::opaque]
pub open spec fn apply(s: State, c: Constants, a: Action) -> State {
    let after = match a {
        Action::Submit { id, txn, ts } => submit(s, c, id, txn, ts),
        Action::Tick { node, time } => replace(s, node, Replica { clock: time, ..s.nodes[node] }, Set::empty()),
        Action::Receive { p } => receive(s, c, p),
        Action::Release { node, id } => release(s, c, node, id),
        Action::Agree { node, id, replies, ts } => agree(s, c, node, id, ts),
        Action::Sync { p } => sync(s, c, p),
        Action::Complete { id, leaders, votes, ts } => complete(s, id, leaders, ts),
        Action::NewView { views } => new_view(s, c, views),
        Action::EnterView { p, pending } => enter_view(s, c, p, pending),
        Action::Rebuild { node, replies, selected, log } => rebuild(s, c, node, log),
        Action::Install { node, replies, log } => install(s, c, node, log),
        Action::Start { p } => start(s, c, p),
        Action::Crash { node } => replace(s, node, Replica { status: Status::Down, ..s.nodes[node] }, Set::empty()),
        Action::Stutter => s,
    };
    State { tick: s.tick + 1, ..after }
}

#[verifier::opaque]
pub open spec fn next(s: State, s_: State, c: Constants) -> bool {
    exists |a: Action| enabled(s, c, a) && s_ == apply(s, c, a)
}

#[verifier::opaque]
pub open spec fn behavior(states: Seq<State>, c: Constants) -> bool {
    &&& valid_constants(c)
    &&& states.len() > 0
    &&& states[0] == initial(c)
    &&& forall |i: int| 0 <= i < states.len() - 1 ==> #[trigger] next(states[i], states[i + 1], c)
}

pub proof fn lemma_initial(c: Constants)
    requires valid_constants(c)
    ensures behavior(seq![initial(c)], c)
{
    reveal(behavior);
}

pub proof fn lemma_extend(states: Seq<State>, c: Constants, a: Action) -> (after: Seq<State>)
    requires behavior(states, c), enabled(states.last(), c, a)
    ensures behavior(after, c), after == states.push(apply(states.last(), c, a))
{
    reveal(behavior);
    reveal(next);
    let s_ = apply(states.last(), c, a);
    assert(next(states.last(), s_, c));
    let after = states.push(s_);
    assert forall |i: int| 0 <= i < after.len() - 1 implies #[trigger] next(after[i], after[i + 1], c) by {
        if i < states.len() - 1 { assert(next(states[i], states[i + 1], c)); }
    }
    after
}

} // verus!
