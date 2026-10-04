//! Literal normal-case read-one/write-all model from Om Section 3.
//! Two replicas, one write of 1, and two reads. All leases remain valid in the
//! same configuration. No read blocking on pending writes is specified here.
//! This exposes an omitted rule in the paper model, not an implementation audit.
use vstd::prelude::*;
verus! {
pub struct State {
    pub phase: int, // 0 idle, 1 prepare, 2 commit sent, 3 writer replied
    pub prepared: Set<int>, pub applied: Set<int>,
    pub calls: Map<int, int>, pub returns: Map<int, int>, pub replies: Map<int, int>,
    pub time: int,
}
pub enum Action { Write, Prepare { node: int }, SendCommit, Apply { node: int },
    WriteReply, Read { id: int }, ReadReply { id: int, node: int } }
pub open spec fn init() -> State {
    State { phase: 0, prepared: Set::empty(), applied: Set::empty(), calls: Map::empty(),
        returns: Map::empty(), replies: Map::empty(), time: 0 }
}
pub open spec fn next(s: State, t: State, a: Action) -> bool {
    match a {
        Action::Write => s.phase == 0 && t == State { phase: 1, time: s.time + 1,
            calls: s.calls.insert(0, s.time), ..s },
        Action::Prepare { node } => s.phase == 1 && 0 <= node < 2
            && t == State { prepared: s.prepared.insert(node), time: s.time + 1, ..s },
        Action::SendCommit => s.phase == 1 && s.prepared.contains(0) && s.prepared.contains(1)
            && t == State { phase: 2, time: s.time + 1, ..s },
        Action::Apply { node } => s.phase == 2 && 0 <= node < 2
            && t == State { applied: s.applied.insert(node), time: s.time + 1, ..s },
        Action::WriteReply => s.phase == 2 && s.applied.contains(0) && s.applied.contains(1)
            && t == State { phase: 3, time: s.time + 1, returns: s.returns.insert(0, s.time),
                replies: s.replies.insert(0, 1), ..s },
        Action::Read { id } => 1 <= id <= 2 && !s.calls.dom().contains(id)
            && t == State { calls: s.calls.insert(id, s.time), time: s.time + 1, ..s },
        Action::ReadReply { id, node } => 1 <= id <= 2 && 0 <= node < 2
            && s.calls.dom().contains(id) && !s.returns.dom().contains(id)
            && t == State { returns: s.returns.insert(id, s.time),
                replies: s.replies.insert(id, if s.applied.contains(node) { 1int } else { 0int }),
                time: s.time + 1, ..s },
    }
}
// The only state-changing operation is write ID 0. Any legal sequential order
// must return 0 on reads before it and 1 on reads after it.
pub open spec fn linearization(s: State, positions: Map<int, int>) -> bool {
    &&& positions.dom() == set![0int, 1int, 2int]
    &&& forall|i: int| 0 <= i <= 2 ==> 0 <= #[trigger] positions[i] <= 2
    &&& forall|i: int, j: int| 0 <= i <= 2 && 0 <= j <= 2 && i != j ==> #[trigger] positions[i] != #[trigger] positions[j]
    &&& forall|i: int, j: int| 0 <= i <= 2 && 0 <= j <= 2
        && s.returns[i] < s.calls[j] ==> #[trigger] positions[i] < #[trigger] positions[j]
    &&& forall|i: int| 1 <= i <= 2 ==> #[trigger] s.replies[i] == (if positions[0] < positions[i] { 1int } else { 0int })
}
pub proof fn new_old_inversion_has_no_linearization(s: State)
    requires s.replies[1] == 1, s.replies[2] == 0, s.returns[1] < s.calls[2],
    ensures !exists|positions: Map<int, int>| linearization(s, positions),
{
    assert forall|p: Map<int, int>| !linearization(s, p) by {
        if linearization(s, p) {
            assert(p[0] < p[1]); assert(p[1] < p[2]); assert(p[2] < p[0]);
        }
    }
}
pub proof fn reachable_new_old_inversion()
    ensures exists|states: Seq<State>, actions: Seq<Action>| #![trigger states.len(), actions.len()]
        states.len() == actions.len() + 1 && states[0] == init()
        && (forall|k: int| 0 <= k < actions.len() ==> #[trigger] next(states[k], states[k + 1], actions[k]))
        && states.last().phase == 3 && states.last().returns.dom() == set![0int, 1int, 2int]
        && !exists|positions: Map<int, int>| linearization(states.last(), positions),
{
    let s0 = init();
    let s1 = State { phase: 1, calls: s0.calls.insert(0, 0), time: 1, ..s0 };
    let s2 = State { prepared: set![0int], time: 2, ..s1 };
    let s3 = State { prepared: set![0int, 1int], time: 3, ..s2 };
    let s4 = State { phase: 2, time: 4, ..s3 };
    let s5 = State { applied: set![0int], time: 5, ..s4 };
    let s6 = State { calls: s5.calls.insert(1, 5), time: 6, ..s5 };
    let s7 = State { returns: s6.returns.insert(1, 6), replies: s6.replies.insert(1, 1), time: 7, ..s6 };
    let s8 = State { calls: s7.calls.insert(2, 7), time: 8, ..s7 };
    let s9 = State { returns: s8.returns.insert(2, 8), replies: s8.replies.insert(2, 0), time: 9, ..s8 };
    let s10 = State { applied: set![0int, 1int], time: 10, ..s9 };
    let s11 = State { phase: 3, returns: s10.returns.insert(0, 10), replies: s10.replies.insert(0, 1), time: 11, ..s10 };
    let states = seq![s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11];
    let actions = seq![Action::Write, Action::Prepare { node: 0 }, Action::Prepare { node: 1 },
        Action::SendCommit, Action::Apply { node: 0 }, Action::Read { id: 1 },
        Action::ReadReply { id: 1, node: 0 }, Action::Read { id: 2 }, Action::ReadReply { id: 2, node: 1 },
        Action::Apply { node: 1 }, Action::WriteReply];
    assert forall|k: int| 0 <= k < actions.len() implies #[trigger] next(states[k], states[k + 1], actions[k]) by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {}
        else if k == 5 {} else if k == 6 {} else if k == 7 {} else if k == 8 {} else if k == 9 {} else {}
    }
    assert(s11.returns.dom() =~= set![0int, 1int, 2int]);
    new_old_inversion_has_no_linearization(s11);
    assert(states.last() == s11);
    assert(states.len() == actions.len() + 1 && states[0] == init()
        && (forall|k: int| 0 <= k < actions.len() ==> #[trigger] next(states[k], states[k + 1], actions[k]))
        && states.last().phase == 3 && states.last().returns.dom() == set![0int, 1int, 2int]
        && !exists|p: Map<int, int>| linearization(states.last(), p));
}
} // verus!
