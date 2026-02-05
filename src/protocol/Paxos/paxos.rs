use crate::protocol::Paxos::types::*;
use vstd::prelude::*;

verus! {
    /// Initialize the Paxos protocol state
    /// All sets start empty, no messages sent
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.max_bal == Set::<int>::empty()
        &&& s.max_v_bal == Set::<int>::empty()
        &&& s.max_val == Set::<int>::empty()
        &&& s.msg_count == 0int
    }

    /// Phase 1a: Proposer sends a prepare request with ballot b
    /// Only the message count changes; acceptor state is unchanged
    pub open spec fn LSend1a(s: LState, s_: LState, c: LConstants, b: int) -> bool {
        &&& s_.max_bal == s.max_bal
        &&& s_.max_v_bal == s.max_v_bal
        &&& s_.max_val == s.max_val
        &&& s_.msg_count == s.msg_count + 1
    }

    /// Phase 1b: Acceptor responds to a prepare request
    /// The acceptor promises not to accept any ballot less than b
    /// by adding b to its max_bal set
    pub open spec fn LSend1b(s: LState, s_: LState, c: LConstants, b: int) -> bool {
        &&& s_.max_bal == s.max_bal.insert(b)
        &&& s_.max_v_bal == s.max_v_bal
        &&& s_.max_val == s.max_val
        &&& s_.msg_count == s.msg_count + 1
    }

    /// Phase 2a: Proposer sends an accept request with ballot b and value v
    /// Only the message count changes; acceptor state is unchanged
    pub open spec fn LSend2a(s: LState, s_: LState, c: LConstants, b: int, v: int) -> bool {
        &&& s_.max_bal == s.max_bal
        &&& s_.max_v_bal == s.max_v_bal
        &&& s_.max_val == s.max_val
        &&& s_.msg_count == s.msg_count + 1
    }

    /// Phase 2b: Acceptor accepts ballot b with value v
    /// Updates the voted ballot set and accepted value set
    pub open spec fn LSend2b(s: LState, s_: LState, c: LConstants, b: int, v: int) -> bool {
        &&& s_.max_bal == s.max_bal
        &&& s_.max_v_bal == s.max_v_bal.insert(b)
        &&& s_.max_val == s.max_val.insert(v)
        &&& s_.msg_count == s.msg_count + 1
    }

    /// Safety predicate: a value v is chosen if it is in max_val
    pub open spec fn LChosen(s: LState, v: int) -> bool {
        s.max_val.contains(v)
    }

    /// Next-state relation: disjunction of all possible transitions
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        ||| exists |b: int| LSend1a(s, s_, c, b)
        ||| exists |b: int| LSend1b(s, s_, c, b)
        ||| exists |b: int, v: int| LSend2a(s, s_, c, b, v)
        ||| exists |b: int, v: int| LSend2b(s, s_, c, b, v)
    }
}
