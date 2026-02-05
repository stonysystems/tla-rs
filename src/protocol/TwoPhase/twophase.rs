use crate::protocol::TwoPhase::types::*;
use vstd::prelude::*;

verus! {
    /// Initialize the protocol state
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.rm_state == Set::<int>::empty()
        &&& s.tm_state is Init
        &&& s.tm_prepared == Set::<int>::empty()
    }

    /// Transaction Manager receives a Prepared message from resource manager r
    pub open spec fn LTMRcvPrepared(s: LState, s_: LState, c: LConstants, r: int) -> bool {
        &&& s.tm_state is Init
        &&& s_.tm_prepared == s.tm_prepared.insert(r)
        &&& s_.rm_state == s.rm_state
        &&& s_.tm_state is Init
    }

    /// Transaction Manager commits (requires all RMs prepared)
    pub open spec fn LTMCommit(s: LState, s_: LState, c: LConstants) -> bool {
        &&& s.tm_state is Init
        &&& s.tm_prepared == c.rm
        &&& s_.tm_state is Committed
        &&& s_.rm_state == s.rm_state
        &&& s_.tm_prepared == s.tm_prepared
    }

    /// Transaction Manager aborts
    pub open spec fn LTMAbort(s: LState, s_: LState, c: LConstants) -> bool {
        &&& s.tm_state is Init
        &&& s_.tm_state is Aborted
        &&& s_.rm_state == s.rm_state
        &&& s_.tm_prepared == s.tm_prepared
    }

    /// Next-state relation: disjunction of all possible transitions
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        ||| LTMCommit(s, s_, c)
        ||| LTMAbort(s, s_, c)
        ||| exists |r: int| LTMRcvPrepared(s, s_, c, r)
    }
}
