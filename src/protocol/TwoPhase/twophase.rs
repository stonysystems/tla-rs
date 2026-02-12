use crate::protocol::TwoPhase::types::*;
use vstd::prelude::*;

verus! {
    /// Initialize the protocol state
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.tm_state is Init
        &&& s.tm_prepared == Set::<int>::empty()
        &&& s.rm_prepared == Set::<int>::empty()
        &&& s.rm_committed == Set::<int>::empty()
        &&& s.rm_aborted == Set::<int>::empty()
        &&& s.msgs_prepare == false
        &&& s.msgs_commit == false
        &&& s.msgs_abort == false
    }

    /// Transaction Manager broadcasts Prepare to all RMs
    pub open spec fn LTMSendPrepare(s: LState, s_: LState, c: LConstants) -> bool {
        &&& s.tm_state is Init
        &&& s_.tm_state == s.tm_state
        &&& s_.tm_prepared == s.tm_prepared
        &&& s_.rm_prepared == s.rm_prepared
        &&& s_.rm_committed == s.rm_committed
        &&& s_.rm_aborted == s.rm_aborted
        &&& s_.msgs_prepare == true
        &&& s_.msgs_commit == s.msgs_commit
        &&& s_.msgs_abort == s.msgs_abort
    }

    /// Resource Manager receives Prepare and transitions Working -> Prepared
    pub open spec fn LRMReceivePrepare(s: LState, s_: LState, c: LConstants, rm: int) -> bool {
        &&& c.rm.contains(rm)
        &&& s.msgs_prepare == true
        &&& !s.rm_prepared.contains(rm)
        &&& !s.rm_aborted.contains(rm)
        &&& s_.tm_state == s.tm_state
        &&& s_.tm_prepared == s.tm_prepared
        &&& s_.rm_prepared == s.rm_prepared.insert(rm)
        &&& s_.rm_committed == s.rm_committed
        &&& s_.rm_aborted == s.rm_aborted
        &&& s_.msgs_prepare == s.msgs_prepare
        &&& s_.msgs_commit == s.msgs_commit
        &&& s_.msgs_abort == s.msgs_abort
    }

    /// Resource Manager unilaterally aborts (before receiving Prepare or while Working)
    pub open spec fn LRMAbort(s: LState, s_: LState, c: LConstants, rm: int) -> bool {
        &&& c.rm.contains(rm)
        &&& !s.rm_prepared.contains(rm)
        &&& !s.rm_aborted.contains(rm)
        &&& !s.rm_committed.contains(rm)
        &&& s_.tm_state == s.tm_state
        &&& s_.tm_prepared == s.tm_prepared
        &&& s_.rm_prepared == s.rm_prepared
        &&& s_.rm_committed == s.rm_committed
        &&& s_.rm_aborted == s.rm_aborted.insert(rm)
        &&& s_.msgs_prepare == s.msgs_prepare
        &&& s_.msgs_commit == s.msgs_commit
        &&& s_.msgs_abort == s.msgs_abort
    }

    /// Transaction Manager receives Prepared from resource manager r
    pub open spec fn LTMRcvPrepared(s: LState, s_: LState, c: LConstants, r: int) -> bool {
        &&& s.tm_state is Init
        &&& s.rm_prepared.contains(r)
        &&& s_.tm_state is Init
        &&& s_.tm_prepared == s.tm_prepared.insert(r)
        &&& s_.rm_prepared == s.rm_prepared
        &&& s_.rm_committed == s.rm_committed
        &&& s_.rm_aborted == s.rm_aborted
        &&& s_.msgs_prepare == s.msgs_prepare
        &&& s_.msgs_commit == s.msgs_commit
        &&& s_.msgs_abort == s.msgs_abort
    }

    /// Transaction Manager commits (all RMs prepared) and broadcasts Commit
    pub open spec fn LTMSendCommit(s: LState, s_: LState, c: LConstants) -> bool {
        &&& s.tm_state is Init
        &&& s.tm_prepared == c.rm
        &&& s_.tm_state is Committed
        &&& s_.tm_prepared == s.tm_prepared
        &&& s_.rm_prepared == s.rm_prepared
        &&& s_.rm_committed == s.rm_committed
        &&& s_.rm_aborted == s.rm_aborted
        &&& s_.msgs_prepare == s.msgs_prepare
        &&& s_.msgs_commit == true
        &&& s_.msgs_abort == s.msgs_abort
    }

    /// Transaction Manager aborts and broadcasts Abort
    pub open spec fn LTMSendAbort(s: LState, s_: LState, c: LConstants) -> bool {
        &&& s.tm_state is Init
        &&& s_.tm_state is Aborted
        &&& s_.tm_prepared == s.tm_prepared
        &&& s_.rm_prepared == s.rm_prepared
        &&& s_.rm_committed == s.rm_committed
        &&& s_.rm_aborted == s.rm_aborted
        &&& s_.msgs_prepare == s.msgs_prepare
        &&& s_.msgs_commit == s.msgs_commit
        &&& s_.msgs_abort == true
    }

    /// Resource Manager receives Commit and transitions Prepared -> Committed
    pub open spec fn LRMReceiveCommit(s: LState, s_: LState, c: LConstants, rm: int) -> bool {
        &&& c.rm.contains(rm)
        &&& s.msgs_commit == true
        &&& s.rm_prepared.contains(rm)
        &&& !s.rm_committed.contains(rm)
        &&& s_.tm_state == s.tm_state
        &&& s_.tm_prepared == s.tm_prepared
        &&& s_.rm_prepared == s.rm_prepared
        &&& s_.rm_committed == s.rm_committed.insert(rm)
        &&& s_.rm_aborted == s.rm_aborted
        &&& s_.msgs_prepare == s.msgs_prepare
        &&& s_.msgs_commit == s.msgs_commit
        &&& s_.msgs_abort == s.msgs_abort
    }

    /// Resource Manager receives Abort and transitions to Aborted
    pub open spec fn LRMReceiveAbort(s: LState, s_: LState, c: LConstants, rm: int) -> bool {
        &&& c.rm.contains(rm)
        &&& s.msgs_abort == true
        &&& !s.rm_committed.contains(rm)
        &&& !s.rm_aborted.contains(rm)
        &&& s_.tm_state == s.tm_state
        &&& s_.tm_prepared == s.tm_prepared
        &&& s_.rm_prepared == s.rm_prepared
        &&& s_.rm_committed == s.rm_committed
        &&& s_.rm_aborted == s.rm_aborted.insert(rm)
        &&& s_.msgs_prepare == s.msgs_prepare
        &&& s_.msgs_commit == s.msgs_commit
        &&& s_.msgs_abort == s.msgs_abort
    }

    /// Next-state relation: disjunction of all possible transitions
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        ||| LTMSendPrepare(s, s_, c)
        ||| (exists |rm: int| LRMReceivePrepare(s, s_, c, rm))
        ||| (exists |rm: int| LRMAbort(s, s_, c, rm))
        ||| (exists |r: int| LTMRcvPrepared(s, s_, c, r))
        ||| LTMSendCommit(s, s_, c)
        ||| LTMSendAbort(s, s_, c)
        ||| (exists |rm: int| LRMReceiveCommit(s, s_, c, rm))
        ||| (exists |rm: int| LRMReceiveAbort(s, s_, c, rm))
    }
}
