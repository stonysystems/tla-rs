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
    }

    /// Transaction Manager broadcasts Prepare to all RMs
    pub open spec fn LTMSendPrepare(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LTPCMessage>) -> bool {
        &&& s.tm_state is Init
        &&& s_.tm_state == s.tm_state
        &&& s_.tm_prepared == s.tm_prepared
        &&& s_.rm_prepared == s.rm_prepared
        &&& s_.rm_committed == s.rm_committed
        &&& s_.rm_aborted == s.rm_aborted
        &&& sent_packets == seq![LTPCMessage::Prepare]
    }

    /// Resource Manager receives Prepare and transitions Working -> Prepared
    pub open spec fn LRMReceivePrepare(s: LState, s_: LState, c: LConstants, rm: int, sent_packets: Seq<LTPCMessage>) -> bool {
        &&& c.rm.contains(rm)
        &&& !s.rm_prepared.contains(rm)
        &&& !s.rm_aborted.contains(rm)
        &&& s_.tm_state == s.tm_state
        &&& s_.tm_prepared == s.tm_prepared
        &&& s_.rm_prepared == s.rm_prepared.insert(rm)
        &&& s_.rm_committed == s.rm_committed
        &&& s_.rm_aborted == s.rm_aborted
        &&& sent_packets == seq![LTPCMessage::PreparedVote { rm }]
    }

    /// Resource Manager unilaterally aborts (before receiving Prepare or while Working)
    pub open spec fn LRMAbort(s: LState, s_: LState, c: LConstants, rm: int, sent_packets: Seq<LTPCMessage>) -> bool {
        &&& c.rm.contains(rm)
        &&& !s.rm_prepared.contains(rm)
        &&& !s.rm_aborted.contains(rm)
        &&& !s.rm_committed.contains(rm)
        &&& s_.tm_state == s.tm_state
        &&& s_.tm_prepared == s.tm_prepared
        &&& s_.rm_prepared == s.rm_prepared
        &&& s_.rm_committed == s.rm_committed
        &&& s_.rm_aborted == s.rm_aborted.insert(rm)
        &&& sent_packets == Seq::<LTPCMessage>::empty()
    }

    /// Transaction Manager receives Prepared from resource manager r
    pub open spec fn LTMRcvPrepared(s: LState, s_: LState, c: LConstants, r: int, sent_packets: Seq<LTPCMessage>) -> bool {
        &&& s.tm_state is Init
        &&& s.rm_prepared.contains(r)
        &&& s_.tm_state is Init
        &&& s_.tm_prepared == s.tm_prepared.insert(r)
        &&& s_.rm_prepared == s.rm_prepared
        &&& s_.rm_committed == s.rm_committed
        &&& s_.rm_aborted == s.rm_aborted
        &&& sent_packets == Seq::<LTPCMessage>::empty()
    }

    /// Transaction Manager commits (all RMs prepared) and broadcasts Commit
    pub open spec fn LTMSendCommit(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LTPCMessage>) -> bool {
        &&& s.tm_state is Init
        &&& s.tm_prepared == c.rm
        &&& s_.tm_state is Committed
        &&& s_.tm_prepared == s.tm_prepared
        &&& s_.rm_prepared == s.rm_prepared
        &&& s_.rm_committed == s.rm_committed
        &&& s_.rm_aborted == s.rm_aborted
        &&& sent_packets == seq![LTPCMessage::Commit]
    }

    /// Transaction Manager aborts and broadcasts Abort
    pub open spec fn LTMSendAbort(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LTPCMessage>) -> bool {
        &&& s.tm_state is Init
        &&& s_.tm_state is Aborted
        &&& s_.tm_prepared == s.tm_prepared
        &&& s_.rm_prepared == s.rm_prepared
        &&& s_.rm_committed == s.rm_committed
        &&& s_.rm_aborted == s.rm_aborted
        &&& sent_packets == seq![LTPCMessage::Abort]
    }

    /// Resource Manager receives Commit and transitions Prepared -> Committed
    pub open spec fn LRMReceiveCommit(s: LState, s_: LState, c: LConstants, rm: int, sent_packets: Seq<LTPCMessage>) -> bool {
        &&& c.rm.contains(rm)
        &&& s.rm_prepared.contains(rm)
        &&& !s.rm_committed.contains(rm)
        &&& s_.tm_state == s.tm_state
        &&& s_.tm_prepared == s.tm_prepared
        &&& s_.rm_prepared == s.rm_prepared
        &&& s_.rm_committed == s.rm_committed.insert(rm)
        &&& s_.rm_aborted == s.rm_aborted
        &&& sent_packets == Seq::<LTPCMessage>::empty()
    }

    /// Resource Manager receives Abort and transitions to Aborted
    pub open spec fn LRMReceiveAbort(s: LState, s_: LState, c: LConstants, rm: int, sent_packets: Seq<LTPCMessage>) -> bool {
        &&& c.rm.contains(rm)
        &&& !s.rm_committed.contains(rm)
        &&& !s.rm_aborted.contains(rm)
        &&& s_.tm_state == s.tm_state
        &&& s_.tm_prepared == s.tm_prepared
        &&& s_.rm_prepared == s.rm_prepared
        &&& s_.rm_committed == s.rm_committed
        &&& s_.rm_aborted == s.rm_aborted.insert(rm)
        &&& sent_packets == Seq::<LTPCMessage>::empty()
    }

    /// Next-state relation: disjunction of all possible transitions
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        ||| (exists |sent_packets: Seq<LTPCMessage>| LTMSendPrepare(s, s_, c, sent_packets))
        ||| (exists |rm: int, sent_packets: Seq<LTPCMessage>| LRMReceivePrepare(s, s_, c, rm, sent_packets))
        ||| (exists |rm: int, sent_packets: Seq<LTPCMessage>| LRMAbort(s, s_, c, rm, sent_packets))
        ||| (exists |r: int, sent_packets: Seq<LTPCMessage>| LTMRcvPrepared(s, s_, c, r, sent_packets))
        ||| (exists |sent_packets: Seq<LTPCMessage>| LTMSendCommit(s, s_, c, sent_packets))
        ||| (exists |sent_packets: Seq<LTPCMessage>| LTMSendAbort(s, s_, c, sent_packets))
        ||| (exists |rm: int, sent_packets: Seq<LTPCMessage>| LRMReceiveCommit(s, s_, c, rm, sent_packets))
        ||| (exists |rm: int, sent_packets: Seq<LTPCMessage>| LRMReceiveAbort(s, s_, c, rm, sent_packets))
    }

    /// Safety: no resource manager can be both committed and aborted.
    pub open spec fn LSafetyNoCommitAbortOverlap(s: LState, c: LConstants) -> bool {
        forall |rm: int| s.rm_committed.contains(rm) ==> !s.rm_aborted.contains(rm)
    }

    /// Safety: committed resource managers must have been prepared.
    pub open spec fn LSafetyCommittedSubsetPrepared(s: LState, c: LConstants) -> bool {
        forall |rm: int| s.rm_committed.contains(rm) ==> s.rm_prepared.contains(rm)
    }

    /// Safety: TM can only be in committed state after all RMs prepared.
    pub open spec fn LSafetyTmCommittedRequiresAllPrepared(s: LState, c: LConstants) -> bool {
        s.tm_state is Committed ==> s.tm_prepared == c.rm
    }
}
