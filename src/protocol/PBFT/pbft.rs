/// Simplified PBFT (Practical Byzantine Fault Tolerance) protocol.
///
/// Models the core PBFT consensus phases:
/// 1. Pre-prepare: Primary broadcasts client request
/// 2. Prepare: Replicas exchange prepare messages (need 2f+1)
/// 3. Commit: Replicas exchange commit messages (need 2f+1)
/// 4. Reply: Execute request and send result to client
/// 5. View change: On timeout, increment view number
use vstd::prelude::*;
use crate::protocol::PBFT::types::*;

verus! {

/// Initial state: view 0, pre-prepare phase, primary node
pub open spec fn LInit(s: LState, c: LConstants) -> bool {
    &&& s.view == 0
    &&& s.phase is PrePrepare
    &&& s.prepare_count == 0
    &&& s.commit_count == 0
    &&& s.seq_num == 0
    &&& s.is_primary == true
    &&& c.n >= 3 * c.f + 1
    &&& c.f >= 0
}

/// Pre-prepare: Primary broadcasts a client request to all replicas.
/// Moves from PrePrepare to Prepare phase.
pub open spec fn LPrePrepare(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is PrePrepare
    &&& s.is_primary == true
    &&& s_.phase is Prepare
    &&& s_.view == s.view
    &&& s_.prepare_count == 1
    &&& s_.commit_count == 0
    &&& s_.seq_num == s.seq_num
    &&& s_.is_primary == s.is_primary
}

/// Receive a prepare message from another replica.
/// Increments prepare_count (only valid in Prepare phase).
pub open spec fn LReceivePrepare(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is Prepare
    &&& s.prepare_count < c.n
    &&& s_.phase == s.phase
    &&& s_.view == s.view
    &&& s_.prepare_count == s.prepare_count + 1
    &&& s_.commit_count == s.commit_count
    &&& s_.seq_num == s.seq_num
    &&& s_.is_primary == s.is_primary
}

/// Enter commit phase when enough prepares received (quorum = 2f+1).
/// Prepared predicate satisfied -> transition to Commit phase.
pub open spec fn LEnterCommit(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is Prepare
    &&& s.prepare_count >= 2 * c.f + 1
    &&& s_.phase is Commit
    &&& s_.view == s.view
    &&& s_.prepare_count == s.prepare_count
    &&& s_.commit_count == 1
    &&& s_.seq_num == s.seq_num
    &&& s_.is_primary == s.is_primary
}

/// Receive a commit message from another replica.
/// Increments commit_count (only valid in Commit phase).
pub open spec fn LReceiveCommit(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is Commit
    &&& s.commit_count < c.n
    &&& s_.phase == s.phase
    &&& s_.view == s.view
    &&& s_.prepare_count == s.prepare_count
    &&& s_.commit_count == s.commit_count + 1
    &&& s_.seq_num == s.seq_num
    &&& s_.is_primary == s.is_primary
}

/// Execute request and reply to client when enough commits received.
/// Committed predicate satisfied -> execute, increment seq_num, reset.
pub open spec fn LExecuteReply(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is Commit
    &&& s.commit_count >= 2 * c.f + 1
    &&& s_.phase is Replied
    &&& s_.view == s.view
    &&& s_.prepare_count == 0
    &&& s_.commit_count == 0
    &&& s_.seq_num == s.seq_num + 1
    &&& s_.is_primary == s.is_primary
}

/// View change: on timeout, increment view and reset to PrePrepare.
/// The new primary is determined by view number (view mod n).
pub open spec fn LViewChange(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s_.view == s.view + 1
    &&& s_.phase is PrePrepare
    &&& s_.prepare_count == 0
    &&& s_.commit_count == 0
    &&& s_.seq_num == s.seq_num
    &&& s_.is_primary == s.is_primary
}

/// Start new round: after reply, return to PrePrepare for next request.
pub open spec fn LNewRound(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is Replied
    &&& s_.phase is PrePrepare
    &&& s_.view == s.view
    &&& s_.prepare_count == 0
    &&& s_.commit_count == 0
    &&& s_.seq_num == s.seq_num
    &&& s_.is_primary == s.is_primary
}

/// Next-state relation: disjunction of all transitions.
pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
    ||| LPrePrepare(s, s_, c)
    ||| LReceivePrepare(s, s_, c)
    ||| LEnterCommit(s, s_, c)
    ||| LReceiveCommit(s, s_, c)
    ||| LExecuteReply(s, s_, c)
    ||| LViewChange(s, s_, c)
    ||| LNewRound(s, s_, c)
}

} // verus!
