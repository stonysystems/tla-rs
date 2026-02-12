/// EPaxos (Egalitarian Paxos) protocol.
///
/// Models the key EPaxos innovations from a single replica's perspective:
/// 1. Any replica can propose (leaderless)
/// 2. Fast path (1 RTT): propose with deps, commit if quorum agrees
/// 3. Slow path (2 RTT): on conflict, run Paxos-like accept phase
/// 4. Set-based quorum tracking for pre-accept and accept phases
/// 5. Message flags for all protocol messages
/// 6. Execution after commit
///
/// Transitions:
/// - Propose: Replica proposes a new command, enters PreAccepted, sends PreAccept
/// - SendPreAcceptOk: Non-leader responds to PreAccept message
/// - ReceivePreAcceptOk: Leader accumulates PreAcceptOk responses
/// - FastCommit: If fast quorum agrees (no conflicts), commit directly
/// - StartAccept: If conflict detected, begin slow path accept phase
/// - SendAcceptOk: Replica responds to Accept message
/// - ReceiveAcceptOk: Leader accumulates AcceptOk responses
/// - SlowCommit: If quorum acks in accept phase, commit
/// - Execute: Execute a committed command
/// - Recover: Recover an instance from a failed leader
/// - NewInstance: Reset to accept a new command after execution
use vstd::prelude::*;
use vstd::set::*;
use crate::protocol::EPaxos::types::*;

verus! {

/// Initial state: empty instance slot, no commands
pub open spec fn LInit(s: LState, c: LConstants) -> bool {
    &&& s.ballot == 0
    &&& s.phase is Empty
    &&& s.cmd == 0
    &&& s.seq == 0
    &&& s.dep_count == 0
    &&& s.is_leader == false
    &&& s.committed_count == 0
    &&& s.executed_count == 0
    &&& s.preaccept_senders == Set::<int>::empty()
    &&& s.accept_senders == Set::<int>::empty()
    &&& s.has_conflict == false
    &&& s.max_resp_seq == 0
    &&& s.msgs_preaccept == false
    &&& s.msgs_preaccept_ballot == 0
    &&& s.msgs_preaccept_cmd == 0
    &&& s.msgs_preaccept_seq == 0
    &&& s.msgs_preaccept_ok == false
    &&& s.msgs_preaccept_ok_sender == 0
    &&& s.msgs_preaccept_ok_seq == 0
    &&& s.msgs_preaccept_ok_conflict == false
    &&& s.msgs_accept == false
    &&& s.msgs_accept_ballot == 0
    &&& s.msgs_accept_cmd == 0
    &&& s.msgs_accept_seq == 0
    &&& s.msgs_accept_ok == false
    &&& s.msgs_accept_ok_sender == 0
    &&& s.msgs_commit == false
    &&& s.msgs_commit_cmd == 0
    &&& s.msgs_commit_seq == 0
    &&& c.num_replicas >= 3
    &&& c.quorum_size > 0
    &&& c.fast_quorum_size >= c.quorum_size
}

/// Propose: This replica proposes a new command (any replica can do this).
/// Assigns a sequence number and enters PreAccepted. Sends PreAccept message.
pub open spec fn LPropose(
    s: LState, s_: LState, c: LConstants, value: int,
) -> bool {
    &&& s.phase is Empty
    // State update: enter pre-accept phase as leader, send PreAccept
    &&& s_.ballot == s.ballot
    &&& s_.phase is PreAccepted
    &&& s_.cmd == value
    &&& s_.seq == s.committed_count + 1
    &&& s_.dep_count == 0
    &&& s_.is_leader == true
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
    &&& s_.preaccept_senders == Set::<int>::empty().insert(c.my_id)
    &&& s_.accept_senders == Set::<int>::empty()
    &&& s_.has_conflict == false
    &&& s_.max_resp_seq == 0
    // Send PreAccept message
    &&& s_.msgs_preaccept == true
    &&& s_.msgs_preaccept_ballot == s.ballot
    &&& s_.msgs_preaccept_cmd == value
    &&& s_.msgs_preaccept_seq == s.committed_count + 1
    // Clear other messages
    &&& s_.msgs_preaccept_ok == false
    &&& s_.msgs_preaccept_ok_sender == 0
    &&& s_.msgs_preaccept_ok_seq == 0
    &&& s_.msgs_preaccept_ok_conflict == false
    &&& s_.msgs_accept == false
    &&& s_.msgs_accept_ballot == 0
    &&& s_.msgs_accept_cmd == 0
    &&& s_.msgs_accept_seq == 0
    &&& s_.msgs_accept_ok == false
    &&& s_.msgs_accept_ok_sender == 0
    &&& s_.msgs_commit == false
    &&& s_.msgs_commit_cmd == 0
    &&& s_.msgs_commit_seq == 0
}

/// SendPreAcceptOk: Non-leader replica responds to a PreAccept message.
/// Checks for local conflicts and reports back.
pub open spec fn LSendPreAcceptOk(
    s: LState, s_: LState, c: LConstants, local_conflict: bool, local_seq: int,
) -> bool {
    &&& s.msgs_preaccept == true
    // State update: send PreAcceptOk response
    &&& s_.msgs_preaccept_ok == true
    &&& s_.msgs_preaccept_ok_sender == c.my_id
    &&& s_.msgs_preaccept_ok_seq == local_seq
    &&& s_.msgs_preaccept_ok_conflict == local_conflict
    // Frame: preserve all other state
    &&& s_.ballot == s.ballot
    &&& s_.phase == s.phase
    &&& s_.cmd == s.cmd
    &&& s_.seq == s.seq
    &&& s_.dep_count == s.dep_count
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
    &&& s_.preaccept_senders == s.preaccept_senders
    &&& s_.accept_senders == s.accept_senders
    &&& s_.has_conflict == s.has_conflict
    &&& s_.max_resp_seq == s.max_resp_seq
    &&& s_.msgs_preaccept == s.msgs_preaccept
    &&& s_.msgs_preaccept_ballot == s.msgs_preaccept_ballot
    &&& s_.msgs_preaccept_cmd == s.msgs_preaccept_cmd
    &&& s_.msgs_preaccept_seq == s.msgs_preaccept_seq
    &&& s_.msgs_accept == s.msgs_accept
    &&& s_.msgs_accept_ballot == s.msgs_accept_ballot
    &&& s_.msgs_accept_cmd == s.msgs_accept_cmd
    &&& s_.msgs_accept_seq == s.msgs_accept_seq
    &&& s_.msgs_accept_ok == s.msgs_accept_ok
    &&& s_.msgs_accept_ok_sender == s.msgs_accept_ok_sender
    &&& s_.msgs_commit == s.msgs_commit
    &&& s_.msgs_commit_cmd == s.msgs_commit_cmd
    &&& s_.msgs_commit_seq == s.msgs_commit_seq
}

/// ReceivePreAcceptOk: Leader receives a PreAcceptOk response.
/// Tracks sender in set, updates conflict and max seq info.
pub open spec fn LReceivePreAcceptOk(
    s: LState, s_: LState, c: LConstants,
) -> bool {
    &&& s.phase is PreAccepted
    &&& s.is_leader == true
    &&& s.msgs_preaccept_ok == true
    &&& !s.preaccept_senders.contains(s.msgs_preaccept_ok_sender)
    // State update: accumulate response
    &&& s_.preaccept_senders == s.preaccept_senders.insert(s.msgs_preaccept_ok_sender)
    &&& s_.has_conflict == (if s.msgs_preaccept_ok_conflict { true } else { s.has_conflict })
    &&& s_.dep_count == (if s.msgs_preaccept_ok_conflict { s.dep_count + 1 } else { s.dep_count })
    &&& s_.max_resp_seq == (if s.msgs_preaccept_ok_seq > s.max_resp_seq { s.msgs_preaccept_ok_seq } else { s.max_resp_seq })
    &&& s_.seq == (if s.msgs_preaccept_ok_seq > s.seq { s.msgs_preaccept_ok_seq } else { s.seq })
    // Frame: preserve all other state
    &&& s_.ballot == s.ballot
    &&& s_.phase == s.phase
    &&& s_.cmd == s.cmd
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
    &&& s_.accept_senders == s.accept_senders
    &&& s_.msgs_preaccept == s.msgs_preaccept
    &&& s_.msgs_preaccept_ballot == s.msgs_preaccept_ballot
    &&& s_.msgs_preaccept_cmd == s.msgs_preaccept_cmd
    &&& s_.msgs_preaccept_seq == s.msgs_preaccept_seq
    &&& s_.msgs_preaccept_ok == s.msgs_preaccept_ok
    &&& s_.msgs_preaccept_ok_sender == s.msgs_preaccept_ok_sender
    &&& s_.msgs_preaccept_ok_seq == s.msgs_preaccept_ok_seq
    &&& s_.msgs_preaccept_ok_conflict == s.msgs_preaccept_ok_conflict
    &&& s_.msgs_accept == s.msgs_accept
    &&& s_.msgs_accept_ballot == s.msgs_accept_ballot
    &&& s_.msgs_accept_cmd == s.msgs_accept_cmd
    &&& s_.msgs_accept_seq == s.msgs_accept_seq
    &&& s_.msgs_accept_ok == s.msgs_accept_ok
    &&& s_.msgs_accept_ok_sender == s.msgs_accept_ok_sender
    &&& s_.msgs_commit == s.msgs_commit
    &&& s_.msgs_commit_cmd == s.msgs_commit_cmd
    &&& s_.msgs_commit_seq == s.msgs_commit_seq
}

/// FastCommit: Commit on the fast path when the fast quorum agrees (no conflicts).
/// This is EPaxos's 1-RTT fast path. Uses Set::len() for quorum check.
pub open spec fn LFastCommit(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is PreAccepted
    &&& s.is_leader == true
    &&& s.preaccept_senders.len() >= c.fast_quorum_size
    &&& s.has_conflict == false
    // State update: commit directly, send Commit message
    &&& s_.ballot == s.ballot
    &&& s_.phase is Committed
    &&& s_.cmd == s.cmd
    &&& s_.seq == s.seq
    &&& s_.dep_count == s.dep_count
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count + 1
    &&& s_.executed_count == s.executed_count
    &&& s_.preaccept_senders == s.preaccept_senders
    &&& s_.accept_senders == s.accept_senders
    &&& s_.has_conflict == s.has_conflict
    &&& s_.max_resp_seq == s.max_resp_seq
    // Send Commit message
    &&& s_.msgs_commit == true
    &&& s_.msgs_commit_cmd == s.cmd
    &&& s_.msgs_commit_seq == s.seq
    // Clear other messages
    &&& s_.msgs_preaccept == false
    &&& s_.msgs_preaccept_ballot == 0
    &&& s_.msgs_preaccept_cmd == 0
    &&& s_.msgs_preaccept_seq == 0
    &&& s_.msgs_preaccept_ok == false
    &&& s_.msgs_preaccept_ok_sender == 0
    &&& s_.msgs_preaccept_ok_seq == 0
    &&& s_.msgs_preaccept_ok_conflict == false
    &&& s_.msgs_accept == false
    &&& s_.msgs_accept_ballot == 0
    &&& s_.msgs_accept_cmd == 0
    &&& s_.msgs_accept_seq == 0
    &&& s_.msgs_accept_ok == false
    &&& s_.msgs_accept_ok_sender == 0
}

/// StartAccept: Begin the slow path (Paxos-like accept phase) when conflicts detected.
/// Uses Set::len() for quorum check.
pub open spec fn LStartAccept(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is PreAccepted
    &&& s.is_leader == true
    &&& s.preaccept_senders.len() >= c.quorum_size
    &&& s.has_conflict == true
    // State update: enter accept phase, send Accept message
    &&& s_.ballot == s.ballot
    &&& s_.phase is Accepted
    &&& s_.cmd == s.cmd
    &&& s_.seq == s.seq
    &&& s_.dep_count == s.dep_count
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
    &&& s_.preaccept_senders == s.preaccept_senders
    &&& s_.accept_senders == Set::<int>::empty().insert(c.my_id)
    &&& s_.has_conflict == s.has_conflict
    &&& s_.max_resp_seq == s.max_resp_seq
    // Send Accept message
    &&& s_.msgs_accept == true
    &&& s_.msgs_accept_ballot == s.ballot
    &&& s_.msgs_accept_cmd == s.cmd
    &&& s_.msgs_accept_seq == s.seq
    // Clear PreAccept messages
    &&& s_.msgs_preaccept == false
    &&& s_.msgs_preaccept_ballot == 0
    &&& s_.msgs_preaccept_cmd == 0
    &&& s_.msgs_preaccept_seq == 0
    &&& s_.msgs_preaccept_ok == false
    &&& s_.msgs_preaccept_ok_sender == 0
    &&& s_.msgs_preaccept_ok_seq == 0
    &&& s_.msgs_preaccept_ok_conflict == false
    &&& s_.msgs_accept_ok == false
    &&& s_.msgs_accept_ok_sender == 0
    &&& s_.msgs_commit == false
    &&& s_.msgs_commit_cmd == 0
    &&& s_.msgs_commit_seq == 0
}

/// SendAcceptOk: Replica responds to an Accept message.
pub open spec fn LSendAcceptOk(
    s: LState, s_: LState, c: LConstants,
) -> bool {
    &&& s.msgs_accept == true
    // State update: send AcceptOk response
    &&& s_.msgs_accept_ok == true
    &&& s_.msgs_accept_ok_sender == c.my_id
    // Frame: preserve all other state
    &&& s_.ballot == s.ballot
    &&& s_.phase == s.phase
    &&& s_.cmd == s.cmd
    &&& s_.seq == s.seq
    &&& s_.dep_count == s.dep_count
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
    &&& s_.preaccept_senders == s.preaccept_senders
    &&& s_.accept_senders == s.accept_senders
    &&& s_.has_conflict == s.has_conflict
    &&& s_.max_resp_seq == s.max_resp_seq
    &&& s_.msgs_preaccept == s.msgs_preaccept
    &&& s_.msgs_preaccept_ballot == s.msgs_preaccept_ballot
    &&& s_.msgs_preaccept_cmd == s.msgs_preaccept_cmd
    &&& s_.msgs_preaccept_seq == s.msgs_preaccept_seq
    &&& s_.msgs_preaccept_ok == s.msgs_preaccept_ok
    &&& s_.msgs_preaccept_ok_sender == s.msgs_preaccept_ok_sender
    &&& s_.msgs_preaccept_ok_seq == s.msgs_preaccept_ok_seq
    &&& s_.msgs_preaccept_ok_conflict == s.msgs_preaccept_ok_conflict
    &&& s_.msgs_accept == s.msgs_accept
    &&& s_.msgs_accept_ballot == s.msgs_accept_ballot
    &&& s_.msgs_accept_cmd == s.msgs_accept_cmd
    &&& s_.msgs_accept_seq == s.msgs_accept_seq
    &&& s_.msgs_commit == s.msgs_commit
    &&& s_.msgs_commit_cmd == s.msgs_commit_cmd
    &&& s_.msgs_commit_seq == s.msgs_commit_seq
}

/// ReceiveAcceptOk: Leader receives an AcceptOk response during the slow path.
/// Tracks sender in set.
pub open spec fn LReceiveAcceptOk(
    s: LState, s_: LState, c: LConstants,
) -> bool {
    &&& s.phase is Accepted
    &&& s.is_leader == true
    &&& s.msgs_accept_ok == true
    &&& !s.accept_senders.contains(s.msgs_accept_ok_sender)
    // State update: accumulate accept
    &&& s_.accept_senders == s.accept_senders.insert(s.msgs_accept_ok_sender)
    // Frame: preserve all other state
    &&& s_.ballot == s.ballot
    &&& s_.phase == s.phase
    &&& s_.cmd == s.cmd
    &&& s_.seq == s.seq
    &&& s_.dep_count == s.dep_count
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
    &&& s_.preaccept_senders == s.preaccept_senders
    &&& s_.has_conflict == s.has_conflict
    &&& s_.max_resp_seq == s.max_resp_seq
    &&& s_.msgs_preaccept == s.msgs_preaccept
    &&& s_.msgs_preaccept_ballot == s.msgs_preaccept_ballot
    &&& s_.msgs_preaccept_cmd == s.msgs_preaccept_cmd
    &&& s_.msgs_preaccept_seq == s.msgs_preaccept_seq
    &&& s_.msgs_preaccept_ok == s.msgs_preaccept_ok
    &&& s_.msgs_preaccept_ok_sender == s.msgs_preaccept_ok_sender
    &&& s_.msgs_preaccept_ok_seq == s.msgs_preaccept_ok_seq
    &&& s_.msgs_preaccept_ok_conflict == s.msgs_preaccept_ok_conflict
    &&& s_.msgs_accept == s.msgs_accept
    &&& s_.msgs_accept_ballot == s.msgs_accept_ballot
    &&& s_.msgs_accept_cmd == s.msgs_accept_cmd
    &&& s_.msgs_accept_seq == s.msgs_accept_seq
    &&& s_.msgs_accept_ok == s.msgs_accept_ok
    &&& s_.msgs_accept_ok_sender == s.msgs_accept_ok_sender
    &&& s_.msgs_commit == s.msgs_commit
    &&& s_.msgs_commit_cmd == s.msgs_commit_cmd
    &&& s_.msgs_commit_seq == s.msgs_commit_seq
}

/// SlowCommit: Commit on the slow path when a quorum accepts.
/// Uses Set::len() for quorum check.
pub open spec fn LSlowCommit(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is Accepted
    &&& s.is_leader == true
    &&& s.accept_senders.len() >= c.quorum_size
    // State update: commit, send Commit message
    &&& s_.ballot == s.ballot
    &&& s_.phase is Committed
    &&& s_.cmd == s.cmd
    &&& s_.seq == s.seq
    &&& s_.dep_count == s.dep_count
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count + 1
    &&& s_.executed_count == s.executed_count
    &&& s_.preaccept_senders == s.preaccept_senders
    &&& s_.accept_senders == s.accept_senders
    &&& s_.has_conflict == s.has_conflict
    &&& s_.max_resp_seq == s.max_resp_seq
    // Send Commit message
    &&& s_.msgs_commit == true
    &&& s_.msgs_commit_cmd == s.cmd
    &&& s_.msgs_commit_seq == s.seq
    // Clear Accept messages
    &&& s_.msgs_preaccept == false
    &&& s_.msgs_preaccept_ballot == 0
    &&& s_.msgs_preaccept_cmd == 0
    &&& s_.msgs_preaccept_seq == 0
    &&& s_.msgs_preaccept_ok == false
    &&& s_.msgs_preaccept_ok_sender == 0
    &&& s_.msgs_preaccept_ok_seq == 0
    &&& s_.msgs_preaccept_ok_conflict == false
    &&& s_.msgs_accept == false
    &&& s_.msgs_accept_ballot == 0
    &&& s_.msgs_accept_cmd == 0
    &&& s_.msgs_accept_seq == 0
    &&& s_.msgs_accept_ok == false
    &&& s_.msgs_accept_ok_sender == 0
}

/// Execute: Execute a committed command.
pub open spec fn LExecute(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is Committed
    // State update: mark as executed
    &&& s_.ballot == s.ballot
    &&& s_.phase is Executed
    &&& s_.cmd == s.cmd
    &&& s_.seq == s.seq
    &&& s_.dep_count == s.dep_count
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count + 1
    &&& s_.preaccept_senders == s.preaccept_senders
    &&& s_.accept_senders == s.accept_senders
    &&& s_.has_conflict == s.has_conflict
    &&& s_.max_resp_seq == s.max_resp_seq
    &&& s_.msgs_preaccept == s.msgs_preaccept
    &&& s_.msgs_preaccept_ballot == s.msgs_preaccept_ballot
    &&& s_.msgs_preaccept_cmd == s.msgs_preaccept_cmd
    &&& s_.msgs_preaccept_seq == s.msgs_preaccept_seq
    &&& s_.msgs_preaccept_ok == s.msgs_preaccept_ok
    &&& s_.msgs_preaccept_ok_sender == s.msgs_preaccept_ok_sender
    &&& s_.msgs_preaccept_ok_seq == s.msgs_preaccept_ok_seq
    &&& s_.msgs_preaccept_ok_conflict == s.msgs_preaccept_ok_conflict
    &&& s_.msgs_accept == s.msgs_accept
    &&& s_.msgs_accept_ballot == s.msgs_accept_ballot
    &&& s_.msgs_accept_cmd == s.msgs_accept_cmd
    &&& s_.msgs_accept_seq == s.msgs_accept_seq
    &&& s_.msgs_accept_ok == s.msgs_accept_ok
    &&& s_.msgs_accept_ok_sender == s.msgs_accept_ok_sender
    &&& s_.msgs_commit == s.msgs_commit
    &&& s_.msgs_commit_cmd == s.msgs_commit_cmd
    &&& s_.msgs_commit_seq == s.msgs_commit_seq
}

/// Recover: Another replica takes over recovery of a stalled instance.
/// Bumps ballot number and re-enters PreAccepted to re-drive consensus.
pub open spec fn LRecover(
    s: LState, s_: LState, c: LConstants, new_ballot: int,
) -> bool {
    &&& s.phase is PreAccepted || s.phase is Accepted
    &&& new_ballot > s.ballot
    // State update: take over with higher ballot, send new PreAccept
    &&& s_.ballot == new_ballot
    &&& s_.phase is PreAccepted
    &&& s_.cmd == s.cmd
    &&& s_.seq == s.seq
    &&& s_.dep_count == 0
    &&& s_.is_leader == true
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
    &&& s_.preaccept_senders == Set::<int>::empty().insert(c.my_id)
    &&& s_.accept_senders == Set::<int>::empty()
    &&& s_.has_conflict == false
    &&& s_.max_resp_seq == 0
    // Send PreAccept with new ballot
    &&& s_.msgs_preaccept == true
    &&& s_.msgs_preaccept_ballot == new_ballot
    &&& s_.msgs_preaccept_cmd == s.cmd
    &&& s_.msgs_preaccept_seq == s.seq
    // Clear other messages
    &&& s_.msgs_preaccept_ok == false
    &&& s_.msgs_preaccept_ok_sender == 0
    &&& s_.msgs_preaccept_ok_seq == 0
    &&& s_.msgs_preaccept_ok_conflict == false
    &&& s_.msgs_accept == false
    &&& s_.msgs_accept_ballot == 0
    &&& s_.msgs_accept_cmd == 0
    &&& s_.msgs_accept_seq == 0
    &&& s_.msgs_accept_ok == false
    &&& s_.msgs_accept_ok_sender == 0
    &&& s_.msgs_commit == false
    &&& s_.msgs_commit_cmd == 0
    &&& s_.msgs_commit_seq == 0
}

/// NewInstance: After executing, reset to accept a new command.
pub open spec fn LNewInstance(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is Executed
    // State update: reset to empty for next instance
    &&& s_.ballot == s.ballot
    &&& s_.phase is Empty
    &&& s_.cmd == 0
    &&& s_.seq == 0
    &&& s_.dep_count == 0
    &&& s_.is_leader == false
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
    &&& s_.preaccept_senders == Set::<int>::empty()
    &&& s_.accept_senders == Set::<int>::empty()
    &&& s_.has_conflict == false
    &&& s_.max_resp_seq == 0
    &&& s_.msgs_preaccept == false
    &&& s_.msgs_preaccept_ballot == 0
    &&& s_.msgs_preaccept_cmd == 0
    &&& s_.msgs_preaccept_seq == 0
    &&& s_.msgs_preaccept_ok == false
    &&& s_.msgs_preaccept_ok_sender == 0
    &&& s_.msgs_preaccept_ok_seq == 0
    &&& s_.msgs_preaccept_ok_conflict == false
    &&& s_.msgs_accept == false
    &&& s_.msgs_accept_ballot == 0
    &&& s_.msgs_accept_cmd == 0
    &&& s_.msgs_accept_seq == 0
    &&& s_.msgs_accept_ok == false
    &&& s_.msgs_accept_ok_sender == 0
    &&& s_.msgs_commit == false
    &&& s_.msgs_commit_cmd == 0
    &&& s_.msgs_commit_seq == 0
}

/// Next-state relation: disjunction of all transitions.
pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
    ||| exists |value: int| LPropose(s, s_, c, value)
    ||| exists |local_conflict: bool, local_seq: int| LSendPreAcceptOk(s, s_, c, local_conflict, local_seq)
    ||| LReceivePreAcceptOk(s, s_, c)
    ||| LFastCommit(s, s_, c)
    ||| LStartAccept(s, s_, c)
    ||| LSendAcceptOk(s, s_, c)
    ||| LReceiveAcceptOk(s, s_, c)
    ||| LSlowCommit(s, s_, c)
    ||| LExecute(s, s_, c)
    ||| exists |new_ballot: int| LRecover(s, s_, c, new_ballot)
    ||| LNewInstance(s, s_, c)
}

} // verus!
