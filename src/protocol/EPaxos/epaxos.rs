use crate::protocol::EPaxos::types::*;
/// EPaxos (Egalitarian Paxos) protocol.
///
/// Models the key EPaxos innovations from a single replica's perspective:
/// 1. Any replica can propose (leaderless)
/// 2. Fast path (1 RTT): propose with deps, commit if quorum agrees
/// 3. Slow path (2 RTT): on conflict, run Paxos-like accept phase
/// 4. Set-based quorum tracking for pre-accept and accept phases
/// 5. Messages modeled as sent_packets output parameter
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
    &&& c.num_replicas >= 3
    &&& c.quorum_size > 0
    &&& c.fast_quorum_size >= c.quorum_size
}

/// Propose: This replica proposes a new command (any replica can do this).
/// Assigns a sequence number and enters PreAccepted. Sends PreAccept message.
pub open spec fn LPropose(
    s: LState, s_: LState, c: LConstants, value: int, sent_packets: Seq<LEPaxosMessage>,
) -> bool {
    &&& s.phase is Empty
    // State update: enter pre-accept phase as leader
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
    &&& sent_packets == seq![LEPaxosMessage::PreAccept { ballot: s.ballot, cmd: value, seq: s.committed_count + 1 }]
}

/// SendPreAcceptOk: Non-leader replica responds to a PreAccept message.
/// Checks for local conflicts and reports back.
pub open spec fn LSendPreAcceptOk(
    s: LState, s_: LState, c: LConstants, local_conflict: bool, local_seq: int, sent_packets: Seq<LEPaxosMessage>,
) -> bool {
    // Send PreAcceptOk response
    &&& sent_packets == seq![LEPaxosMessage::PreAcceptOk { sender: c.my_id, seq: local_seq, conflict: local_conflict }]
    // Frame: preserve all state
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
}

/// ReceivePreAcceptOk: Leader receives a PreAcceptOk response.
/// Tracks sender in set, updates conflict and max seq info.
pub open spec fn LReceivePreAcceptOk(
    s: LState, s_: LState, c: LConstants, pa_sender: int, pa_seq: int, pa_conflict: bool, sent_packets: Seq<LEPaxosMessage>,
) -> bool {
    &&& s.phase is PreAccepted
    &&& s.is_leader == true
    &&& !s.preaccept_senders.contains(pa_sender)
    // State update: accumulate response
    &&& s_.preaccept_senders == s.preaccept_senders.insert(pa_sender)
    &&& s_.has_conflict == (if pa_conflict { true } else { s.has_conflict })
    &&& s_.dep_count == (if pa_conflict { s.dep_count + 1 } else { s.dep_count })
    &&& s_.max_resp_seq == (if pa_seq > s.max_resp_seq { pa_seq } else { s.max_resp_seq })
    &&& s_.seq == (if pa_seq > s.seq { pa_seq } else { s.seq })
    // No messages sent
    &&& sent_packets == Seq::<LEPaxosMessage>::empty()
    // Frame
    &&& s_.ballot == s.ballot
    &&& s_.phase == s.phase
    &&& s_.cmd == s.cmd
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
    &&& s_.accept_senders == s.accept_senders
}

/// FastCommit: Commit on the fast path when the fast quorum agrees (no conflicts).
/// This is EPaxos's 1-RTT fast path. Uses Set::len() for quorum check.
pub open spec fn LFastCommit(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LEPaxosMessage>) -> bool {
    &&& s.phase is PreAccepted
    &&& s.is_leader == true
    &&& s.preaccept_senders.len() >= c.fast_quorum_size
    &&& s.has_conflict == false
    // State update: commit directly
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
    &&& sent_packets == seq![LEPaxosMessage::Commit { cmd: s.cmd, seq: s.seq }]
}

/// StartAccept: Begin the slow path (Paxos-like accept phase) when conflicts detected.
/// Uses Set::len() for quorum check.
pub open spec fn LStartAccept(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LEPaxosMessage>) -> bool {
    &&& s.phase is PreAccepted
    &&& s.is_leader == true
    &&& s.preaccept_senders.len() >= c.quorum_size
    &&& s.has_conflict == true
    // State update: enter accept phase
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
    &&& sent_packets == seq![LEPaxosMessage::Accept { ballot: s.ballot, cmd: s.cmd, seq: s.seq }]
}

/// SendAcceptOk: Replica responds to an Accept message.
pub open spec fn LSendAcceptOk(
    s: LState, s_: LState, c: LConstants, sent_packets: Seq<LEPaxosMessage>,
) -> bool {
    // Send AcceptOk response
    &&& sent_packets == seq![LEPaxosMessage::AcceptOk { sender: c.my_id }]
    // Frame: preserve all state
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
}

/// ReceiveAcceptOk: Leader receives an AcceptOk response during the slow path.
/// Tracks sender in set.
pub open spec fn LReceiveAcceptOk(
    s: LState, s_: LState, c: LConstants, ao_sender: int, sent_packets: Seq<LEPaxosMessage>,
) -> bool {
    &&& s.phase is Accepted
    &&& s.is_leader == true
    &&& !s.accept_senders.contains(ao_sender)
    // State update: accumulate accept
    &&& s_.accept_senders == s.accept_senders.insert(ao_sender)
    // No messages sent
    &&& sent_packets == Seq::<LEPaxosMessage>::empty()
    // Frame
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
}

/// SlowCommit: Commit on the slow path when a quorum accepts.
/// Uses Set::len() for quorum check.
pub open spec fn LSlowCommit(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LEPaxosMessage>) -> bool {
    &&& s.phase is Accepted
    &&& s.is_leader == true
    &&& s.accept_senders.len() >= c.quorum_size
    // State update: commit
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
    &&& sent_packets == seq![LEPaxosMessage::Commit { cmd: s.cmd, seq: s.seq }]
}

/// Execute: Execute a committed command.
/// If this replica is the command leader, send ClientReply to the requesting client.
pub open spec fn LExecute(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LEPaxosMessage>) -> bool {
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
    // Send ClientReply with the executed command value
    &&& sent_packets == seq![LEPaxosMessage::ClientReply { cmd: s.cmd }]
}

/// Recover: Another replica takes over recovery of a stalled instance.
/// Bumps ballot number and re-enters PreAccepted to re-drive consensus.
pub open spec fn LRecover(
    s: LState, s_: LState, c: LConstants, new_ballot: int, sent_packets: Seq<LEPaxosMessage>,
) -> bool {
    &&& s.phase is PreAccepted || s.phase is Accepted
    &&& new_ballot > s.ballot
    // State update: take over with higher ballot
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
    &&& sent_packets == seq![LEPaxosMessage::PreAccept { ballot: new_ballot, cmd: s.cmd, seq: s.seq }]
}

/// NewInstance: After executing, reset to accept a new command.
pub open spec fn LNewInstance(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LEPaxosMessage>) -> bool {
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
    // No messages sent
    &&& sent_packets == Seq::<LEPaxosMessage>::empty()
}

/// Next-state relation: disjunction of all transitions.
pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
    ||| exists |value: int, sent_packets: Seq<LEPaxosMessage>| LPropose(s, s_, c, value, sent_packets)
    ||| exists |local_conflict: bool, local_seq: int, sent_packets: Seq<LEPaxosMessage>| LSendPreAcceptOk(s, s_, c, local_conflict, local_seq, sent_packets)
    ||| exists |pa_sender: int, pa_seq: int, pa_conflict: bool, sent_packets: Seq<LEPaxosMessage>| LReceivePreAcceptOk(s, s_, c, pa_sender, pa_seq, pa_conflict, sent_packets)
    ||| exists |sent_packets: Seq<LEPaxosMessage>| LFastCommit(s, s_, c, sent_packets)
    ||| exists |sent_packets: Seq<LEPaxosMessage>| LStartAccept(s, s_, c, sent_packets)
    ||| exists |sent_packets: Seq<LEPaxosMessage>| LSendAcceptOk(s, s_, c, sent_packets)
    ||| exists |ao_sender: int, sent_packets: Seq<LEPaxosMessage>| LReceiveAcceptOk(s, s_, c, ao_sender, sent_packets)
    ||| exists |sent_packets: Seq<LEPaxosMessage>| LSlowCommit(s, s_, c, sent_packets)
    ||| exists |sent_packets: Seq<LEPaxosMessage>| LExecute(s, s_, c, sent_packets)
    ||| exists |new_ballot: int, sent_packets: Seq<LEPaxosMessage>| LRecover(s, s_, c, new_ballot, sent_packets)
    ||| exists |sent_packets: Seq<LEPaxosMessage>| LNewInstance(s, s_, c, sent_packets)
}

} // verus!
