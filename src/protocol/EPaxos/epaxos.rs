/// Simplified EPaxos (Egalitarian Paxos) protocol.
///
/// Models the key EPaxos innovations from a single replica's perspective:
/// 1. Any replica can propose (leaderless)
/// 2. Fast path (1 RTT): propose with deps, commit if quorum agrees
/// 3. Slow path (2 RTT): on conflict, run Paxos-like accept phase
/// 4. Dependency tracking via sequence numbers
/// 5. Execution after all dependencies are committed
///
/// Transitions:
/// - Propose: Replica proposes a new command, enters PreAccepted
/// - ReceivePreAccept: Accumulate fast-path acks; track conflicts
/// - FastCommit: If fast quorum agrees (no conflicts), commit directly
/// - StartAccept: If conflict detected, begin slow path accept phase
/// - ReceiveAccept: Accumulate slow-path acks
/// - SlowCommit: If quorum acks in accept phase, commit
/// - Execute: Execute a committed command once deps are ready
/// - Recover: Recover an instance from a failed leader
use vstd::prelude::*;
use crate::protocol::EPaxos::types::*;

verus! {

/// Initial state: empty instance slot, no commands
pub open spec fn LInit(s: LState, c: LConstants) -> bool {
    &&& s.ballot == 0
    &&& s.phase is Empty
    &&& s.cmd == 0
    &&& s.seq == 0
    &&& s.dep_count == 0
    &&& s.preaccept_count == 0
    &&& s.accept_count == 0
    &&& s.is_leader == false
    &&& s.committed_count == 0
    &&& s.executed_count == 0
    &&& c.num_replicas >= 3
    &&& c.quorum_size > 0
    &&& c.fast_quorum_size >= c.quorum_size
}

/// Propose: This replica proposes a new command (any replica can do this).
/// Assigns a sequence number based on committed count and enters PreAccepted.
/// This is the key EPaxos innovation -- no designated leader needed.
pub open spec fn LPropose(
    s: LState, s_: LState, c: LConstants, value: int,
) -> bool {
    &&& s.phase is Empty
    // State update: enter pre-accept phase as leader
    &&& s_.ballot == s.ballot
    &&& s_.phase is PreAccepted
    &&& s_.cmd == value
    &&& s_.seq == s.committed_count + 1
    &&& s_.dep_count == 0
    &&& s_.preaccept_count == 1
    &&& s_.accept_count == 0
    &&& s_.is_leader == true
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
}

/// ReceivePreAccept: Receive a pre-accept response from another replica.
/// If the responder reports a dependency conflict, increment dep_count.
pub open spec fn LReceivePreAccept(
    s: LState, s_: LState, c: LConstants, has_conflict: bool,
) -> bool {
    &&& s.phase is PreAccepted
    &&& s.is_leader == true
    &&& s.preaccept_count < c.num_replicas
    // State update: accumulate response
    &&& s_.ballot == s.ballot
    &&& s_.phase == s.phase
    &&& s_.cmd == s.cmd
    &&& s_.seq == (if has_conflict && s.seq <= s.committed_count { s.seq + 1 } else { s.seq })
    &&& s_.dep_count == (if has_conflict { s.dep_count + 1 } else { s.dep_count })
    &&& s_.preaccept_count == s.preaccept_count + 1
    &&& s_.accept_count == s.accept_count
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
}

/// FastCommit: Commit on the fast path when the fast quorum agrees (no conflicts).
/// This is EPaxos's 1-RTT fast path -- if all responders agree on deps, commit directly.
pub open spec fn LFastCommit(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is PreAccepted
    &&& s.is_leader == true
    &&& s.preaccept_count >= c.fast_quorum_size
    &&& s.dep_count == 0
    // State update: commit directly
    &&& s_.ballot == s.ballot
    &&& s_.phase is Committed
    &&& s_.cmd == s.cmd
    &&& s_.seq == s.seq
    &&& s_.dep_count == s.dep_count
    &&& s_.preaccept_count == s.preaccept_count
    &&& s_.accept_count == s.accept_count
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count + 1
    &&& s_.executed_count == s.executed_count
}

/// StartAccept: Begin the slow path (Paxos-like accept phase) when conflicts detected.
/// This happens when some responders disagree on dependencies during pre-accept.
pub open spec fn LStartAccept(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is PreAccepted
    &&& s.is_leader == true
    &&& s.preaccept_count >= c.quorum_size
    &&& s.dep_count > 0
    // State update: enter accept phase with resolved deps
    &&& s_.ballot == s.ballot
    &&& s_.phase is Accepted
    &&& s_.cmd == s.cmd
    &&& s_.seq == s.seq
    &&& s_.dep_count == s.dep_count
    &&& s_.preaccept_count == s.preaccept_count
    &&& s_.accept_count == 1
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
}

/// ReceiveAccept: Receive an accept response during the slow path.
pub open spec fn LReceiveAccept(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is Accepted
    &&& s.is_leader == true
    &&& s.accept_count < c.num_replicas
    // State update: accumulate accept
    &&& s_.ballot == s.ballot
    &&& s_.phase == s.phase
    &&& s_.cmd == s.cmd
    &&& s_.seq == s.seq
    &&& s_.dep_count == s.dep_count
    &&& s_.preaccept_count == s.preaccept_count
    &&& s_.accept_count == s.accept_count + 1
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
}

/// SlowCommit: Commit on the slow path when a quorum accepts.
/// This is EPaxos's 2-RTT path -- used when there were dependency conflicts.
pub open spec fn LSlowCommit(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is Accepted
    &&& s.is_leader == true
    &&& s.accept_count >= c.quorum_size
    // State update: commit
    &&& s_.ballot == s.ballot
    &&& s_.phase is Committed
    &&& s_.cmd == s.cmd
    &&& s_.seq == s.seq
    &&& s_.dep_count == s.dep_count
    &&& s_.preaccept_count == s.preaccept_count
    &&& s_.accept_count == s.accept_count
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count + 1
    &&& s_.executed_count == s.executed_count
}

/// Execute: Execute a committed command.
/// In full EPaxos, this requires checking that all transitive dependencies are
/// also committed. Simplified here: execute any committed instance.
pub open spec fn LExecute(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.phase is Committed
    // State update: mark as executed
    &&& s_.ballot == s.ballot
    &&& s_.phase is Executed
    &&& s_.cmd == s.cmd
    &&& s_.seq == s.seq
    &&& s_.dep_count == s.dep_count
    &&& s_.preaccept_count == s.preaccept_count
    &&& s_.accept_count == s.accept_count
    &&& s_.is_leader == s.is_leader
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count + 1
}

/// Recover: Another replica takes over recovery of a stalled instance.
/// Bumps ballot number and re-enters PreAccepted to re-drive consensus.
/// This models the EPaxos explicit-prepare (recovery) protocol.
pub open spec fn LRecover(
    s: LState, s_: LState, c: LConstants, new_ballot: int,
) -> bool {
    &&& s.phase is PreAccepted || s.phase is Accepted
    &&& new_ballot > s.ballot
    // State update: take over with higher ballot
    &&& s_.ballot == new_ballot
    &&& s_.phase is PreAccepted
    &&& s_.cmd == s.cmd
    &&& s_.seq == s.seq
    &&& s_.dep_count == 0
    &&& s_.preaccept_count == 1
    &&& s_.accept_count == 0
    &&& s_.is_leader == true
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
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
    &&& s_.preaccept_count == 0
    &&& s_.accept_count == 0
    &&& s_.is_leader == false
    &&& s_.committed_count == s.committed_count
    &&& s_.executed_count == s.executed_count
}

/// Next-state relation: disjunction of all transitions.
pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
    ||| exists |value: int| LPropose(s, s_, c, value)
    ||| exists |has_conflict: bool| LReceivePreAccept(s, s_, c, has_conflict)
    ||| LFastCommit(s, s_, c)
    ||| LStartAccept(s, s_, c)
    ||| LReceiveAccept(s, s_, c)
    ||| LSlowCommit(s, s_, c)
    ||| LExecute(s, s_, c)
    ||| exists |new_ballot: int| LRecover(s, s_, c, new_ballot)
    ||| LNewInstance(s, s_, c)
}

} // verus!
