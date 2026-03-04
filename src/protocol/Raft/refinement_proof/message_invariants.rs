use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use vstd::prelude::*;
use vstd::{map::*, seq::*, set::*};

verus! {

    // =========================================================================
    // Message Invariant 1: Sender Integrity
    // =========================================================================
    //
    // Every packet's src field matches the identity field in the message.
    // This follows from the network model: src == server_id, and the message
    // fields (candidate, voter, leader, follower) are set to c.my_id == server_id.

    pub open spec fn SenderIntegrity(ds: RaftDistributedState) -> bool {
        forall |p: LRaftPacket| ds.network.contains(p) ==> {
            &&& 0 <= p.src < ds.num_servers
            &&& 0 <= p.dst < ds.num_servers
            &&& match p.msg {
                LRaftMessage::RequestVote { candidate, .. } => p.src == candidate,
                LRaftMessage::VoteResponse { voter, .. } => p.src == voter,
                LRaftMessage::AppendEntries { leader, .. } => p.src == leader,
                LRaftMessage::AppendResponse { follower, .. } => p.src == follower,
            }
        }
    }

    // =========================================================================
    // Message Invariant 2: Vote Response Integrity
    // =========================================================================
    //
    // If a VoteResponse{granted: true, term: t, voter: v} packet is in the
    // network going to destination d, then:
    // - v actually has voted (has_voted == true, voted_for == d at term t)
    // - OR v has moved to a term higher than t
    //
    // The `voted_for == p.dst` clause uses the routing constraint in the
    // network model: VoteResponse packets are routed back to the candidate
    // that sent the RequestVote (received_from == Some(pkt.src)).

    pub open spec fn VoteResponseIntegrity(ds: RaftDistributedState) -> bool {
        forall |p: LRaftPacket| ds.network.contains(p) ==>
            match p.msg {
                LRaftMessage::VoteResponse { term: t, granted, voter: v } => {
                    granted ==> {
                        &&& 0 <= v < ds.num_servers
                        &&& p.src == v
                        &&& (ds.server_states[v].current_term > t
                            || (ds.server_states[v].current_term == t
                                && ds.server_states[v].has_voted
                                && ds.server_states[v].voted_for == p.dst))
                    }
                }
                _ => true,
            }
    }

    // =========================================================================
    // Message Invariant 3: AppendEntries Integrity
    // =========================================================================
    //
    // If an AppendEntries{term: t, leader: l, ...} packet is in the network,
    // then the leader l's log is consistent with the message content.
    //
    // This relies on two properties:
    // 1. At send time, the leader's log matches the message (requires
    //    strengthening LSendAppendEntries — deferred to Phase 34.3).
    // 2. After send, log entries are preserved (LogAppendOnly).
    //
    // For now we define the full invariant. Its inductive proof will use
    // assume() until LSendAppendEntries is strengthened.

    pub open spec fn AppendEntriesIntegrity(ds: RaftDistributedState) -> bool {
        forall |p: LRaftPacket| ds.network.contains(p) ==>
            match p.msg {
                LRaftMessage::AppendEntries { term: t, leader: l, prev_index,
                                               prev_term, value, has_entry, .. } => {
                    &&& 0 <= l < ds.num_servers
                    &&& p.src == l
                    // Leader's current term >= message term
                    &&& ds.server_states[l].current_term >= t
                    // Leader's log still contains the referenced entries
                    &&& ds.server_states[l].log.len() >= prev_index
                            + (if has_entry { 1int } else { 0int })
                    // prev_term matches leader's log at prev_index
                    &&& (prev_index > 0 ==>
                        ds.server_states[l].log[prev_index - 1].term == prev_term)
                    // The entry value matches leader's log
                    &&& (has_entry ==>
                        ds.server_states[l].log[prev_index].value == value)
                }
                _ => true,
            }
    }

    // =========================================================================
    // Message Invariant 4: One Vote Per Term in Network
    // =========================================================================
    //
    // Each server votes at most once per term. If two VoteResponse{granted: true}
    // packets have the same voter and term, they have the same destination.
    // This follows from the has_voted guard in LGrantVote: a server only sends
    // VoteResponse{granted: true} when !has_voted (first vote in that term).

    pub open spec fn OneVotePerTermInNetwork(ds: RaftDistributedState) -> bool {
        forall |p1: LRaftPacket, p2: LRaftPacket|
            ds.network.contains(p1) && ds.network.contains(p2) ==>
            match p1.msg {
                LRaftMessage::VoteResponse { term: t1, granted: g1, voter: v1 } =>
                    match p2.msg {
                        LRaftMessage::VoteResponse { term: t2, granted: g2, voter: v2 } =>
                            (g1 && g2 && v1 == v2 && t1 == t2) ==> p1.dst == p2.dst,
                        _ => true,
                    },
                _ => true,
            }
    }

    // =========================================================================
    // Step Property: Log Append Only
    // =========================================================================
    //
    // Logs only grow by appending: existing entries are never modified.
    // This is a property of transitions (ds -> ds_), not a state invariant.
    // NOT included in RaftSafetyInvariant.
    //
    // The current Raft spec uses `s.log.push(...)` for all log modifications
    // (LClientRequest, LFollowerAppendEntries), so there is no log truncation.

    pub open spec fn LogAppendOnly(ds: RaftDistributedState, ds_: RaftDistributedState) -> bool {
        forall |i: int| 0 <= i < ds.num_servers ==> {
            &&& ds_.server_states[i].log.len() >= ds.server_states[i].log.len()
            &&& (forall |k: int| #![trigger ds.server_states[i].log[k]]
                0 <= k < ds.server_states[i].log.len() ==>
                ds_.server_states[i].log[k] == ds.server_states[i].log[k])
        }
    }
}
