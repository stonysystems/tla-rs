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
                LRaftMessage::VoteResponse { term: t, granted, voter: v, .. } => {
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
    // Message Invariant 2b: VoteResponse -> RequestVote provenance
    // =========================================================================
    //
    // Every granted VoteResponse packet in the network has a matching
    // RequestVote packet in the network from the candidate to the voter
    // for the same term.
    //
    // This is a packet-level provenance hook needed when we later connect
    // overlap-voter witnesses back to request-vote context.

    pub open spec fn VoteResponseHasRequestVote(ds: RaftDistributedState) -> bool {
        forall |p: LRaftPacket| ds.network.contains(p) ==>
            match p.msg {
                LRaftMessage::VoteResponse { term: t, granted, voter: v, .. } => {
                    granted ==> exists |req: LRaftPacket| {
                        &&& ds.network.contains(req)
                        &&& req.src == p.dst
                        &&& req.dst == v
                        &&& req.msg matches LRaftMessage::RequestVote {
                            term,
                            candidate,
                            last_log_index: _,
                            last_log_term: _,
                        }
                        &&& term == t
                        &&& candidate == p.dst
                    }
                }
                _ => true,
            }
    }

    // =========================================================================
    // Message Invariant 2c: RequestVote summary stays valid for same term
    // =========================================================================
    //
    // For any in-network RequestVote packet sent by candidate d at term t,
    // if d is still at that same term, then d's current log still contains
    // the packet's referenced last-log summary index/term.
    //
    // Intuition:
    // - At send time (LTimeout), RequestVote carries d's exact log summary.
    // - Logs are append-only (old prefix preserved), so that summary remains
    //   valid while d stays in the same election term.

    pub open spec fn RequestVoteSummaryStillValidAtSameTerm(ds: RaftDistributedState) -> bool {
        forall |p: LRaftPacket| ds.network.contains(p) ==>
            match p.msg {
                LRaftMessage::RequestVote {
                    term: t,
                    candidate: d,
                    last_log_index: last_idx,
                    last_log_term: last_term,
                } => {
                    0 <= d < ds.num_servers ==> (
                        ds.server_states[d].current_term == t ==> {
                            &&& 0 <= last_idx <= ds.server_states[d].log.len()
                            &&& (last_idx == 0 ==> last_term == 0)
                            &&& (last_idx > 0 ==> ds.server_states[d].log[last_idx - 1].term == last_term)
                        }
                    )
                }
                _ => true,
            }
    }

    // =========================================================================
    // Message Invariant 2d: VoteResponse summary stays valid at/above term
    // =========================================================================
    //
    // For any in-network granted VoteResponse packet from voter v at term t,
    // if v is currently at term >= t, then v's current log still contains the
    // vote-time log summary embedded in the packet.
    //
    // Intuition:
    // - At send time (LGrantVote), VoteResponse carries v's exact log summary.
    // - Logs are append-only (old prefix preserved), so that summary remains
    //   valid even if v has moved to a higher term.

    pub open spec fn VoteResponseSummaryStillValidAtOrAboveTerm(ds: RaftDistributedState) -> bool {
        forall |p: LRaftPacket| ds.network.contains(p) ==>
            match p.msg {
                LRaftMessage::VoteResponse {
                    term: t,
                    granted,
                    voter: v,
                    voter_last_log_index: last_idx,
                    voter_last_log_term: last_term,
                } => {
                    granted && 0 <= v < ds.num_servers && ds.server_states[v].current_term >= t ==> {
                        &&& 0 <= last_idx <= ds.server_states[v].log.len()
                        &&& (last_idx == 0 ==> last_term == 0)
                        &&& (last_idx > 0 ==> ds.server_states[v].log[last_idx - 1].term == last_term)
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
        forall |p: LRaftPacket| #![trigger ds.network.contains(p)] ds.network.contains(p) ==>
            match p.msg {
                LRaftMessage::AppendEntries { term: t, leader: l, prev_index,
                                               prev_term, value, has_entry, .. } => {
                    &&& 0 <= l < ds.num_servers
                    &&& p.src == l
                    &&& prev_index >= 0
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
                    // The entry's term in leader's log matches the message term
                    // (leader only sends entries from current term)
                    &&& (has_entry ==>
                        ds.server_states[l].log[prev_index].term == t)
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
                LRaftMessage::VoteResponse { term: t1, granted: g1, voter: v1, .. } =>
                    match p2.msg {
                        LRaftMessage::VoteResponse { term: t2, granted: g2, voter: v2, .. } =>
                            (g1 && g2 && v1 == v2 && t1 == t2) ==> p1.dst == p2.dst,
                        _ => true,
                    },
                _ => true,
            }
    }

    // =========================================================================
    // Message Invariant 5: Vote Log Len Covers Network
    // =========================================================================
    //
    // Every granted VoteResponse packet in the network from voter v at term t
    // has (v, t) recorded in the ghost map vote_log_len.
    // This follows from the ghost state update in RaftServerStepWithNetwork:
    // when LGrantVote sends VoteResponse{granted: true, term: t, voter: v},
    // (v, t) is added to vote_log_len.

    pub open spec fn VoteLogLenCoversNetwork(ds: RaftDistributedState) -> bool {
        forall |p: LRaftPacket| ds.network.contains(p) ==>
            match p.msg {
                LRaftMessage::VoteResponse { term: t, granted, voter: v, .. } => {
                    granted ==> {
                        &&& ds.vote_log_len.dom().contains((v, t))
                    }
                }
                _ => true,
            }
    }

    // =========================================================================
    // Message Invariant 6: Vote Log Len Bounded
    // =========================================================================
    //
    // For every (v, t) in vote_log_len, the recorded length is bounded by the
    // voter's current log length: vote_log_len[(v, t)] <= server_states[v].log.len().
    // This follows from LogAppendOnly: the voter's log only grows after voting.

    pub open spec fn VoteLogLenBounded(ds: RaftDistributedState) -> bool {
        forall |v: int, t: int| ds.vote_log_len.dom().contains((v, t)) ==> {
            &&& 0 <= v < ds.num_servers
            &&& 0 <= ds.vote_log_len[(v, t)]
            &&& ds.vote_log_len[(v, t)] <= ds.server_states[v].log.len()
            &&& ds.server_states[v].current_term >= t
        }
    }

    // =========================================================================
    // Message Invariant 6b: Vote Log Len Entry Term Bound
    // =========================================================================
    //
    // For every (v, t) in vote_log_len, all log entries at indices >= the
    // recorded vote-time length have term >= t.
    //
    // Intuition: when server v grants a vote at term t, vote_log_len records
    // v's log length L. After that point, v's current_term >= t (terms only
    // increase). Any new log entry added via LClientRequest or
    // LFollowerAppendEntries has term >= current_term >= t. So entries at
    // indices >= L all have term >= t.

    pub open spec fn VoteLogLenEntryTermBound(ds: RaftDistributedState) -> bool {
        forall |p: (int, int), i: int|
            #![trigger ds.server_states[p.0].log[i], ds.vote_log_len.dom().contains(p)]
            ds.vote_log_len.dom().contains(p)
            && 0 <= p.0 < ds.num_servers
            && ds.vote_log_len[p] <= i
            && i < ds.server_states[p.0].log.len()
        ==> ds.server_states[p.0].log[i].term >= p.1
    }

    // =========================================================================
    // Message Invariant 7: Vote Granted implies Log Up-To-Date at Vote Time
    // =========================================================================
    //
    // For every pair of (granted VoteResponse, matching RequestVote) packets
    // where the voter's log length at vote time is recorded in vote_log_len:
    // the candidate's last-log parameters satisfy log_up_to_date against the
    // voter's reconstructed vote-time log (prefix up to vote_log_len[(v, t)]).
    //
    // Restricted to the specific candidate the voter voted for, identified by
    // vote_pkt.dst == req.src (VoteResponse destination = RequestVote sender).
    //
    // Since logs are append-only, the voter's current log preserves the vote-time
    // prefix, so we can express the vote-time last-log-term using current state:
    //   vote_time_last_term = if L == 0 { 0 } else { voter.log[L-1].term }
    // where L = vote_log_len[(v, t)].
    //
    // Proof intuition:
    // - At vote time, LHandleRequestVoteMsg checked log_up_to_date before granting.
    // - The voter's log prefix up to L is preserved (LogAppendOnly), so the
    //   vote-time last-log-term is still readable from the current state.
    // - The RequestVote packet parameters are immutable in-network.

    pub open spec fn VoteGrantedLogUpToDateAtVoteTime(ds: RaftDistributedState) -> bool {
        forall |vote_pkt: LRaftPacket, req: LRaftPacket|
            #![trigger ds.network.contains(vote_pkt), ds.network.contains(req)]
            ds.network.contains(vote_pkt) && ds.network.contains(req)
            && (vote_pkt.msg is VoteResponse)
            && vote_pkt.msg->VoteResponse_granted
            && (req.msg is RequestVote)
            && vote_pkt.msg->VoteResponse_term == req.msg->RequestVote_term
            && vote_pkt.src == req.dst   // voter
            && vote_pkt.dst == req.src   // candidate
            && ds.vote_log_len.dom().contains(
                (vote_pkt.src, vote_pkt.msg->VoteResponse_term))
            && 0 <= vote_pkt.src < ds.num_servers
        ==> {
            let v = vote_pkt.src;
            let t = vote_pkt.msg->VoteResponse_term;
            let L = ds.vote_log_len[(v, t)];
            let voter_vote_time_last_term: int = if L == 0 {
                0int
            } else {
                ds.server_states[v].log[L - 1].term
            };
            let li = req.msg->RequestVote_last_log_index;
            let lt = req.msg->RequestVote_last_log_term;
            lt > voter_vote_time_last_term
                || (lt == voter_vote_time_last_term && li >= L)
        }
    }

    // =========================================================================
    // Message Invariant 8: Log Terms Monotonic
    // =========================================================================
    //
    // For every server, log entry terms are monotonically non-decreasing:
    //   forall j, k: 0 <= j <= k < log.len() ==> log[j].term <= log[k].term
    //
    // This holds because the simplified Raft spec only appends entries, and
    // every appended entry has term >= current_term at the time of the append:
    //   - LClientRequest: appends LLogEntry { term: s.current_term, .. }
    //   - LFollowerAppendEntries: appends LLogEntry { term: ae_term, .. }
    //     where ae_term >= s.current_term
    // Since current_term is monotonically non-decreasing and existing entries
    // are never modified (no log truncation), the last entry's term is always
    // >= the current_term at the time of the previous append, ensuring
    // monotonicity across the entire log.

    pub open spec fn LogTermsMonotonic(ds: RaftDistributedState) -> bool {
        forall |i: int, j: int, k: int|
            #![trigger ds.server_states[i].log[j], ds.server_states[i].log[k]]
            0 <= i < ds.num_servers
            && 0 <= j <= k
            && k < ds.server_states[i].log.len()
        ==> ds.server_states[i].log[j].term <= ds.server_states[i].log[k].term
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

    // =========================================================================
    // LogAppendOnly proof
    // =========================================================================

    /// Prove LogAppendOnly as a step property of RaftDistributedNext.
    /// Every LNext branch either preserves the log (frame) or pushes one entry.
    pub proof fn lemma_log_append_only(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            RaftDistributedNext(ds, ds_),
        ensures
            LogAppendOnly(ds, ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |sid: int| {
            &&& 0 <= sid < ds.num_servers
            &&& LNext(ds.server_states[sid], ds_.server_states[sid],
                       ds.server_constants[sid])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        assert forall |i: int| 0 <= i < ds.num_servers implies {
            &&& ds_.server_states[i].log.len() >= ds.server_states[i].log.len()
            &&& (forall |k: int| #![trigger ds.server_states[i].log[k]]
                0 <= k < ds.server_states[i].log.len() ==>
                ds_.server_states[i].log[k] == ds.server_states[i].log[k])
        } by {
            if i != server_id {
                // Non-stepping server: state unchanged
                assert(ds_.server_states[i] == ds.server_states[i]);
            }
            // For i == server_id: all LNext branches either keep s_.log == s.log
            // (frame conditions) or set s_.log == s.log.push(entry).
            // Seq::push preserves existing elements and extends length by 1.
        }
    }
}
