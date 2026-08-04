use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::refinement_proof::invariants::CommitIndexBounded;
use vstd::prelude::*;
use vstd::{map::*, seq::*, set::*};

verus! {

    // =========================================================================
    // Distributed Raft System State
    // =========================================================================

    /// The global state of a distributed Raft cluster.
    /// Models N servers each running the Raft protocol, plus a network of messages.
    pub struct RaftDistributedState {
        pub server_states: Seq<LState>,     // Per-server Raft state (indexed by server ID)
        pub server_constants: Seq<LConstants>, // Per-server constants
        pub network: Set<LRaftPacket>,      // Routed messages in transit
        pub num_servers: int,               // Number of servers in the cluster
        // Ghost state: maps (voter_id, vote_term) → voter's log length at vote time.
        // Used for stale-vote provenance in LeaderCompleteness proof (Phase 34.7).
        // Only meaningful for granted votes; populated by LGrantVote.
        pub vote_log_len: Map<(int, int), int>,
    }

    /// Well-formedness of the distributed state
    pub open spec fn WellFormedRaftDistributed(ds: RaftDistributedState) -> bool {
        &&& ds.num_servers > 0
        &&& ds.num_servers <= u64::MAX as int
        &&& ds.server_states.len() == ds.num_servers
        &&& ds.server_constants.len() == ds.num_servers
        &&& (forall |i: int| #![trigger ds.server_constants[i]] 0 <= i < ds.num_servers ==> {
            &&& ds.server_constants[i].my_id == i
            &&& ds.server_constants[i].quorum_size == ds.num_servers / 2 + 1
            &&& ds.server_constants[i].servers =~= Set::<int>::range(0, ds.num_servers)
        })
    }

    /// Distributed system initialization
    pub open spec fn RaftDistributedInit(ds: RaftDistributedState) -> bool {
        &&& WellFormedRaftDistributed(ds)
        &&& (forall |i: int| #![trigger ds.server_states[i]] #![trigger ds.server_constants[i]] 0 <= i < ds.num_servers ==>
            LInit(ds.server_states[i], ds.server_constants[i]))
        &&& ds.network == Set::<LRaftPacket>::empty()
        &&& ds.vote_log_len == Map::<(int, int), int>::empty()
    }

    /// Helper: which action branch was taken, producing the given sent_packets.
    /// `received_from` is None for local/sending actions, Some(pkt.src) for
    /// message-handling actions, enabling response routing constraints.
    pub open spec fn RaftActionProduces(
        ds: RaftDistributedState, server_id: int,
        s: LState, s_: LState, c: LConstants,
        sent_packets: Seq<LRaftMessage>,
        received_from: Option<int>,
    ) -> bool {
        {
            // (A) Local/sending actions — no message received from network
            ||| (received_from is None && LTimeout(s, s_, c, sent_packets))
            ||| (received_from is None && (exists |value: int| LClientRequest(s, s_, c, value, sent_packets)))
            ||| (received_from is None && (exists |follower: int, ev: int, pli: int, plt: int, he: bool|
                    LSendAppendEntries(s, s_, c, follower, ev, pli, plt, he, sent_packets)))
            ||| (received_from is None && (exists |nci: int| LTryAdvanceCommitIndex(s, s_, c, nci, sent_packets)))
            // (B) Message handling — received packet must be in network
            ||| (exists |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
                    &&& received_from == Some(pkt.src)
                    &&& ds.network.contains(pkt)
                    &&& pkt.dst == server_id
                    &&& LHandleMessage(s, s_, c, pkt.msg, sent_packets)
                })
        }
    }

    /// Server step with full network semantics: the stepping server produces
    /// sent_packets via an action, and new packets in the network correspond
    /// to those sent_packets wrapped with src == server_id.
    /// For message-handling actions, response packets are routed back to the
    /// sender of the received packet (received_from).
    pub open spec fn RaftServerStepWithNetwork(
        ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int,
    ) -> bool {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        exists |sent_packets: Seq<LRaftMessage>, received_from: Option<int>|
            #![trigger RaftActionProduces(ds, server_id, s, s_, c, sent_packets, received_from)]
        {
            // Action: which branch was taken
            &&& RaftActionProduces(ds, server_id, s, s_, c, sent_packets, received_from)
            // Network monotonicity: old packets preserved
            &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt) ==> ds_.network.contains(pkt))
            // New packets come from sent_packets with routing constraints
            &&& (forall |pkt: LRaftPacket| #![trigger ds_.network.contains(pkt)] #![trigger ds.network.contains(pkt)]
                ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                    &&& pkt.src == server_id
                    &&& 0 <= pkt.dst < ds.num_servers
                    &&& (exists |i: int| 0 <= i < sent_packets.len() && pkt.msg == sent_packets[i])
                    // Routing: message-handling responses go back to sender
                    &&& (match received_from {
                        Some(src) => pkt.dst == src,
                        None => true,
                    })
                })
            // Ghost state: vote_log_len tracks voter log length at vote time.
            // Old entries preserved (monotonic). New entry added when a granted
            // VoteResponse is sent: record (server_id, vote_term) → s.log.len().
            &&& (forall |v: int, t: int| #![trigger ds_.vote_log_len[(v, t)]] #![trigger ds.vote_log_len[(v, t)]] ds.vote_log_len.dom().contains((v, t))
                ==> ds_.vote_log_len.dom().contains((v, t))
                    && ds_.vote_log_len[(v, t)] == ds.vote_log_len[(v, t)])
            // Ghost state new-entry clause: either a granted VoteResponse was
            // sent and its provenance was recorded, or no granted VoteResponse was sent.
            &&& ({
                ||| (exists |vt: int| #![trigger ds_.vote_log_len.dom().contains((server_id, vt))] {
                    // A granted VoteResponse was sent at term vt
                    &&& (exists |i: int| #![trigger sent_packets[i]]
                        0 <= i < sent_packets.len()
                        && sent_packets[i] is VoteResponse
                        && sent_packets[i]->VoteResponse_term == vt
                        && sent_packets[i]->VoteResponse_granted
                        && sent_packets[i]->VoteResponse_voter == server_id)
                    // Record voter log length at vote time
                    &&& ds_.vote_log_len.dom().contains((server_id, vt))
                    &&& ds_.vote_log_len[(server_id, vt)] == s.log.len()
                    &&& ds_.vote_log_len
                        == ds.vote_log_len.insert(
                            (server_id, vt), s.log.len() as int)
                })
                ||| (
                    // No granted VoteResponse sent
                    !(exists |i: int| #![trigger sent_packets[i]]
                        0 <= i < sent_packets.len()
                        && (sent_packets[i] is VoteResponse)
                        && sent_packets[i]->VoteResponse_granted)
                    && ds_.vote_log_len == ds.vote_log_len
                )
            })
        }
    }

    /// Distributed system step: one server takes a step, with network routing.
    ///
    /// The server either:
    /// (A) performs a local/sending action (LTimeout, LClientRequest,
    ///     LSendAppendEntries, LTryAdvanceCommitIndex), or
    /// (B) handles a message received from the network (LHandleMessage),
    ///     where the received packet must exist in ds.network with dst == server_id.
    ///
    /// In both cases, the network is monotonic (messages are never removed),
    /// new messages are tagged with src == server_id, and new message payloads
    /// correspond to what the action produced.
    pub open spec fn RaftDistributedNext(ds: RaftDistributedState, ds_: RaftDistributedState) -> bool {
        &&& WellFormedRaftDistributed(ds)
        &&& WellFormedRaftDistributed(ds_)
        &&& ds_.num_servers == ds.num_servers
        &&& ds_.server_constants == ds.server_constants
        &&& exists |server_id: int| #![trigger ds.server_states[server_id]] {
            &&& 0 <= server_id < ds.num_servers
            // All other servers remain unchanged
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
            // Server action + network update with message correspondence
            &&& RaftServerStepWithNetwork(ds, ds_, server_id)
        }
    }

    /// RaftDistributedNext without network routing.
    /// Omits sent_packets and recv_from, keeping only the server step and frame.
    /// Every step of RaftDistributedNext implies a step of RaftDistributedNextLegacy.
    pub open spec fn RaftDistributedNextLegacy(ds: RaftDistributedState, ds_: RaftDistributedState) -> bool {
        &&& WellFormedRaftDistributed(ds)
        &&& WellFormedRaftDistributed(ds_)
        &&& ds_.num_servers == ds.num_servers
        &&& ds_.server_constants == ds.server_constants
        &&& exists |server_id: int| #![trigger ds.server_states[server_id]] #![trigger ds_.server_states[server_id]] #![trigger ds.server_constants[server_id]] {
            &&& 0 <= server_id < ds.num_servers
            // The chosen server transitions
            &&& LNext(ds.server_states[server_id], ds_.server_states[server_id], ds.server_constants[server_id])
            // All other servers remain unchanged
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        }
    }

    /// RaftDistributedNext implies the legacy version (without network routing).
    /// Each action category in RaftDistributedNext (LTimeout, LClientRequest,
    /// LSendAppendEntries, LTryAdvanceCommitIndex, LHandleMessage) directly
    /// corresponds to a branch of LNext. The same server_id witness works
    /// for both. Network update constraints and sent_packets are dropped.
    pub proof fn lemma_distributed_next_implies_legacy(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires RaftDistributedNext(ds, ds_)
        ensures RaftDistributedNextLegacy(ds, ds_)
    {
        // RaftDistributedNext provides exists |server_id, sent_packets| { action_categories && ... }
        // Each action category implies the corresponding LNext branch by existential weakening.
        // The frame condition is identical. Network constraints are simply dropped.
    }

    // =========================================================================
    // Behavior (sequence of distributed states)
    // =========================================================================

    pub type RaftBehavior = Seq<RaftDistributedState>;

    /// A valid Raft behavior: initial state followed by valid transitions
    pub open spec fn IsValidRaftBehavior(b: RaftBehavior) -> bool {
        &&& b.len() > 0
        &&& RaftDistributedInit(b[0])
        &&& (forall |i: int| #![trigger b[i]] 0 <= i < b.len() - 1 ==> RaftDistributedNext(b[i], b[i + 1]))
    }

    // =========================================================================
    // Abstract Sequential State Machine
    // =========================================================================

    /// The abstract state: a simple sequential log of committed values.
    /// This is what the Raft protocol "refines" — a single ordered log
    /// that all correct servers eventually agree on.
    pub struct RaftSystemState {
        pub committed_log: Seq<int>,        // Committed values in order
        pub server_ids: Set<int>,           // The set of server IDs (constant)
    }

    /// Abstract initial state: empty committed log
    pub open spec fn RaftSystemInit(rs: RaftSystemState, server_ids: Set<int>) -> bool {
        &&& rs.committed_log == Seq::<int>::empty()
        &&& rs.server_ids == server_ids
    }

    /// Abstract next step: extend the committed log by one or more entries.
    /// The existing prefix is preserved and at least one new entry is added.
    /// This allows a single distributed step to commit multiple log entries
    /// (e.g., when LAdvanceCommitIndex jumps commit_index by several entries).
    pub open spec fn RaftSystemNextAppendCommitted(
        rs: RaftSystemState,
        rs_: RaftSystemState,
    ) -> bool {
        &&& rs_.committed_log.len() > rs.committed_log.len()
        &&& (forall |k: int| #![trigger rs_.committed_log[k]]
             0 <= k < rs.committed_log.len() ==>
             rs_.committed_log[k] == rs.committed_log[k])
        &&& rs_.server_ids == rs.server_ids
    }

    /// Abstract next-state relation: either stutter or extend committed log
    pub open spec fn RaftSystemNext(rs: RaftSystemState, rs_: RaftSystemState) -> bool {
        ||| rs_ == rs   // stutter
        ||| RaftSystemNextAppendCommitted(rs, rs_)
    }

    // =========================================================================
    // Committed Log Extraction
    // =========================================================================

    /// Extract the committed log prefix from the distributed state.
    /// The committed log at step i is the longest prefix of any server's log
    /// such that every entry up to that point is backed by a majority of servers
    /// having that entry in their logs.
    ///
    /// Formally: entry at index k is committed if there exists a majority quorum Q
    /// such that for every server j in Q, j's log has length > k and j's log[k]
    /// matches the entry. The committed log is the longest prefix of such entries.
    ///
    /// For safety, we use the strongest definition: the committed log is the
    /// prefix up to the minimum commit_index among all servers that are leaders
    /// in the current term, or we look at majority agreement on log entries.
    ///
    /// Simplified definition: extract from the leader's commit_index.
    pub open spec fn GetCommittedLog(ds: RaftDistributedState) -> Seq<int> {
        // The committed log is derived from the longest commit prefix
        // backed by majority agreement. For well-behaved behaviors,
        // this equals the leader's log[0..commit_index].
        //
        // We define it as the log prefix up to the maximum commit_index
        // among all servers, projected through any server's log.
        // Safety invariants ensure all servers agree on committed entries.
        let max_commit = MaxCommitIndex(ds);
        if max_commit <= 0 {
            Seq::<int>::empty()
        } else {
            // Use the first server that has commit_index >= max_commit
            // (Safety invariants guarantee all such servers agree)
            let server_id = choose |id: int| #![trigger ds.server_states[id]] 0 <= id < ds.num_servers
                && ds.server_states[id].commit_index >= max_commit
                && ds.server_states[id].log.len() >= max_commit;
            ExtractLogValues(ds.server_states[server_id].log, max_commit)
        }
    }

    /// Maximum commit_index across all servers
    pub open spec fn MaxCommitIndex(ds: RaftDistributedState) -> int
        decreases ds.num_servers
    {
        if ds.num_servers <= 0 {
            0
        } else {
            let last_commit = ds.server_states[ds.num_servers - 1].commit_index;
            let rest_max = MaxCommitIndex(RaftDistributedState {
                server_states: ds.server_states.subrange(0, ds.num_servers - 1),
                server_constants: ds.server_constants.subrange(0, ds.num_servers - 1),
                network: ds.network,
                num_servers: ds.num_servers - 1,
                vote_log_len: ds.vote_log_len,
            });
            if last_commit > rest_max { last_commit } else { rest_max }
        }
    }

    /// Extract values from log entries up to a given length
    pub open spec fn ExtractLogValues(log: Seq<LLogEntry>, len: int) -> Seq<int>
        decreases len
    {
        if len <= 0 || len > log.len() {
            Seq::<int>::empty()
        } else if len == 1 {
            seq![log[0].value]
        } else {
            ExtractLogValues(log, len - 1).push(log[len - 1].value)
        }
    }

    // =========================================================================
    // Refinement Relation
    // =========================================================================

    /// The refinement relation: a distributed Raft state maps to an abstract state
    /// if the abstract committed log matches the committed log extracted from
    /// the distributed state.
    pub open spec fn RaftSystemRefinement(
        ds: RaftDistributedState,
        rs: RaftSystemState
    ) -> bool {
        &&& rs.server_ids =~= Set::<int>::range(0, ds.num_servers)
        &&& rs.committed_log == GetCommittedLog(ds)
    }

    /// Top-level correctness: the abstract behavior refines the distributed behavior
    pub open spec fn RaftSystemBehaviorRefinementCorrect(
        low_level_behavior: RaftBehavior,
        high_level_behavior: Seq<RaftSystemState>
    ) -> bool {
        &&& high_level_behavior.len() == low_level_behavior.len()
        &&& high_level_behavior.len() > 0
        &&& RaftSystemInit(
            high_level_behavior[0],
            Set::<int>::range(0, low_level_behavior[0].num_servers)
        )
        &&& (forall |i: int| #![trigger low_level_behavior[i]] 0 <= i < low_level_behavior.len() ==>
            RaftSystemRefinement(low_level_behavior[i], high_level_behavior[i]))
        &&& (forall |i: int| #![trigger high_level_behavior[i]] 0 <= i < high_level_behavior.len() - 1 ==>
            RaftSystemNext(high_level_behavior[i], high_level_behavior[i + 1]))
    }

    // =========================================================================
    // Helper: Seq-based max commit index (avoids WellFormedness constraints)
    // =========================================================================

    /// Maximum commit_index across a sequence of server states.
    /// This is equivalent to MaxCommitIndex but takes only the server_states
    /// sequence, avoiding the need for WellFormedRaftDistributed in proofs.
    pub open spec fn max_commit_index_seq(states: Seq<LState>) -> int
        decreases states.len()
    {
        if states.len() <= 0 {
            0
        } else {
            let last_commit = states[states.len() - 1].commit_index;
            let rest_max = max_commit_index_seq(states.subrange(0, states.len() - 1));
            if last_commit > rest_max { last_commit } else { rest_max }
        }
    }

    /// Equivalence: MaxCommitIndex(ds) == max_commit_index_seq(ds.server_states)
    /// when ds.server_states.len() == ds.num_servers
    pub proof fn lemma_max_commit_index_eq_seq(ds: RaftDistributedState)
        requires ds.server_states.len() == ds.num_servers
        ensures MaxCommitIndex(ds) == max_commit_index_seq(ds.server_states)
        decreases ds.num_servers
    {
        if ds.num_servers > 0 {
            let sub_ds = RaftDistributedState {
                server_states: ds.server_states.subrange(0, ds.num_servers - 1),
                server_constants: ds.server_constants.subrange(0, ds.num_servers - 1),
                network: ds.network,
                num_servers: ds.num_servers - 1,
                vote_log_len: ds.vote_log_len,
            };
            assert(sub_ds.server_states.len() == ds.num_servers - 1);
            lemma_max_commit_index_eq_seq(sub_ds);
        }
    }

    /// max_commit_index_seq is at least each server's commit_index
    pub proof fn lemma_max_commit_seq_ge_server(states: Seq<LState>, j: int)
        requires 0 <= j < states.len()
        ensures max_commit_index_seq(states) >= states[j].commit_index
        decreases states.len()
    {
        if states.len() > 0 {
            if j == states.len() - 1 {
                // j is the last element; directly compared in the definition
            } else {
                // j < states.len() - 1; recurse on subrange
                let sub = states.subrange(0, states.len() - 1);
                assert(sub[j] == states[j]);
                lemma_max_commit_seq_ge_server(sub, j);
                // max_commit_index_seq(sub) >= sub[j].commit_index == states[j].commit_index
                // max_commit_index_seq(states) >= max_commit_index_seq(sub)
            }
        }
    }

    /// max_commit_index_seq is achieved by some server (when commit_indices are non-negative)
    pub proof fn lemma_max_commit_seq_achieved(states: Seq<LState>)
        requires
            states.len() > 0,
            forall |j: int| #![trigger states[j]] 0 <= j < states.len() ==> states[j].commit_index >= 0,
        ensures exists |j: int| #![trigger states[j]] 0 <= j < states.len()
            && states[j].commit_index == max_commit_index_seq(states)
        decreases states.len()
    {
        let n = states.len();
        let sub = states.subrange(0, n - 1);
        let last_commit = states[n - 1].commit_index;
        let rest_max = max_commit_index_seq(sub);

        if n == 1 {
            // max_commit_index_seq(states) = max(states[0].commit_index, 0)
            // Since commit_index >= 0, max(commit_index, 0) == commit_index
            assert(states[0].commit_index >= 0);
            // rest_max = max_commit_index_seq(empty subrange) = 0
            assert(sub.len() == 0);
            // max = if last_commit > rest_max { last_commit } else { rest_max }
            // Since last_commit >= 0 == rest_max, we have max == last_commit
            if last_commit > rest_max {
                assert(max_commit_index_seq(states) == last_commit);
            } else {
                // last_commit <= 0 and last_commit >= 0, so last_commit == 0 == rest_max
                assert(last_commit == 0);
                assert(max_commit_index_seq(states) == rest_max);
                assert(rest_max == 0);
                assert(states[0].commit_index == 0);
            }
        } else {
            if last_commit > rest_max {
                // Last server achieves the max
                assert(states[n - 1].commit_index == max_commit_index_seq(states));
            } else {
                // Some server in sub achieves rest_max
                assert forall |j: int| #![trigger sub[j]] 0 <= j < sub.len()
                implies sub[j].commit_index >= 0 by {
                    assert(sub[j] == states[j]);
                }
                lemma_max_commit_seq_achieved(sub);
                let j = choose |j: int| #![trigger sub[j]] 0 <= j < sub.len()
                    && sub[j].commit_index == max_commit_index_seq(sub);
                assert(states[j] == sub[j]);
                assert(states[j].commit_index == rest_max);
                assert(max_commit_index_seq(states) == rest_max);
            }
        }
    }

    /// MaxCommitIndex(ds) > 0 implies some server has commit_index >= MaxCommitIndex
    /// and log.len() >= MaxCommitIndex (from CommitIndexBounded).
    pub proof fn lemma_max_commit_index_witness(ds: RaftDistributedState)
        requires
            WellFormedRaftDistributed(ds),
            CommitIndexBounded(ds),
            MaxCommitIndex(ds) > 0,
        ensures
            exists |id: int| #![trigger ds.server_states[id]] 0 <= id < ds.num_servers
                && ds.server_states[id].commit_index >= MaxCommitIndex(ds)
                && ds.server_states[id].log.len() >= MaxCommitIndex(ds)
        decreases ds.num_servers
    {
        let n = ds.num_servers;
        let last_commit = ds.server_states[n - 1].commit_index;
        let sub_ds = RaftDistributedState {
            server_states: ds.server_states.subrange(0, n - 1),
            server_constants: ds.server_constants.subrange(0, n - 1),
            network: ds.network,
            num_servers: n - 1,
            vote_log_len: ds.vote_log_len,
        };
        let rest_max = MaxCommitIndex(sub_ds);
        if last_commit >= MaxCommitIndex(ds) {
            // Last server achieves the max
            assert(ds.server_states[n - 1].commit_index >= MaxCommitIndex(ds));
            assert(CommitIndexBounded(ds));
            assert(ds.server_states[n - 1].log.len() >= last_commit);
        } else {
            // MaxCommitIndex comes from sub_ds
            assert(rest_max >= MaxCommitIndex(ds));
            assert(rest_max > 0);
            // Need WellFormed for sub_ds — establish manually
            // sub_ds has n-1 servers; WellFormedness requires my_id/quorum_size/servers match
            // These are inherited from ds but with wrong values for the sub-state.
            // Instead, prove the witness directly: rest_max == MaxCommitIndex(sub_ds) > 0,
            // so recursively there's a witness in 0..n-1 which is also in 0..n.
            if n - 1 > 0 {
                // The recursive case: find witness in sub_ds
                // We can't recurse directly (need WellFormed(sub_ds)), but we know
                // rest_max > 0 means some server in 0..n-1 has commit_index == rest_max.
                // Use seq-based approach:
                lemma_max_commit_index_eq_seq(ds);
                lemma_max_commit_index_eq_seq(sub_ds);
                // max_commit_index_seq(ds.server_states) == MaxCommitIndex(ds)
                // max_commit_index_seq(sub) == rest_max
                let sub = ds.server_states.subrange(0, n - 1);
                lemma_max_commit_seq_ge_server_reverse(sub, rest_max);
                let j = choose |j: int| #![trigger sub[j]] 0 <= j < sub.len()
                    && sub[j].commit_index >= rest_max;
                assert(ds.server_states[j] == sub[j]);
                assert(ds.server_states[j].commit_index >= MaxCommitIndex(ds));
                assert(CommitIndexBounded(ds));
                assert(ds.server_states[j].log.len() >= ds.server_states[j].commit_index);
            }
        }
    }

    /// If max_commit_index_seq(states) >= threshold > 0, some server achieves >= threshold
    pub proof fn lemma_max_commit_seq_ge_server_reverse(states: Seq<LState>, threshold: int)
        requires
            states.len() > 0,
            max_commit_index_seq(states) >= threshold,
            threshold > 0,
        ensures
            exists |j: int| #![trigger states[j]] 0 <= j < states.len()
                && states[j].commit_index >= threshold
        decreases states.len()
    {
        let n = states.len();
        let last_commit = states[n - 1].commit_index;
        let sub = states.subrange(0, n - 1);
        let rest_max = max_commit_index_seq(sub);
        if last_commit >= threshold {
            // Last server suffices
        } else {
            // rest_max >= threshold (since max(last_commit, rest_max) >= threshold and last_commit < threshold)
            assert(rest_max >= threshold);
            if sub.len() > 0 {
                lemma_max_commit_seq_ge_server_reverse(sub, threshold);
                let j = choose |j: int| #![trigger sub[j]] 0 <= j < sub.len()
                    && sub[j].commit_index >= threshold;
                assert(states[j] == sub[j]);
            }
        }
    }

    /// GetCommittedLog length equals MaxCommitIndex when CommitIndexBounded holds
    pub proof fn lemma_committed_log_len(ds: RaftDistributedState)
        requires
            WellFormedRaftDistributed(ds),
            CommitIndexBounded(ds),
        ensures
            GetCommittedLog(ds).len() == if MaxCommitIndex(ds) <= 0 { 0 } else { MaxCommitIndex(ds) }
    {
        let max_commit = MaxCommitIndex(ds);
        if max_commit <= 0 {
            // GetCommittedLog returns empty
        } else {
            // Find a server achieving max_commit with log.len() >= max_commit
            lemma_max_commit_index_witness(ds);
            let j = choose |id: int| #![trigger ds.server_states[id]] 0 <= id < ds.num_servers
                && ds.server_states[id].commit_index >= max_commit
                && ds.server_states[id].log.len() >= max_commit;
            // ExtractLogValues(log, max_commit) has length max_commit
            lemma_extract_log_values_len(ds.server_states[j].log, max_commit);
        }
    }

    /// If every server's commit_index in states' >= that in states,
    /// then max_commit_index_seq(states') >= max_commit_index_seq(states).
    pub proof fn lemma_max_commit_seq_monotone(
        states: Seq<LState>, states_: Seq<LState>
    )
        requires
            states.len() == states_.len(),
            forall |j: int| 0 <= j < states.len()
                ==> #[trigger] states_[j].commit_index >= states[j].commit_index,
        ensures
            max_commit_index_seq(states_) >= max_commit_index_seq(states)
        decreases states.len()
    {
        if states.len() > 0 {
            let n = states.len();
            let sub = states.subrange(0, n - 1);
            let sub_ = states_.subrange(0, n - 1);

            // Per-element monotonicity for the subrange
            assert forall |j: int| 0 <= j < sub.len()
            implies #[trigger] sub_[j].commit_index >= sub[j].commit_index by {
                assert(sub[j] == states[j]);
                assert(sub_[j] == states_[j]);
            }

            lemma_max_commit_seq_monotone(sub, sub_);
            // max_commit_index_seq(sub_) >= max_commit_index_seq(sub)
            // states_[n-1].commit_index >= states[n-1].commit_index
            // max_commit_index_seq(states_) = max(states_[n-1].commit_index, max_commit_index_seq(sub_))
            //                                >= max(states[n-1].commit_index, max_commit_index_seq(sub))
            //                                = max_commit_index_seq(states)
        }
    }

    // =========================================================================
    // Helper Lemma: ExtractLogValues length
    // =========================================================================

    pub proof fn lemma_extract_log_values_len(log: Seq<LLogEntry>, len: int)
        requires 0 <= len <= log.len()
        ensures ExtractLogValues(log, len).len() == len
        decreases len
    {
        if len > 0 {
            lemma_extract_log_values_len(log, len - 1);
        }
    }

    /// ExtractLogValues(log, len)[k] == log[k].value for 0 <= k < len
    pub proof fn lemma_extract_log_values_index(log: Seq<LLogEntry>, len: int, k: int)
        requires
            0 <= len <= log.len(),
            0 <= k < len,
        ensures
            ExtractLogValues(log, len)[k] == log[k].value
        decreases len
    {
        if len == 1 {
            // ExtractLogValues(log, 1) == seq![log[0].value], k == 0
        } else {
            lemma_extract_log_values_len(log, len - 1);
            if k < len - 1 {
                lemma_extract_log_values_index(log, len - 1, k);
            } else {
                // k == len - 1: pushed element
            }
        }
    }
}
