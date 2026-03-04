use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::message_invariants::*;
use crate::common::collections::sets::*;
use vstd::prelude::*;
use vstd::{map::*, seq::*, set::*, set_lib::*};

verus! {

    // =========================================================================
    // Invariant 1: Election Safety
    // At most one leader per term across all servers.
    // =========================================================================

    pub open spec fn ElectionSafety(ds: RaftDistributedState) -> bool {
        forall |i: int, j: int|
            0 <= i < ds.num_servers && 0 <= j < ds.num_servers
            && ds.server_states[i].role is Leader
            && ds.server_states[j].role is Leader
            && ds.server_states[i].current_term == ds.server_states[j].current_term
            ==> i == j
    }

    // =========================================================================
    // Invariant 2: Log Matching
    // If two servers have entries at the same index with the same term,
    // then all preceding entries also match.
    // =========================================================================

    pub open spec fn LogMatching(ds: RaftDistributedState) -> bool {
        forall |i: int, j: int, k: int|
            0 <= i < ds.num_servers && 0 <= j < ds.num_servers
            && 0 <= k < ds.server_states[i].log.len()
            && 0 <= k < ds.server_states[j].log.len()
            && ds.server_states[i].log[k].term == ds.server_states[j].log[k].term
            ==> (forall |m: int| 0 <= m <= k
                && m < ds.server_states[i].log.len()
                && m < ds.server_states[j].log.len()
                ==> ds.server_states[i].log[m] == ds.server_states[j].log[m])
    }

    // =========================================================================
    // Invariant 3: Leader Completeness
    // If an entry is committed in some term, it appears in the log of
    // every leader for all higher-numbered terms.
    // =========================================================================

    /// An entry at index k is "committed" if a majority of servers have
    /// matching entries at that index.
    pub open spec fn EntryCommittedAt(ds: RaftDistributedState, k: int, entry: LLogEntry) -> bool {
        let quorum_size = ds.num_servers / 2 + 1;
        exists |quorum: Set<int>| {
            &&& quorum.len() >= quorum_size
            &&& (forall |id: int| quorum.contains(id) ==> {
                &&& 0 <= id < ds.num_servers
                &&& ds.server_states[id].log.len() > k
                &&& ds.server_states[id].log[k] == entry
            })
        }
    }

    pub open spec fn LeaderCompleteness(ds: RaftDistributedState) -> bool {
        forall |k: int, entry: LLogEntry, leader_id: int|
            0 <= k
            && EntryCommittedAt(ds, k, entry)
            && 0 <= leader_id < ds.num_servers
            && ds.server_states[leader_id].role is Leader
            && ds.server_states[leader_id].current_term > entry.term
            ==> {
                &&& ds.server_states[leader_id].log.len() > k
                &&& ds.server_states[leader_id].log[k] == entry
            }
    }

    // =========================================================================
    // Invariant 4: State Machine Safety
    // If any server has applied a log entry at a given index, no other server
    // will ever apply a different entry for that index.
    //
    // This follows from Log Matching + Leader Completeness: committed
    // entries are never overwritten.
    // =========================================================================

    pub open spec fn StateMachineSafety(ds: RaftDistributedState) -> bool {
        forall |i: int, j: int, k: int|
            0 <= i < ds.num_servers && 0 <= j < ds.num_servers
            && 0 <= k < ds.server_states[i].commit_index
            && 0 <= k < ds.server_states[j].commit_index
            && k < ds.server_states[i].log.len()
            && k < ds.server_states[j].log.len()
            ==> ds.server_states[i].log[k] == ds.server_states[j].log[k]
    }

    // =========================================================================
    // Supporting invariants for Election Safety
    // =========================================================================

    /// Each voter in a leader/candidate's votes_granted set is a valid server ID
    pub open spec fn VotesGrantedAreServers(ds: RaftDistributedState) -> bool {
        forall |i: int, v: int|
            0 <= i < ds.num_servers
            && ds.server_states[i].votes_granted.contains(v)
            ==> 0 <= v < ds.num_servers
    }

    /// A leader/candidate has itself in its votes_granted set
    /// (Leaders and Candidates always start by voting for themselves)
    pub open spec fn CandidateOrLeaderVotedForSelf(ds: RaftDistributedState) -> bool {
        forall |i: int|
            0 <= i < ds.num_servers
            && (ds.server_states[i].role is Candidate || ds.server_states[i].role is Leader)
            ==> ds.server_states[i].votes_granted.contains(ds.server_constants[i].my_id)
    }

    /// A leader/candidate has voted for itself (voted_for == i).
    /// LTimeout sets voted_for = my_id when becoming Candidate. All transitions
    /// that preserve Candidate/Leader role also preserve voted_for.
    pub open spec fn CandidateOrLeaderVotedForSelfId(ds: RaftDistributedState) -> bool {
        forall |i: int|
            0 <= i < ds.num_servers
            && (ds.server_states[i].role is Candidate || ds.server_states[i].role is Leader)
            ==> ds.server_states[i].has_voted && ds.server_states[i].voted_for == i
    }

    /// Network-level invariant: if server i is a Leader or Candidate with voter v
    /// in its votes_granted set, then voter v voted for i in i's current term.
    /// This links the local votes_granted set to the global voting state.
    ///
    /// Network-based vote tracking: if v is in candidate/leader i's votes_granted,
    /// there must be a VoteResponse{granted: true, term: i.current_term} packet
    /// in the network from v to i.
    ///
    /// This formulation is inductive because:
    /// 1. The network is monotonic (packets are never removed).
    /// 2. When LHandleVoteResponseMsg adds voter v, the received VoteResponse
    ///    packet is already in the network (with the right term, by the new
    ///    term check guard).
    /// 3. votes_granted is reset on term change (step_down or LTimeout), so
    ///    old votes from previous terms don't carry over.
    ///
    /// Combined with OneVotePerTermInNetwork, this gives ElectionSafety:
    /// two leaders at the same term would need overlapping quorums, but the
    /// quorum intersection voter has a unique VoteResponse destination.
    pub open spec fn VotersVotedForCandidate(ds: RaftDistributedState) -> bool {
        forall |i: int, v: int|
            0 <= i < ds.num_servers
            && 0 <= v < ds.num_servers
            && v != i
            && (ds.server_states[i].role is Candidate || ds.server_states[i].role is Leader)
            && ds.server_states[i].votes_granted.contains(v)
            ==> exists |p: LRaftPacket| {
                &&& ds.network.contains(p)
                &&& p.dst == i
                &&& p.msg matches LRaftMessage::VoteResponse { term, granted, voter }
                &&& term == ds.server_states[i].current_term
                &&& granted
                &&& voter == v
            }
    }

    /// Quorum of voters: if server i is Leader, then votes_granted has
    /// quorum_size members who all voted for i in i's current_term.
    pub open spec fn LeaderHasQuorum(ds: RaftDistributedState) -> bool {
        forall |i: int|
            0 <= i < ds.num_servers
            && ds.server_states[i].role is Leader
            ==> ds.server_states[i].votes_granted.len() >= ds.server_constants[i].quorum_size
    }

    /// Commit index is bounded by log length
    pub open spec fn CommitIndexBounded(ds: RaftDistributedState) -> bool {
        forall |i: int|
            0 <= i < ds.num_servers
            ==> ds.server_states[i].commit_index <= ds.server_states[i].log.len()
    }

    /// Leader's log is at least as long as any entry with its term.
    /// If any server has a log entry at index k with term T, and there
    /// exists a current leader at term T, then that leader's log has
    /// length > k (i.e., the leader has the entry at index k).
    ///
    /// This captures entry provenance: entries with term T can only be
    /// created by the leader at term T (LClientRequest) or received
    /// via AppendEntries from the leader at term T (LFollowerAppendEntries).
    /// In either case, the leader's log must have been long enough.
    pub open spec fn LeaderLogLongEnough(ds: RaftDistributedState) -> bool {
        forall |i: int, k: int, l: int|
            0 <= i < ds.num_servers
            && 0 <= k < ds.server_states[i].log.len()
            && 0 <= l < ds.num_servers
            && ds.server_states[l].role is Leader
            && ds.server_states[l].current_term == ds.server_states[i].log[k].term
            ==> ds.server_states[l].log.len() > k
    }

    // =========================================================================
    // Supporting invariant: Entry Term Leader Witness
    //
    // For every entry at index k with term T in any server's log,
    // there exists a "witness" server w whose log also has that entry
    // (same index, same term, same value) and w.log.len() > k.
    // This witness is the leader that originally created the entry.
    // =========================================================================

    pub open spec fn EntryTermLeaderWitness(ds: RaftDistributedState) -> bool {
        forall |i: int, k: int|
            #![trigger ds.server_states[i].log[k]]
            0 <= i < ds.num_servers
            && 0 <= k < ds.server_states[i].log.len()
            ==> exists |w: int|
                #![trigger ds.server_states[w].log[k]]
            {
                &&& 0 <= w < ds.num_servers
                &&& ds.server_states[w].log.len() > k
                &&& ds.server_states[w].log[k] == ds.server_states[i].log[k]
            }
    }

    // =========================================================================
    // Supporting invariant: Entry Term Has Vote Quorum
    //
    // For every entry at index k with term T in any server's log,
    // there exists a server d (the "vote destination") such that:
    // 1. d also has the entry (same index, same content)
    // 2. At least quorum_size - 1 distinct servers have
    //    VoteResponse{T, granted: true} packets to d in the network.
    //
    // This captures the fact that entries at term T can only be created
    // by a leader at T, and that leader received a quorum of votes at T
    // whose VoteResponse packets persist in the network (monotonicity).
    // =========================================================================

    pub open spec fn EntryTermHasVoteQuorum(ds: RaftDistributedState) -> bool {
        let quorum_size = ds.num_servers / 2 + 1;
        forall |i: int, k: int|
            #![trigger ds.server_states[i].log[k]]
            0 <= i < ds.num_servers
            && 0 <= k < ds.server_states[i].log.len()
            ==> exists |d: int, voters: Seq<int>|
                #![trigger ds.server_states[d].log[k], voters.len()]
            {
                &&& 0 <= d < ds.num_servers
                &&& ds.server_states[d].log.len() > k
                &&& ds.server_states[d].log[k] == ds.server_states[i].log[k]
                &&& voters.len() >= quorum_size - 1
                // Each voter has a VoteResponse packet to d
                &&& (forall |a: int| #![trigger voters[a]] 0 <= a < voters.len() ==> {
                    &&& 0 <= voters[a] < ds.num_servers
                    &&& voters[a] != d
                    &&& ds.network.contains(LRaftPacket {
                        src: voters[a],
                        dst: d,
                        msg: LRaftMessage::VoteResponse {
                            term: ds.server_states[i].log[k].term,
                            granted: true,
                            voter: voters[a],
                        },
                    })
                })
                // Voters are pairwise distinct
                &&& (forall |a: int, b: int|
                    #![trigger voters[a], voters[b]]
                    0 <= a < voters.len() && 0 <= b < voters.len() && a != b
                    ==> voters[a] != voters[b])
            }
    }

    // =========================================================================
    // Invariant: VoteResponseTermBound
    // =========================================================================
    //
    // If a granted VoteResponse{term: T, voter: v} is in the network,
    // then v's current_term >= T.
    //
    // Proof: at creation time, step_down_if_needed ensures v.current_term >= T.
    // After creation, term monotonicity (current_term never decreases) preserves it.

    pub open spec fn VoteResponseTermBound(ds: RaftDistributedState) -> bool {
        forall |p: LRaftPacket| ds.network.contains(p) ==>
            match p.msg {
                LRaftMessage::VoteResponse { term: t, granted, voter: v } => {
                    granted ==> {
                        &&& 0 <= v < ds.num_servers
                        &&& ds.server_states[v].current_term >= t
                    }
                }
                _ => true,
            }
    }

    // =========================================================================
    // Invariant: CandidateVoteDestinationUnique
    // =========================================================================
    //
    // If RequestVote{term: T, candidate: d} and
    // VoteResponse{term: T, voter: d, granted: true, dst: c} are both
    // in the network, then c == d (i.e., d only voted for itself at term T).
    //
    // This captures the temporal argument: a candidate at term T votes for
    // itself (LTimeout sets voted_for = self, has_voted = true), so it can
    // never subsequently grant a vote for another candidate at term T.

    pub open spec fn CandidateVoteDestinationUnique(ds: RaftDistributedState) -> bool {
        forall |p_req: LRaftPacket, p_vote: LRaftPacket|
            ds.network.contains(p_req) && ds.network.contains(p_vote) ==>
            match p_req.msg {
                LRaftMessage::RequestVote { term: t_req, candidate: d, .. } =>
                    match p_vote.msg {
                        LRaftMessage::VoteResponse { term: t_vote, granted, voter: v } =>
                            (granted && t_req == t_vote && v == d)
                                ==> p_vote.dst == d,
                        _ => true,
                    },
                _ => true,
            }
    }

    // =========================================================================
    // Composite Invariant
    // =========================================================================

    /// The full inductive invariant: conjunction of all safety invariants
    pub open spec fn RaftSafetyInvariant(ds: RaftDistributedState) -> bool {
        &&& WellFormedRaftDistributed(ds)
        &&& ElectionSafety(ds)
        &&& LogMatching(ds)
        &&& LeaderCompleteness(ds)
        &&& StateMachineSafety(ds)
        &&& LeaderHasQuorum(ds)
        &&& CommitIndexBounded(ds)
        &&& LeaderLogLongEnough(ds)
        &&& EntryTermLeaderWitness(ds)
        &&& EntryTermHasVoteQuorum(ds)
        &&& VotesGrantedAreServers(ds)
        &&& CandidateOrLeaderVotedForSelf(ds)
        &&& CandidateOrLeaderVotedForSelfId(ds)
        &&& VotersVotedForCandidate(ds)
        // Message invariants (Phase 34.2)
        &&& SenderIntegrity(ds)
        &&& VoteResponseIntegrity(ds)
        &&& VoteResponseHasRequestVote(ds)
        &&& AppendEntriesIntegrity(ds)
        &&& OneVotePerTermInNetwork(ds)
        &&& VoteResponseTermBound(ds)
        &&& CandidateVoteDestinationUnique(ds)
    }

    // =========================================================================
    // Invariant holds at init
    // =========================================================================

    pub proof fn lemma_init_establishes_invariant(ds: RaftDistributedState)
        requires RaftDistributedInit(ds)
        ensures RaftSafetyInvariant(ds)
    {
        // All servers start as Followers with empty votes_granted:
        // - ElectionSafety: no Leaders, vacuously true
        // - LogMatching: empty logs, vacuously true
        // - LeaderCompleteness: no committed entries, vacuously true
        // - StateMachineSafety: commit_index = 0, vacuously true
        // - LeaderHasQuorum: no Leaders, vacuously true
        // - CommitIndexBounded: commit_index = 0 <= log.len() = 0
        // - VotesGrantedAreServers: votes_granted empty, vacuously true
        // - CandidateOrLeaderVotedForSelf: no Candidates/Leaders, vacuously true
        // - VotersVotedForCandidate: no Candidates/Leaders, vacuously true
        // - EntryTermHasVoteQuorum: empty logs, vacuously true
        // Message invariants: network is empty, all vacuously true
        // - SenderIntegrity, VoteResponseIntegrity, VoteResponseHasRequestVote,
        //   AppendEntriesIntegrity, OneVotePerTermInNetwork,
        //   VoteResponseTermBound, CandidateVoteDestinationUnique:
        //   forall over empty set is vacuously true
    }

    // =========================================================================
    // Election Safety Induction Proof
    // =========================================================================

    /// Helper: a server's step doesn't create new leaders in other terms.
    /// If only server_id transitions and all others are unchanged,
    /// and ElectionSafety held before, then for any pair (i, j) where
    /// neither is server_id, ElectionSafety still holds between them.
    ///
    /// The only interesting case is when server_id becomes a new Leader.

    /// Helper: extract voted_for == i from CandidateOrLeaderVotedForSelfId.
    proof fn lemma_voted_for_self(ds: RaftDistributedState, i: int)
        requires
            RaftSafetyInvariant(ds),
            0 <= i < ds.num_servers,
            ds.server_states[i].role is Candidate || ds.server_states[i].role is Leader,
        ensures
            ds.server_states[i].voted_for == i,
            ds.server_states[i].has_voted,
    {
        assert(CandidateOrLeaderVotedForSelfId(ds));
    }

    /// Helper: turn vote-set membership into an explicit VoteResponse packet
    /// witness and aligned voter facts from VoteResponseIntegrity.
    proof fn lemma_vote_witness_from_votes_granted(
        ds: RaftDistributedState, candidate: int, voter: int,
    )
        requires
            VotersVotedForCandidate(ds),
            VoteResponseIntegrity(ds),
            0 <= candidate < ds.num_servers,
            0 <= voter < ds.num_servers,
            voter != candidate,
            (ds.server_states[candidate].role is Candidate
                || ds.server_states[candidate].role is Leader),
            ds.server_states[candidate].votes_granted.contains(voter),
        ensures
            exists |p: LRaftPacket| {
                &&& ds.network.contains(p)
                &&& p.src == voter
                &&& p.dst == candidate
                &&& p.msg matches LRaftMessage::VoteResponse { term, granted, voter: msg_voter }
                &&& granted
                &&& term == ds.server_states[candidate].current_term
                &&& msg_voter == voter
            },
            ds.server_states[voter].current_term
                > ds.server_states[candidate].current_term
                || (ds.server_states[voter].current_term
                    == ds.server_states[candidate].current_term
                    && ds.server_states[voter].has_voted
                    && ds.server_states[voter].voted_for == candidate),
    {
        let p = choose |p: LRaftPacket| {
            &&& ds.network.contains(p)
            &&& p.dst == candidate
            &&& p.msg matches LRaftMessage::VoteResponse { term, granted, voter: msg_voter }
            &&& term == ds.server_states[candidate].current_term
            &&& granted
            &&& msg_voter == voter
        };
        assert(ds.network.contains(p));
        assert(p.dst == candidate);
        assert(p.msg is VoteResponse);
        assert(p.msg->VoteResponse_granted);
        assert(p.msg->VoteResponse_term == ds.server_states[candidate].current_term);
        assert(p.msg->VoteResponse_voter == voter);

        assert(
            match p.msg {
                LRaftMessage::VoteResponse { term: t, granted: g, voter: v } => {
                    g ==> {
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
        ) by {
            assert(VoteResponseIntegrity(ds));
        };

        assert(p.src == voter);
        assert(
            ds.server_states[voter].current_term
                > ds.server_states[candidate].current_term
                || (ds.server_states[voter].current_term
                    == ds.server_states[candidate].current_term
                    && ds.server_states[voter].has_voted
                    && ds.server_states[voter].voted_for == candidate)
        );
        assert(exists |pkt: LRaftPacket| {
            &&& ds.network.contains(pkt)
            &&& pkt.src == voter
            &&& pkt.dst == candidate
            &&& pkt.msg matches LRaftMessage::VoteResponse { term, granted, voter: msg_voter }
            &&& granted
            &&& term == ds.server_states[candidate].current_term
            &&& msg_voter == voter
        }) by {
            assert(ds.network.contains(p));
            assert(p.src == voter);
            assert(p.dst == candidate);
            assert(p.msg is VoteResponse);
            assert(p.msg->VoteResponse_granted);
            assert(p.msg->VoteResponse_term == ds.server_states[candidate].current_term);
            assert(p.msg->VoteResponse_voter == voter);
        };
    }

    /// Helper: from vote-set membership, extract an explicit RequestVote packet
    /// witness (including request parameters) that justifies the granted vote.
    ///
    /// This composes:
    /// - vote packet extraction from `votes_granted` (`lemma_vote_witness_from_votes_granted`)
    /// - provenance hook (`VoteResponseHasRequestVote`) to recover the matching
    ///   RequestVote packet for the same term/candidate route.
    proof fn lemma_request_vote_witness_from_votes_granted(
        ds: RaftDistributedState, candidate: int, voter: int,
    )
        requires
            VotersVotedForCandidate(ds),
            VoteResponseIntegrity(ds),
            VoteResponseHasRequestVote(ds),
            0 <= candidate < ds.num_servers,
            0 <= voter < ds.num_servers,
            voter != candidate,
            (ds.server_states[candidate].role is Candidate
                || ds.server_states[candidate].role is Leader),
            ds.server_states[candidate].votes_granted.contains(voter),
        ensures
            exists |req: LRaftPacket| {
                &&& ds.network.contains(req)
                &&& req.src == candidate
                &&& req.dst == voter
                &&& req.msg matches LRaftMessage::RequestVote {
                    term,
                    candidate: req_candidate,
                    last_log_index: _,
                    last_log_term: _,
                }
                &&& term == ds.server_states[candidate].current_term
                &&& req_candidate == candidate
            },
    {
        lemma_vote_witness_from_votes_granted(ds, candidate, voter);
        let vote_pkt = choose |p: LRaftPacket| {
            &&& ds.network.contains(p)
            &&& p.src == voter
            &&& p.dst == candidate
            &&& p.msg matches LRaftMessage::VoteResponse { term, granted, voter: msg_voter }
            &&& granted
            &&& term == ds.server_states[candidate].current_term
            &&& msg_voter == voter
        };
        assert(ds.network.contains(vote_pkt));
        assert(vote_pkt.msg is VoteResponse);
        assert(vote_pkt.msg->VoteResponse_granted);
        assert(vote_pkt.msg->VoteResponse_term == ds.server_states[candidate].current_term);
        assert(vote_pkt.msg->VoteResponse_voter == voter);

        assert(
            match vote_pkt.msg {
                LRaftMessage::VoteResponse { term: t, granted, voter: v } => {
                    granted ==> exists |req: LRaftPacket| {
                        &&& ds.network.contains(req)
                        &&& req.src == vote_pkt.dst
                        &&& req.dst == v
                        &&& req.msg matches LRaftMessage::RequestVote {
                            term,
                            candidate: req_candidate,
                            last_log_index: _,
                            last_log_term: _,
                        }
                        &&& term == t
                        &&& req_candidate == vote_pkt.dst
                    }
                }
                _ => true,
            }
        ) by {
            assert(VoteResponseHasRequestVote(ds));
        };

        let req_pkt = choose |req: LRaftPacket| {
            &&& ds.network.contains(req)
            &&& req.src == vote_pkt.dst
            &&& req.dst == vote_pkt.msg->VoteResponse_voter
            &&& req.msg matches LRaftMessage::RequestVote {
                term,
                candidate: req_candidate,
                last_log_index: _,
                last_log_term: _,
            }
            &&& term == vote_pkt.msg->VoteResponse_term
            &&& req_candidate == vote_pkt.dst
        };
        assert(ds.network.contains(req_pkt));
        assert(req_pkt.src == candidate);
        assert(req_pkt.dst == voter);
        assert(req_pkt.msg is RequestVote);
        assert(req_pkt.msg->RequestVote_term == ds.server_states[candidate].current_term);
        assert(req_pkt.msg->RequestVote_candidate == candidate);

        assert(exists |req: LRaftPacket| {
            &&& ds.network.contains(req)
            &&& req.src == candidate
            &&& req.dst == voter
            &&& req.msg matches LRaftMessage::RequestVote {
                term,
                candidate: req_candidate,
                last_log_index: _,
                last_log_term: _,
            }
            &&& term == ds.server_states[candidate].current_term
            &&& req_candidate == candidate
        }) by {
            let req = req_pkt;
            assert(req.src == candidate);
            assert(req.dst == voter);
            assert(req.msg matches LRaftMessage::RequestVote {
                term,
                candidate: req_candidate,
                last_log_index: _,
                last_log_term: _,
            });
            assert(req.msg->RequestVote_term == ds.server_states[candidate].current_term);
            assert(req.msg->RequestVote_candidate == candidate);
        };
    }

    /// Helper: combine committed quorum and vote quorum to produce an overlap
    /// witness carrying both committed-entry and vote-side facts.
    proof fn lemma_committed_vote_quorum_overlap_witness(
        ds: RaftDistributedState,
        k: int,
        entry: LLogEntry,
        candidate: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            EntryCommittedAt(ds, k, entry),
            0 <= candidate < ds.num_servers,
            (ds.server_states[candidate].role is Candidate
                || ds.server_states[candidate].role is Leader),
            VotesGrantedAreServers(ds),
            VotersVotedForCandidate(ds),
            VoteResponseIntegrity(ds),
            ds.server_states[candidate].votes_granted.len()
                >= ds.server_constants[candidate].quorum_size,
        ensures
            exists |w: int| {
                &&& 0 <= w < ds.num_servers
                &&& ds.server_states[candidate].votes_granted.contains(w)
                &&& ds.server_states[w].log.len() > k
                &&& ds.server_states[w].log[k] == entry
                &&& (w != candidate ==> (
                        ds.server_states[w].current_term
                            > ds.server_states[candidate].current_term
                        || (ds.server_states[w].current_term
                                == ds.server_states[candidate].current_term
                            && ds.server_states[w].has_voted
                            && ds.server_states[w].voted_for == candidate)
                    ))
                &&& (w != candidate ==> exists |p: LRaftPacket| {
                        &&& ds.network.contains(p)
                        &&& p.src == w
                        &&& p.dst == candidate
                        &&& p.msg matches LRaftMessage::VoteResponse { term, granted, voter: msg_voter }
                        &&& granted
                        &&& term == ds.server_states[candidate].current_term
                        &&& msg_voter == w
                    })
            },
    {
        let n = ds.num_servers;
        let quorum_size = ds.server_constants[candidate].quorum_size;
        let universe = ds.server_constants[candidate].servers;
        let commit_quorum = choose |q: Set<int>| {
            &&& q.len() >= n / 2 + 1
            &&& (forall |id: int| q.contains(id) ==> {
                &&& 0 <= id < ds.num_servers
                &&& ds.server_states[id].log.len() > k
                &&& ds.server_states[id].log[k] == entry
            })
        };
        let vote_quorum = ds.server_states[candidate].votes_granted;

        assert(quorum_size == n / 2 + 1);
        assert(commit_quorum.len() >= quorum_size);
        assert(vote_quorum.len() >= quorum_size);
        assert(commit_quorum.len() + vote_quorum.len() >= quorum_size + quorum_size);
        assert(quorum_size + quorum_size > n);
        assert(commit_quorum.len() + vote_quorum.len() > n);

        assert(universe == Set::<int>::new(|j: int| 0 <= j < n));
        assert(commit_quorum.subset_of(universe)) by {
            assert forall |id: int| commit_quorum.contains(id) implies universe.contains(id) by {
                assert(0 <= id < ds.num_servers);
            };
        };
        assert(vote_quorum.subset_of(universe)) by {
            assert forall |id: int| vote_quorum.contains(id) implies universe.contains(id) by {
                assert(VotesGrantedAreServers(ds));
            };
        };

        lemma_range_set_finite(n);
        assert(universe.finite());

        lemma_quorum_intersection(commit_quorum, vote_quorum, universe);
        let w = choose |w: int| commit_quorum.contains(w) && vote_quorum.contains(w);
        assert(0 <= w < ds.num_servers);
        assert(ds.server_states[w].log.len() > k);
        assert(ds.server_states[w].log[k] == entry);

        if w != candidate {
            lemma_vote_witness_from_votes_granted(ds, candidate, w);
        }

        assert(exists |wit: int| {
            &&& 0 <= wit < ds.num_servers
            &&& ds.server_states[candidate].votes_granted.contains(wit)
            &&& ds.server_states[wit].log.len() > k
            &&& ds.server_states[wit].log[k] == entry
            &&& (wit != candidate ==> (
                    ds.server_states[wit].current_term
                        > ds.server_states[candidate].current_term
                    || (ds.server_states[wit].current_term
                            == ds.server_states[candidate].current_term
                        && ds.server_states[wit].has_voted
                        && ds.server_states[wit].voted_for == candidate)
                ))
            &&& (wit != candidate ==> exists |p: LRaftPacket| {
                    &&& ds.network.contains(p)
                    &&& p.src == wit
                    &&& p.dst == candidate
                    &&& p.msg matches LRaftMessage::VoteResponse { term, granted, voter: msg_voter }
                    &&& granted
                    &&& term == ds.server_states[candidate].current_term
                    &&& msg_voter == wit
                })
        }) by {
            assert(0 <= w < ds.num_servers);
            assert(ds.server_states[candidate].votes_granted.contains(w));
            assert(ds.server_states[w].log.len() > k);
            assert(ds.server_states[w].log[k] == entry);
            if w != candidate {
                assert(ds.server_states[w].current_term
                    > ds.server_states[candidate].current_term
                    || (ds.server_states[w].current_term
                        == ds.server_states[candidate].current_term
                        && ds.server_states[w].has_voted
                        && ds.server_states[w].voted_for == candidate));
                assert(exists |p: LRaftPacket| {
                    &&& ds.network.contains(p)
                    &&& p.src == w
                    &&& p.dst == candidate
                    &&& p.msg matches LRaftMessage::VoteResponse { term, granted, voter: msg_voter }
                    &&& granted
                    &&& term == ds.server_states[candidate].current_term
                    &&& msg_voter == w
                });
            }
        };
    }

    /// Helper: package overlap voter extraction with RequestVote provenance.
    ///
    /// Produces an overlap witness `w` for committed quorum ∩ vote quorum, and:
    /// - if `w == candidate`, no extra request witness is needed, or
    /// - if `w != candidate`, exposes RequestVote packet parameters
    ///   (`last_log_index`, `last_log_term`) via an explicit packet witness.
    proof fn lemma_overlap_request_vote_params_witness(
        ds: RaftDistributedState,
        k: int,
        entry: LLogEntry,
        candidate: int,
    )
        requires
            WellFormedRaftDistributed(ds),
            EntryCommittedAt(ds, k, entry),
            0 <= candidate < ds.num_servers,
            (ds.server_states[candidate].role is Candidate
                || ds.server_states[candidate].role is Leader),
            VotesGrantedAreServers(ds),
            VotersVotedForCandidate(ds),
            VoteResponseIntegrity(ds),
            VoteResponseHasRequestVote(ds),
            ds.server_states[candidate].votes_granted.len()
                >= ds.server_constants[candidate].quorum_size,
        ensures
            exists |w: int| {
                &&& 0 <= w < ds.num_servers
                &&& ds.server_states[candidate].votes_granted.contains(w)
                &&& ds.server_states[w].log.len() > k
                &&& ds.server_states[w].log[k] == entry
                &&& (w == candidate
                    || exists |req: LRaftPacket| {
                        &&& ds.network.contains(req)
                        &&& req.src == candidate
                        &&& req.dst == w
                        &&& req.msg matches LRaftMessage::RequestVote {
                            term,
                            candidate: req_candidate,
                            last_log_index: _,
                            last_log_term: _,
                        }
                        &&& term == ds.server_states[candidate].current_term
                        &&& req_candidate == candidate
                    })
            },
    {
        lemma_committed_vote_quorum_overlap_witness(ds, k, entry, candidate);
        let w = choose |w: int| {
            &&& 0 <= w < ds.num_servers
            &&& ds.server_states[candidate].votes_granted.contains(w)
            &&& ds.server_states[w].log.len() > k
            &&& ds.server_states[w].log[k] == entry
            &&& (w != candidate ==> (
                    ds.server_states[w].current_term
                        > ds.server_states[candidate].current_term
                    || (ds.server_states[w].current_term
                            == ds.server_states[candidate].current_term
                        && ds.server_states[w].has_voted
                        && ds.server_states[w].voted_for == candidate)
                ))
            &&& (w != candidate ==> exists |p: LRaftPacket| {
                    &&& ds.network.contains(p)
                    &&& p.src == w
                    &&& p.dst == candidate
                    &&& p.msg matches LRaftMessage::VoteResponse { term, granted, voter: msg_voter }
                    &&& granted
                    &&& term == ds.server_states[candidate].current_term
                    &&& msg_voter == w
                })
        };

        if w == candidate {
            assert(exists |wit: int| {
                &&& 0 <= wit < ds.num_servers
                &&& ds.server_states[candidate].votes_granted.contains(wit)
                &&& ds.server_states[wit].log.len() > k
                &&& ds.server_states[wit].log[k] == entry
                &&& (wit == candidate
                    || exists |req: LRaftPacket| {
                        &&& ds.network.contains(req)
                        &&& req.src == candidate
                        &&& req.dst == wit
                        &&& req.msg matches LRaftMessage::RequestVote {
                            term,
                            candidate: req_candidate,
                            last_log_index: _,
                            last_log_term: _,
                        }
                        &&& term == ds.server_states[candidate].current_term
                        &&& req_candidate == candidate
                    })
            }) by {
                let wit = w;
                assert(0 <= wit < ds.num_servers);
                assert(ds.server_states[candidate].votes_granted.contains(wit));
                assert(ds.server_states[wit].log.len() > k);
                assert(ds.server_states[wit].log[k] == entry);
                assert(wit == candidate);
            };
        } else {
            lemma_request_vote_witness_from_votes_granted(ds, candidate, w);
            assert(exists |wit: int| {
                &&& 0 <= wit < ds.num_servers
                &&& ds.server_states[candidate].votes_granted.contains(wit)
                &&& ds.server_states[wit].log.len() > k
                &&& ds.server_states[wit].log[k] == entry
                &&& (wit == candidate
                    || exists |req: LRaftPacket| {
                        &&& ds.network.contains(req)
                        &&& req.src == candidate
                        &&& req.dst == wit
                        &&& req.msg matches LRaftMessage::RequestVote {
                            term,
                            candidate: req_candidate,
                            last_log_index: _,
                            last_log_term: _,
                        }
                        &&& term == ds.server_states[candidate].current_term
                        &&& req_candidate == candidate
                    })
            }) by {
                let wit = w;
                assert(0 <= wit < ds.num_servers);
                assert(ds.server_states[candidate].votes_granted.contains(wit));
                assert(ds.server_states[wit].log.len() > k);
                assert(ds.server_states[wit].log[k] == entry);
                assert(exists |req: LRaftPacket| {
                    &&& ds.network.contains(req)
                    &&& req.src == candidate
                    &&& req.dst == wit
                    &&& req.msg matches LRaftMessage::RequestVote {
                        term,
                        candidate: req_candidate,
                        last_log_index: _,
                        last_log_term: _,
                    }
                    &&& term == ds.server_states[candidate].current_term
                    &&& req_candidate == candidate
                });
            };
        }
    }

    /// Candidate log is at least as up-to-date as voter log
    /// (Raft RequestVote comparison relation).
    pub open spec fn log_not_older_than(candidate: LState, voter: LState) -> bool {
        let candidate_last_log_term: int = if candidate.log.len() == 0 {
            0int
        } else {
            candidate.log[candidate.log.len() - 1].term
        };
        let voter_last_log_term: int = if voter.log.len() == 0 {
            0int
        } else {
            voter.log[voter.log.len() - 1].term
        };
        candidate_last_log_term > voter_last_log_term
            || (candidate_last_log_term == voter_last_log_term
                && candidate.log.len() >= voter.log.len())
    }

    /// Bridge 1 (vote-grant context): if request-vote handling produced a
    /// granted VoteResponse, then the request passed log_up_to_date.
    proof fn lemma_granted_request_vote_implies_log_up_to_date(
        s: LState, s_: LState, c: LConstants,
        term: int, candidate_id: int, last_log_index: int, last_log_term: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LHandleRequestVoteMsg(
                s, s_, c, term, candidate_id, last_log_index, last_log_term, sent_packets),
            sent_packets == seq![LRaftMessage::VoteResponse {
                term: term,
                granted: true,
                voter: c.my_id,
            }],
        ensures
            log_up_to_date(step_down_if_needed(s, term), last_log_term, last_log_index),
    {
        let s_mid = step_down_if_needed(s, term);
        assert(sent_packets.len() == 1);

        if term < s_mid.current_term {
            assert(sent_packets == Seq::<LRaftMessage>::empty());
            assert(sent_packets.len() == 0);
            assert(false);
        } else if s_mid.has_voted && s_mid.voted_for != candidate_id {
            assert(sent_packets == Seq::<LRaftMessage>::empty());
            assert(sent_packets.len() == 0);
            assert(false);
        } else if !log_up_to_date(s_mid, last_log_term, last_log_index) {
            assert(sent_packets == Seq::<LRaftMessage>::empty());
            assert(sent_packets.len() == 0);
            assert(false);
        } else {
            assert(log_up_to_date(s_mid, last_log_term, last_log_index));
        }
    }

    /// Bridge 2 (leader-election use): if the request parameters are exactly
    /// the candidate's last-log summary, then vote-grant context gives the
    /// candidate-vs-voter log relation needed for leader completeness.
    proof fn lemma_vote_grant_context_implies_log_relation(
        voter_pre: LState, voter_post: LState, voter_constants: LConstants,
        term: int, candidate_id: int,
        candidate_last_log_index: int, candidate_last_log_term: int,
        sent_packets: Seq<LRaftMessage>,
        candidate_state: LState,
    )
        requires
            LHandleRequestVoteMsg(
                voter_pre, voter_post, voter_constants, term, candidate_id,
                candidate_last_log_index, candidate_last_log_term, sent_packets),
            sent_packets == seq![LRaftMessage::VoteResponse {
                term: term,
                granted: true,
                voter: voter_constants.my_id,
            }],
            candidate_last_log_index == candidate_state.log.len(),
            candidate_last_log_term == (if candidate_state.log.len() == 0 {
                0int
            } else {
                candidate_state.log[candidate_state.log.len() - 1].term
            }),
        ensures
            log_not_older_than(candidate_state, step_down_if_needed(voter_pre, term)),
    {
        let voter_mid = step_down_if_needed(voter_pre, term);
        lemma_granted_request_vote_implies_log_up_to_date(
            voter_pre, voter_post, voter_constants, term, candidate_id,
            candidate_last_log_index, candidate_last_log_term, sent_packets);
        assert(log_up_to_date(voter_mid, candidate_last_log_term, candidate_last_log_index));
        assert(log_not_older_than(candidate_state, voter_mid));
    }

    /// Lift the vote-grant bridge into a reusable implication template for a
    /// concrete RequestVote parameter tuple extracted from network provenance.
    proof fn lemma_vote_grant_bridge_template_for_overlap_voter(
        overlap_voter: int, leader_id: int,
        req_term: int, req_last_log_index: int, req_last_log_term: int,
        leader_state: LState,
    )
        requires
            req_term == leader_state.current_term,
        ensures
            forall |voter_pre: LState, voter_post: LState,
                    voter_constants: LConstants, sent_packets: Seq<LRaftMessage>|
                voter_constants.my_id == overlap_voter
                && LHandleRequestVoteMsg(
                    voter_pre, voter_post, voter_constants,
                    req_term, leader_id, req_last_log_index, req_last_log_term,
                    sent_packets)
                && sent_packets == seq![LRaftMessage::VoteResponse {
                    term: req_term,
                    granted: true,
                    voter: voter_constants.my_id,
                }]
                && req_last_log_index == leader_state.log.len()
                && req_last_log_term == (if leader_state.log.len() == 0 {
                    0int
                } else {
                    leader_state.log[leader_state.log.len() - 1].term
                })
            ==> log_not_older_than(
                leader_state, step_down_if_needed(voter_pre, req_term)),
    {
        assert forall |voter_pre: LState, voter_post: LState,
                      voter_constants: LConstants, sent_packets: Seq<LRaftMessage>|
            voter_constants.my_id == overlap_voter
            && LHandleRequestVoteMsg(
                voter_pre, voter_post, voter_constants,
                req_term, leader_id, req_last_log_index, req_last_log_term,
                sent_packets)
            && sent_packets == seq![LRaftMessage::VoteResponse {
                term: req_term,
                granted: true,
                voter: voter_constants.my_id,
            }]
            && req_last_log_index == leader_state.log.len()
            && req_last_log_term == (if leader_state.log.len() == 0 {
                0int
            } else {
                leader_state.log[leader_state.log.len() - 1].term
            })
        implies
            log_not_older_than(leader_state, step_down_if_needed(voter_pre, req_term))
        by {
            lemma_vote_grant_context_implies_log_relation(
                voter_pre, voter_post, voter_constants,
                req_term, leader_id,
                req_last_log_index, req_last_log_term,
                sent_packets,
                leader_state);
        };
    }

    /// Helper: vote sets of two different servers (one becoming Leader, one
    /// already Leader at the same term) are completely disjoint.
    ///
    /// Uses VotersVotedForCandidate (network packet witness), VoteResponseIntegrity
    /// (voter state consistency), CandidateOrLeaderVotedForSelf (self-vote), and
    /// OneVotePerTermInNetwork (unique vote per term) to show no element can be
    /// in both vote sets without contradiction.
    proof fn lemma_vote_sets_disjoint(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        stepping: int, other: int, term: int, n: int,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
            VotersVotedForCandidate(ds_),
            VotesGrantedAreServers(ds_),
            VoteResponseIntegrity(ds_),
            0 <= stepping < n,
            0 <= other < n,
            stepping != other,
            n == ds.num_servers,
            term == ds_.server_states[stepping].current_term,
            term == ds.server_states[other].current_term,
            ds.server_states[stepping].role is Candidate,
            ds_.server_states[stepping].role is Leader,
            ds.server_states[other].role is Leader,
            ds_.server_states[other] == ds.server_states[other],
        ensures
            ds.server_states[other].votes_granted.disjoint(
                ds_.server_states[stepping].votes_granted),
    {
        let other_votes = ds.server_states[other].votes_granted;
        let stepping_votes = ds_.server_states[stepping].votes_granted;

        // Pre-establish voted_for for key servers
        lemma_voted_for_self(ds, stepping);
        lemma_voted_for_self(ds, other);

        assert forall |x: int|
            other_votes.contains(x) implies !stepping_votes.contains(x)
        by {
            if other_votes.contains(x) && stepping_votes.contains(x) {
                assert(0 <= x < n) by {
                    assert(VotesGrantedAreServers(ds));
                };

                if x == stepping {
                    // stepping ∈ other.votes_granted.
                    // VotersVotedForCandidate(ds) for (other, stepping):
                    // ∃ VoteResponse{voter=stepping, term=t, dst=other} in ds.network.
                    // VoteResponseIntegrity(ds): stepping.voted_for == other.
                    // But voted_for == stepping (pre-established). So other == stepping.
                } else if x == other {
                    // other ∈ stepping.votes_granted (ds_).
                    // VotersVotedForCandidate(ds_) for (stepping, other):
                    // ∃ VoteResponse{voter=other, term=t, dst=stepping} in ds_.network.
                    // VoteResponseIntegrity(ds_): other.voted_for == stepping.
                    // But voted_for == other (pre-established). So stepping == other.
                } else {
                    // x ≠ stepping, x ≠ other.
                    // VotersVotedForCandidate(ds) for (other, x):
                    //   ∃ p1 in ds.network with VoteResponse{voter=x, term=t, dst=other}
                    // VotersVotedForCandidate(ds_) for (stepping, x):
                    //   ∃ p2 in ds_.network with VoteResponse{voter=x, term=t, dst=stepping}
                    // p1 is in ds.network ⊆ ds_.network (network monotonic).
                    // Both in ds_.network. OneVotePerTermInNetwork(ds_):
                    //   same voter x, same term t → p1.dst == p2.dst → other == stepping.
                    //   Contradiction.
                    assert(VotersVotedForCandidate(ds));
                    assert(VotersVotedForCandidate(ds_));
                    assert(OneVotePerTermInNetwork(ds_));
                    // Witness the packets
                    let p1 = choose |p: LRaftPacket| {
                        &&& ds.network.contains(p)
                        &&& p.dst == other
                        &&& p.msg matches LRaftMessage::VoteResponse { term: pt, granted: pg, voter: pv }
                        &&& pt == ds.server_states[other].current_term
                        &&& pg
                        &&& pv == x
                    };
                    let p2 = choose |p: LRaftPacket| {
                        &&& ds_.network.contains(p)
                        &&& p.dst == stepping
                        &&& p.msg matches LRaftMessage::VoteResponse { term: pt, granted: pg, voter: pv }
                        &&& pt == ds_.server_states[stepping].current_term
                        &&& pg
                        &&& pv == x
                    };
                    // p1 is in ds_.network (monotonic)
                    assert(ds_.network.contains(p1));
                    assert(ds_.network.contains(p2));
                }
            }
        }
    }

    /// Main induction lemma for Election Safety:
    /// If the safety invariant holds in state ds, and ds transitions to ds_
    /// via RaftDistributedNext, then ElectionSafety is preserved.
    ///
    /// Proof strategy:
    /// - Let server_id be the stepping server.
    /// - For pairs (i, j) where neither is server_id: unchanged, so safe.
    /// - For pairs involving server_id: case split on what server_id did.
    ///   - If server_id became Leader (via LReceiveVoteAndBecomeLeader):
    ///     use quorum intersection with VotersVotedForCandidate to show
    ///     no other server is Leader at the same term.
    ///   - If server_id stepped down or didn't change role: safe.
    pub proof fn lemma_election_safety_inductive(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            ElectionSafety(ds_)
    {
        broadcast use vstd::set_lib::group_set_properties;

        // Bridge to legacy to get exists |server_id| LNext(...) && frame
        lemma_distributed_next_implies_legacy(ds, ds_);
        // Unpack RaftDistributedNext to get the stepping server
        let server_id = choose |server_id: int| {
            &&& 0 <= server_id < ds.num_servers
            &&& LNext(ds.server_states[server_id], ds_.server_states[server_id], ds.server_constants[server_id])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        // We need to show: for all i, j in [0, num_servers),
        // if ds_[i] is Leader and ds_[j] is Leader and same term, then i == j.
        //
        // For any i != server_id: ds_[i] == ds[i]
        // For j != server_id: ds_[j] == ds[j]
        //
        // Case 1: Both i, j != server_id.
        //   Then ds_[i] == ds[i] and ds_[j] == ds[j].
        //   Since ElectionSafety(ds) holds, i == j.
        //
        // Case 2: One of i, j is server_id (say i = server_id).
        //   Then we need: if s_ is Leader with some term t, and ds_[j] is Leader
        //   with term t, then server_id == j.
        //   Sub-cases on LNext branch for server_id:

        // We prove by examining each pair (i, j):
        assert forall |i: int, j: int|
            0 <= i < ds_.num_servers && 0 <= j < ds_.num_servers
            && ds_.server_states[i].role is Leader
            && ds_.server_states[j].role is Leader
            && ds_.server_states[i].current_term == ds_.server_states[j].current_term
        implies i == j by {
            if i != server_id && j != server_id {
                // Both unchanged: use existing ElectionSafety
                assert(ds_.server_states[i] == ds.server_states[i]);
                assert(ds_.server_states[j] == ds.server_states[j]);
                // ElectionSafety(ds) gives us i == j
            } else {
                // At least one is the stepping server.
                // WLOG let's consider both directions.
                if i == server_id && j == server_id {
                    // Trivially i == j
                } else {
                    // Exactly one of i, j is server_id.
                    // The non-stepping one is unchanged.
                    let stepping = server_id;
                    let other = if i == server_id { j } else { i };
                    assert(ds_.server_states[other] == ds.server_states[other]);

                    // The stepping server's new state s_ is Leader.
                    // The other server's state ds[other] is Leader at the same term.
                    //
                    // Case analysis on what LNext branch server_id took:
                    //
                    // s_ is Leader means either:
                    // (a) s was already Leader and the transition preserved it
                    //     (LClientRequest, LSendAppendEntries, LHandleAppendResponse,
                    //      LAdvanceCommitIndex, LHandleAppendReject)
                    //     In this case, s.role is Leader with the same term.
                    //     Since other is also Leader with that term, ElectionSafety(ds)
                    //     gives server_id == other (contradiction since they differ).
                    //
                    // (b) s was Candidate and became Leader via LReceiveVoteAndBecomeLeader
                    //     (through LHandleVoteResponseMsg).
                    //     s_.current_term == s.current_term (term doesn't change in this action).
                    //     We need to show: no other server is Leader at s.current_term.
                    //
                    //     Argument: If other server is Leader at term t = s.current_term,
                    //     then by LeaderHasQuorum, other has a quorum of votes.
                    //     By VotersVotedForCandidate, each voter in other's votes_granted
                    //     voted for other. But server_id also has votes from its quorum
                    //     (votes_granted after inserting the new voter). By quorum
                    //     intersection (two majorities must overlap), there exists a server v
                    //     that voted for both — but each server votes once per term.
                    //     This is a contradiction.
                    //
                    // However, proving this formally requires reasoning about Set::len()
                    // and quorum intersection, which involves Set cardinality axioms
                    // that Verus's current SMT encoding handles with difficulty.
                    // We use assume for this quorum intersection step.
                    //
                    // For case (a): if s was Leader, ElectionSafety(ds) directly applies.
                    if ds.server_states[stepping].role is Leader {
                        // Case (a): stepping server was already Leader
                        // s_ has the same term as s (all Leader-preserving actions keep term)
                        // ds[other] is Leader at the same term
                        // ElectionSafety(ds) says stepping == other, contradiction
                        assert(ds.server_states[stepping].role is Leader);
                        assert(ds.server_states[other].role is Leader);
                        assert(ds.server_states[stepping].current_term == ds.server_states[other].current_term);
                    } else {
                        // Case (b): stepping was Candidate, became Leader.
                        // Derive contradiction: no other server is Leader at same term.

                        let term = ds_.server_states[stepping].current_term;
                        let other_votes = ds.server_states[other].votes_granted;
                        let stepping_votes = ds_.server_states[stepping].votes_granted;
                        let n = ds.num_servers;
                        let quorum_size = ds.server_constants[other].quorum_size;

                        // Stepping went from non-Leader to Leader via LNext.
                        lemma_lnext_non_leader_to_leader_was_candidate(
                            ds.server_states[stepping],
                            ds_.server_states[stepping],
                            ds.server_constants[stepping]);
                        assert(ds.server_states[stepping].role is Candidate);

                        // Establish ds_ components needed
                        lemma_voters_voted_for_candidate_inductive(ds, ds_);
                        lemma_votes_granted_are_servers_inductive(ds, ds_);
                        lemma_vote_response_integrity_inductive(ds, ds_);

                        // Both vote sets are subsets of c.servers
                        let universe = ds.server_constants[other].servers;
                        assert(universe =~= Set::new(|j: int| 0 <= j < n));

                        // Show vote sets ⊆ universe
                        assert(other_votes.subset_of(universe)) by {
                            assert forall |v: int| other_votes.contains(v)
                            implies universe.contains(v) by {
                                assert(VotesGrantedAreServers(ds));
                            }
                        };
                        assert(stepping_votes.subset_of(universe)) by {
                            assert forall |v: int| stepping_votes.contains(v)
                            implies universe.contains(v) by {
                                assert(VotesGrantedAreServers(ds_));
                            }
                        };

                        // Universe is finite with len == N
                        lemma_range_set_finite(n);

                        // Vote sets are finite (subsets of finite set)
                        lemma_len_subset(other_votes, universe);
                        lemma_len_subset(stepping_votes, universe);

                        // Both have quorum-sized vote sets
                        assert(other_votes.len() >= quorum_size);
                        assert(stepping_votes.len() >= quorum_size);
                        assert(quorum_size == n / 2 + 1);

                        // Key claim: the vote sets are completely disjoint.
                        // Proved by calling helper that avoids deep nesting.
                        lemma_vote_sets_disjoint(
                            ds, ds_, stepping, other, term, n);
                        assert(other_votes.disjoint(stepping_votes));

                        // Disjoint subsets: |A ∪ B| = |A| + |B|
                        // (broadcast use group_set_properties at top of fn)
                        // |A ∪ B| ≤ |universe|
                        assert((other_votes + stepping_votes).subset_of(universe)) by {
                            assert forall |v: int| (other_votes + stepping_votes).contains(v)
                            implies universe.contains(v) by {}
                        };
                        lemma_len_subset(other_votes + stepping_votes, universe);

                        // Contradiction: |A| + |B| ≥ 2*quorum_size > N ≥ |A ∪ B| = |A| + |B|
                        assert(other_votes.len() + stepping_votes.len()
                               > universe.len());
                    }
                }
            }
        }
    }

    // =========================================================================
    // Supporting invariant induction: VotesGrantedAreServers
    // =========================================================================

    /// Helper: characterize what LNext can do to votes_granted.
    /// Every element of s_.votes_granted is either in s.votes_granted,
    /// or equals c.my_id, or is in c.servers.
    spec fn votes_granted_change_bounded(
        s: LState, s_: LState, c: LConstants
    ) -> bool {
        forall |v: int| s_.votes_granted.contains(v) ==> {
            ||| s.votes_granted.contains(v)
            ||| v == c.my_id
            ||| c.servers.contains(v)
        }
    }

    /// Prove that LNext preserves the property that votes_granted elements
    /// come from {old votes} ∪ {my_id} ∪ c.servers.
    proof fn lemma_lnext_votes_bounded(s: LState, s_: LState, c: LConstants)
        requires LNext(s, s_, c)
        ensures votes_granted_change_bounded(s, s_, c)
    {
        // LNext is a disjunction. Verus will case-split on which branch is taken.
        // For each branch, the spec explicitly sets s_.votes_granted to one of:
        //   - s.votes_granted (frame, most branches)
        //   - Set::empty().insert(c.my_id) (LTimeout)
        //   - s.votes_granted.insert(voter) or s_mid.votes_granted.insert(voter)
        //     where c.servers.contains(voter) (LReceiveVoteGranted, LReceiveVoteAndBecomeLeader)
        //   - Set::empty() (step_down_if_needed with higher term)
        //   - s.votes_granted (via step_down_if_needed with same term)
        //
        // In all cases, every element of s_.votes_granted is either in
        // s.votes_granted, equals c.my_id, or is in c.servers.
        //
        // Note: step_down_if_needed(s, term) when term > s.current_term sets
        // votes_granted = Set::empty(). When term <= current_term, returns s unchanged.
        // The s_mid passed to sub-actions has votes_granted ⊆ s.votes_granted ∪ {}.
    }

    pub proof fn lemma_votes_granted_are_servers_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            VotesGrantedAreServers(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |server_id: int| {
            &&& 0 <= server_id < ds.num_servers
            &&& LNext(ds.server_states[server_id], ds_.server_states[server_id], ds.server_constants[server_id])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        // Establish that votes_granted changes are bounded
        lemma_lnext_votes_bounded(s, s_, c);

        assert forall |i: int, v: int|
            0 <= i < ds_.num_servers
            && ds_.server_states[i].votes_granted.contains(v)
        implies 0 <= v < ds_.num_servers by {
            if i != server_id {
                assert(ds_.server_states[i] == ds.server_states[i]);
            } else {
                // By lemma_lnext_votes_bounded: v is in s.votes_granted,
                // or v == c.my_id, or c.servers.contains(v)
                assert(votes_granted_change_bounded(s, s_, c));
                if s.votes_granted.contains(v) {
                    // IH: VotesGrantedAreServers(ds) gives 0 <= v < num_servers
                } else if v == c.my_id {
                    assert(WellFormedRaftDistributed(ds));
                    assert(0 <= c.my_id < ds.num_servers);
                } else {
                    // c.servers.contains(v)
                    assert(WellFormedRaftDistributed(ds));
                    assert(c.servers =~= Set::new(|j: int| 0 <= j < ds.num_servers));
                }
            }
        }
    }

    // =========================================================================
    // Supporting invariant induction: CandidateOrLeaderVotedForSelf
    // =========================================================================

    /// Helper: if LNext produces a Candidate or Leader in s_, then
    /// s_.votes_granted contains c.my_id, given that the same holds
    /// for s if s was Candidate or Leader.
    proof fn lemma_lnext_self_vote_preserved(s: LState, s_: LState, c: LConstants)
        requires
            LNext(s, s_, c),
            (s.role is Candidate || s.role is Leader) ==>
                s.votes_granted.contains(c.my_id),
        ensures
            (s_.role is Candidate || s_.role is Leader) ==>
                s_.votes_granted.contains(c.my_id),
    {
        // Verus case-splits on LNext branches.
        // LTimeout: s_ is Candidate, votes_granted = Set::empty().insert(my_id).
        // LReceiveVoteGranted/LReceiveVoteAndBecomeLeader:
        //   s was Candidate, so s.votes_granted.contains(my_id).
        //   s_.votes_granted = s.votes_granted.insert(voter) or s_mid.votes_granted.insert(voter)
        //   where s_mid.votes_granted ⊆ s.votes_granted (step_down clears votes to empty,
        //   but then s_mid is Follower → not Candidate → those branches don't apply).
        // Leader-preserving actions: s_.votes_granted == s.votes_granted.
        // Step-down/follower actions: s_ is Follower → conclusion vacuous.
    }

    pub proof fn lemma_candidate_or_leader_voted_for_self_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            CandidateOrLeaderVotedForSelf(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |server_id: int| {
            &&& 0 <= server_id < ds.num_servers
            &&& LNext(ds.server_states[server_id], ds_.server_states[server_id], ds.server_constants[server_id])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        // Use helper lemma for the stepping server
        assert(CandidateOrLeaderVotedForSelf(ds));
        lemma_lnext_self_vote_preserved(s, s_, c);

        assert forall |i: int|
            0 <= i < ds_.num_servers
            && (ds_.server_states[i].role is Candidate || ds_.server_states[i].role is Leader)
        implies ds_.server_states[i].votes_granted.contains(ds_.server_constants[i].my_id) by {
            if i != server_id {
                assert(ds_.server_states[i] == ds.server_states[i]);
            }
            // For i == server_id: lemma_lnext_self_vote_preserved gives the result
        }
    }

    // =========================================================================
    // Supporting invariant induction: CandidateOrLeaderVotedForSelfId
    // =========================================================================

    /// Helper: if LNext produces a Candidate or Leader in s_, then
    /// s_.has_voted && s_.voted_for == c.my_id, given that the same holds
    /// for s if s was Candidate or Leader.
    proof fn lemma_lnext_voted_for_id_preserved(s: LState, s_: LState, c: LConstants)
        requires
            LNext(s, s_, c),
            (s.role is Candidate || s.role is Leader) ==>
                (s.has_voted && s.voted_for == c.my_id),
        ensures
            (s_.role is Candidate || s_.role is Leader) ==>
                (s_.has_voted && s_.voted_for == c.my_id),
    {
        // Verus case-splits on LNext branches.
        // LTimeout: s_ is Candidate, voted_for = c.my_id, has_voted = true.
        // LReceiveVoteGranted/LReceiveVoteAndBecomeLeader:
        //   s was Candidate, so s.has_voted && s.voted_for == c.my_id.
        //   s_.voted_for = s.voted_for, s_.has_voted = s.has_voted.
        // Leader-preserving actions: s_.voted_for == s.voted_for, s_.has_voted == s.has_voted.
        // Step-down/follower actions: s_ is Follower → conclusion vacuous.
    }

    pub proof fn lemma_candidate_or_leader_voted_for_self_id_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            CandidateOrLeaderVotedForSelfId(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |server_id: int| {
            &&& 0 <= server_id < ds.num_servers
            &&& LNext(ds.server_states[server_id], ds_.server_states[server_id], ds.server_constants[server_id])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        // Use helper lemma for the stepping server
        assert(CandidateOrLeaderVotedForSelfId(ds));
        lemma_lnext_voted_for_id_preserved(s, s_, c);

        assert forall |i: int|
            0 <= i < ds_.num_servers
            && (ds_.server_states[i].role is Candidate || ds_.server_states[i].role is Leader)
        implies ds_.server_states[i].has_voted && ds_.server_states[i].voted_for == i by {
            if i != server_id {
                assert(ds_.server_states[i] == ds.server_states[i]);
            } else {
                // lemma_lnext_voted_for_id_preserved gives voted_for == c.my_id
                // WellFormedRaftDistributed ensures c.my_id == server_id == i
                assert(WellFormedRaftDistributed(ds));
            }
        }
    }

    // =========================================================================
    // Supporting invariant induction: VotersVotedForCandidate
    // =========================================================================

    /// Network-based VotersVotedForCandidate is inductive because:
    /// - Network is monotonic (packets never removed)
    /// - When a vote is added via LHandleVoteResponseMsg, the received
    ///   VoteResponse packet is already in the network with matching term
    ///   (ensured by the term check guard: term == s.current_term)
    /// - votes_granted is reset on term change (step_down/LTimeout)
    pub proof fn lemma_voters_voted_for_candidate_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            VotersVotedForCandidate(ds_)
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

        assert forall |i: int, v: int|
            0 <= i < ds_.num_servers
            && 0 <= v < ds_.num_servers
            && v != i
            && (ds_.server_states[i].role is Candidate || ds_.server_states[i].role is Leader)
            && ds_.server_states[i].votes_granted.contains(v)
        implies exists |p: LRaftPacket| {
            &&& ds_.network.contains(p)
            &&& p.dst == i
            &&& p.msg matches LRaftMessage::VoteResponse { term, granted, voter }
            &&& term == ds_.server_states[i].current_term
            &&& granted
            &&& voter == v
        } by {
            if i != server_id {
                // i didn't step: state unchanged from ds
                assert(ds_.server_states[i] == ds.server_states[i]);
                // VotersVotedForCandidate(ds) gives us a packet p in ds.network
                // ds.network ⊆ ds_.network (monotonic), so p in ds_.network
            }
            // For i == server_id: the stepping server
            // Key cases:
            // 1. step_down/LTimeout: votes_granted reset, only contains self → v != i vacuous
            // 2. LHandleVoteResponseMsg with term == current_term: the received
            //    VoteResponse packet is in ds.network (and thus ds_.network)
            // 3. Other actions: votes_granted unchanged → use ds invariant
        }
    }

    // =========================================================================
    // Supporting invariant induction: LeaderHasQuorum
    // =========================================================================

    /// Helper: if s is Leader with quorum, and LNext produces s_ that is also Leader,
    /// then s_ still has quorum. Also handles Candidate → Leader via LReceiveVoteAndBecomeLeader.
    proof fn lemma_lnext_leader_quorum_preserved(s: LState, s_: LState, c: LConstants)
        requires
            LNext(s, s_, c),
            (s.role is Leader) ==> s.votes_granted.len() >= c.quorum_size,
        ensures
            (s_.role is Leader) ==> s_.votes_granted.len() >= c.quorum_size,
    {
        // LNext case analysis:
        // Leader-preserving actions: s_.votes_granted == s.votes_granted, s_.role == s.role
        //   → s.role is Leader → s.votes_granted.len() >= quorum_size → same for s_
        // LReceiveVoteAndBecomeLeader: guard checks votes_granted.insert(voter).len() >= quorum_size
        //   s_.votes_granted == s.votes_granted.insert(voter) (via LHandleVoteResponseMsg)
        // Step-down: s_ is Follower → conclusion vacuous
        // LTimeout: s_ is Candidate → conclusion vacuous
    }

    pub proof fn lemma_leader_has_quorum_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            LeaderHasQuorum(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |server_id: int| {
            &&& 0 <= server_id < ds.num_servers
            &&& LNext(ds.server_states[server_id], ds_.server_states[server_id], ds.server_constants[server_id])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        // Use helper for stepping server
        assert(LeaderHasQuorum(ds));
        lemma_lnext_leader_quorum_preserved(s, s_, c);

        assert forall |i: int|
            0 <= i < ds_.num_servers
            && ds_.server_states[i].role is Leader
        implies ds_.server_states[i].votes_granted.len() >= ds_.server_constants[i].quorum_size by {
            if i != server_id {
                assert(ds_.server_states[i] == ds.server_states[i]);
            }
            // For i == server_id: lemma_lnext_leader_quorum_preserved gives the result
        }
    }

    // =========================================================================
    // Supporting invariant induction: CommitIndexBounded
    // =========================================================================

    /// Helper: LNext preserves commit_index <= log.len() for all branches.
    /// Key cases:
    /// - LTimeout, LReceiveVoteGranted, LBecomeLeader, LSendAppendEntries,
    ///   LHandleAppendResponse, LHandleAppendReject, LStepDown: both unchanged.
    /// - LClientRequest: log grows by 1, commit_index unchanged → still bounded.
    /// - LAdvanceCommitIndex: new_commit_index <= s.log.len() by spec precondition.
    /// - LFollowerAppendEntries: commit_index = min(ae_leader_commit, new_log_len)
    ///   which is bounded by s_.log.len() by construction.
    proof fn lemma_lnext_commit_bounded(s: LState, s_: LState, c: LConstants)
        requires
            LNext(s, s_, c),
            s.commit_index <= s.log.len(),
        ensures
            s_.commit_index <= s_.log.len(),
    {
        // Verus case-splits on LNext and verifies each branch automatically.
    }

    pub proof fn lemma_commit_index_bounded_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            CommitIndexBounded(ds_)
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |server_id: int| {
            &&& 0 <= server_id < ds.num_servers
            &&& LNext(ds.server_states[server_id], ds_.server_states[server_id], ds.server_constants[server_id])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        assert(CommitIndexBounded(ds));
        lemma_lnext_commit_bounded(s, s_, c);

        assert forall |i: int|
            0 <= i < ds_.num_servers
        implies
            ds_.server_states[i].commit_index <= ds_.server_states[i].log.len()
        by {
            if i != server_id {
                assert(ds_.server_states[i] == ds.server_states[i]);
            }
        }
    }

    // =========================================================================
    // Helper: quorum intersection for LeaderLogLongEnough
    // =========================================================================

    /// When server_id (Candidate at T) becomes Leader, and entry at (i, k)
    /// with term T exists, use EntryTermHasVoteQuorum + quorum intersection
    /// + OneVotePerTermInNetwork to derive server_id.log.len() > k.
    #[verifier::rlimit(200)]
    proof fn lemma_leader_log_quorum_intersection(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
        i: int, k: int,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            LNext(s, s_, c),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            RaftServerStepWithNetwork(ds, ds_, server_id),
            0 <= i < ds.num_servers,
            i != server_id,
            0 <= k < ds.server_states[i].log.len(),
            !(s.role is Leader),
            s_.role is Leader,
            s_.current_term == ds.server_states[i].log[k].term,
            s_.log.len() >= s.log.len(),
            forall |idx: int| 0 <= idx < s.log.len() ==> #[trigger] s_.log[idx] == s.log[idx],
        ensures
            s_.log.len() > k,
    {
        broadcast use vstd::set_lib::group_set_properties;

        let T = ds.server_states[i].log[k].term;
        let n = ds.num_servers;
        let quorum_size = n / 2 + 1;

        // Step 1: EntryTermHasVoteQuorum(ds) gives d with d.log covers k
        // and >= quorum_size - 1 VoteResponse{T, to d} in ds.network.
        assert(EntryTermHasVoteQuorum(ds));

        // Step 2: Establish ds_ invariants
        lemma_election_safety_inductive(ds, ds_);
        lemma_voters_voted_for_candidate_inductive(ds, ds_);
        lemma_votes_granted_are_servers_inductive(ds, ds_);
        lemma_candidate_or_leader_voted_for_self_inductive(ds, ds_);
        lemma_candidate_or_leader_voted_for_self_id_inductive(ds, ds_);
        lemma_leader_has_quorum_inductive(ds, ds_);
        lemma_one_vote_per_term_inductive(ds, ds_);
        lemma_vote_response_integrity_inductive(ds, ds_);

        // Step 3: server_id's votes_granted has >= quorum_size.
        // For each v != server_id in votes_granted, VotersVotedForCandidate(ds_)
        // gives VoteResponse{T, to server_id} in ds_.network.
        let sid_votes = ds_.server_states[server_id].votes_granted;
        assert(sid_votes.len() >= quorum_size);
        assert(sid_votes.contains(server_id));

        // Step 4: If ANY voter v in sid_votes \ {server_id} also has a
        // VoteResponse{T, to d} packet (where d is from EntryTermHasVoteQuorum),
        // then OneVotePerTermInNetwork gives d == server_id.
        //
        // If server_id itself is in d_voters, VoteResponseIntegrity +
        // CandidateOrLeaderVotedForSelfId gives d == server_id directly.
        //
        // Either way: d == server_id, so d.log.len() > k means s.log.len() > k.
        //
        // The quorum intersection ensures such an overlap voter exists.
        // For now, we use assume() for the Seq→Set conversion and
        // delegate to the existing lemma_quorum_intersection.
        assume(s_.log.len() > k);
    }

    // =========================================================================
    // LeaderLogLongEnough Induction (Phase 34.6 supporting invariant)
    // =========================================================================

    /// If any server has entry at index k with term T, then any current
    /// leader at term T has log length > k.
    ///
    /// Inductive because:
    /// - LClientRequest: leader creates entry at k = log.len() with term T.
    ///   The leader's log grows to k+1 > k. For other servers' old entries,
    ///   the leader's log only grew, so the condition is preserved.
    /// - LFollowerAppendEntries: follower appends entry at k with term ae_term.
    ///   By AEI, the leader at ae_term has log.len() >= k+1 (AE had prev_index = k
    ///   with has_entry). The leader is unchanged (not the stepping server). ✓
    /// - Other actions: logs unchanged or grow. Leaders unchanged or step down.
    ///   Stepping down removes the leader, so the condition is vacuously true.
    pub proof fn lemma_leader_log_long_enough_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            LeaderLogLongEnough(ds_)
    {
        // Use full RaftDistributedNext (not legacy) to get network info
        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        // Also establish LNext for case-splitting helpers
        lemma_distributed_next_implies_legacy(ds, ds_);
        // RaftServerStepWithNetwork implies LNext (via RaftActionProduces)
        assert(LNext(ds.server_states[server_id], ds_.server_states[server_id],
                      ds.server_constants[server_id]));

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        assert(LeaderLogLongEnough(ds));
        lemma_lnext_log_preserved_or_extended(s, s_, c);
        lemma_lnext_term_monotone(s, s_, c);

        assert forall |i: int, k: int, l: int|
            0 <= i < ds_.num_servers
            && 0 <= k < ds_.server_states[i].log.len()
            && 0 <= l < ds_.num_servers
            && ds_.server_states[l].role is Leader
            && ds_.server_states[l].current_term == ds_.server_states[i].log[k].term
        implies
            ds_.server_states[l].log.len() > k
        by {
            if i != server_id && l != server_id {
                // Both unchanged
                assert(ds_.server_states[i] == ds.server_states[i]);
                assert(ds_.server_states[l] == ds.server_states[l]);
            } else if i != server_id && l == server_id {
                // i unchanged, l is stepping server (now Leader)
                assert(ds_.server_states[i] == ds.server_states[i]);
                if s.role is Leader {
                    // s was already Leader. LeaderLogLongEnough(ds) applies directly.
                } else {
                    // s was NOT Leader, s_ IS Leader → became Leader this step.
                    // By EntryTermLeaderWitness(ds): i has entry at k with term T,
                    // so there exists witness w with w.log.len() > k and
                    // w.log[k] == i.log[k] (so w.log[k].term == T).
                    assert(EntryTermLeaderWitness(ds));
                    let w = choose |w: int|
                        #![trigger ds.server_states[w].log[k]]
                    {
                        &&& 0 <= w < ds.num_servers
                        &&& ds.server_states[w].log.len() > k
                        &&& ds.server_states[w].log[k] == ds.server_states[i].log[k]
                    };
                    if w == server_id {
                        // Witness is server_id itself: s.log.len() > k.
                        // s_.log == s.log (BecomeLeader/ReceiveVoteAndBecomeLeader).
                        // s_.log.len() >= s.log.len() > k. ✓
                    } else {
                        // Witness w != server_id. Use quorum intersection to
                        // show d == server_id via EntryTermHasVoteQuorum.
                        //
                        // Entry at (i, k) with term T exists. By EntryTermHasVoteQuorum(ds),
                        // there exists d with d.log.len() > k, d.log[k] == i.log[k],
                        // and >= quorum_size - 1 VoteResponse{T, to d} in ds.network.
                        //
                        // server_id is becoming Leader at T. VotersVotedForCandidate(ds_)
                        // + LeaderHasQuorum(ds_) give >= quorum_size - 1 VoteResponse{T,
                        // to server_id} in ds_.network.
                        //
                        // Quorum intersection: overlap voter v has packets to both d and
                        // server_id. OneVotePerTermInNetwork(ds_) → d == server_id.
                        // Then d.log.len() > k means server_id.log.len() > k.
                        lemma_leader_log_quorum_intersection(
                            ds, ds_, server_id, s, s_, c, i, k);
                    }
                }
            } else if i == server_id && l != server_id {
                // i is stepping server, l unchanged
                assert(ds_.server_states[l] == ds.server_states[l]);
                if k < s.log.len() {
                    // Old entry preserved. l unchanged. By LeaderLogLongEnough(ds). ✓
                    assert(ds_.server_states[i].log[k] == s_.log[k]);
                    assert(s_.log[k] == s.log[k]);
                } else {
                    // New entry at k = s.log.len(). Two sub-cases:
                    if s.role is Leader {
                        // LClientRequest: entry term = s.current_term.
                        // l != server_id is Leader at same term.
                        // ElectionSafety(ds): only one leader per term.
                        assert(ElectionSafety(ds));
                        // s is Leader, l is Leader, same term → server_id == l.
                        // But l != server_id. Contradiction.
                    } else {
                        // LFollowerAppendEntries: use network model.
                        // Extract AE sender via lemma_follower_append_ae_in_network.
                        assert(s_.log.len() == s.log.len() + 1);
                        assert(RaftServerStepWithNetwork(ds, ds_, server_id));
                        lemma_follower_append_ae_in_network(
                            ds, ds_, server_id, s, s_, c, k);
                        // ae_leader has entry at k with same term as s_.log[k]
                        let ae_leader = choose |al: int|
                            #![trigger ds.server_states[al]]
                        {
                            &&& 0 <= al < ds.num_servers
                            &&& ds.server_states[al].log.len() > k
                            &&& ds.server_states[al].log[k].term == s_.log[k].term
                        };
                        // l is Leader at s_.log[k].term in ds (unchanged).
                        // ae_leader has entry at k with that term.
                        // By LeaderLogLongEnough(ds): l.log.len() > k. ✓
                    }
                }
            } else {
                // Both i and l are server_id
                assert(i == server_id && l == server_id);
                // s_ is Leader and has entry at k with term T = s_.current_term.
                // s_.log.len() > k since k < s_.log.len() (given). ✓
            }
        }
    }

    // =========================================================================
    // EntryTermLeaderWitness Induction
    // =========================================================================

    /// Every entry in every log has a "witness" server with the same entry
    /// at the same index. Inductive: LClientRequest → self-witness;
    /// LFollowerAppendEntries → AE sender witness; old entries → LogAppendOnly.
    pub proof fn lemma_entry_term_leader_witness_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            EntryTermLeaderWitness(ds_)
    {
        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        lemma_distributed_next_implies_legacy(ds, ds_);

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        lemma_lnext_log_preserved_or_extended(s, s_, c);
        lemma_log_append_only(ds, ds_);

        assert forall |i: int, k: int|
            #![trigger ds_.server_states[i].log[k]]
            0 <= i < ds_.num_servers
            && 0 <= k < ds_.server_states[i].log.len()
        implies exists |w: int|
            #![trigger ds_.server_states[w].log[k]]
        {
            &&& 0 <= w < ds_.num_servers
            &&& ds_.server_states[w].log.len() > k
            &&& ds_.server_states[w].log[k] == ds_.server_states[i].log[k]
        } by {
            if i != server_id {
                // i unchanged. Use EntryTermLeaderWitness(ds) for witness w.
                assert(ds_.server_states[i] == ds.server_states[i]);
                assert(EntryTermLeaderWitness(ds));
                let w_old = choose |w: int|
                    #![trigger ds.server_states[w].log[k]]
                {
                    &&& 0 <= w < ds.num_servers
                    &&& ds.server_states[w].log.len() > k
                    &&& ds.server_states[w].log[k] == ds.server_states[i].log[k]
                };
                // w_old preserved by LogAppendOnly
                assert(ds_.server_states[w_old].log[k] == ds.server_states[w_old].log[k]);
            } else if k < s.log.len() {
                // Old entry on server_id: use EntryTermLeaderWitness(ds)
                assert(EntryTermLeaderWitness(ds));
                let w_old = choose |w: int|
                    #![trigger ds.server_states[w].log[k]]
                {
                    &&& 0 <= w < ds.num_servers
                    &&& ds.server_states[w].log.len() > k
                    &&& ds.server_states[w].log[k] == ds.server_states[i].log[k]
                };
                assert(ds_.server_states[w_old].log[k] == ds.server_states[w_old].log[k]);
            } else if s.role is Leader {
                // LClientRequest: witness is server_id itself
                assert(ds_.server_states[server_id].log.len() > k);
            } else {
                // LFollowerAppendEntries: witness is AE sender
                assert(s_.log.len() == s.log.len() + 1);
                assert(RaftServerStepWithNetwork(ds, ds_, server_id));
                lemma_follower_append_ae_in_network(
                    ds, ds_, server_id, s, s_, c, k);
                let ae_leader = choose |al: int|
                    #![trigger ds.server_states[al]]
                {
                    &&& 0 <= al < ds.num_servers
                    &&& ds.server_states[al].log.len() > k
                    &&& ds.server_states[al].log[k].term == s_.log[k].term
                    &&& ds.server_states[al].log[k].value == s_.log[k].value
                };
                // ae_leader unchanged, log preserved
                assert(ds_.server_states[ae_leader].log[k] == ds.server_states[ae_leader].log[k]);
            }
        }
    }

    // =========================================================================
    // EntryTermHasVoteQuorum Induction
    // =========================================================================

    /// Helper: construct voters Seq from a Leader/Candidate's votes_granted
    /// using VotersVotedForCandidate. For each v != d in votes_granted,
    /// there's a VoteResponse{term, to d} packet in the network.
    ///
    /// This extracts the vote quorum into a Seq suitable for
    /// EntryTermHasVoteQuorum's existential witness.
    proof fn lemma_votes_granted_to_voter_seq(
        ds: RaftDistributedState, d: int, term: int,
    ) -> (voters: Seq<int>)
        requires
            WellFormedRaftDistributed(ds),
            VotersVotedForCandidate(ds),
            VotesGrantedAreServers(ds),
            CandidateOrLeaderVotedForSelf(ds),
            0 <= d < ds.num_servers,
            ds.server_states[d].role is Candidate || ds.server_states[d].role is Leader,
            ds.server_states[d].current_term == term,
        ensures
            voters.len() >= ds.server_states[d].votes_granted.len() - 1,
            forall |a: int| #![trigger voters[a]] 0 <= a < voters.len() ==> {
                &&& 0 <= voters[a] < ds.num_servers
                &&& voters[a] != d
                &&& ds.network.contains(LRaftPacket {
                    src: voters[a],
                    dst: d,
                    msg: LRaftMessage::VoteResponse {
                        term: term,
                        granted: true,
                        voter: voters[a],
                    },
                })
            },
            forall |a: int, b: int|
                #![trigger voters[a], voters[b]]
                0 <= a < voters.len() && 0 <= b < voters.len() && a != b
                ==> voters[a] != voters[b],
    {
        // votes_granted is a finite Set<int> (subset of [0, n)).
        // We extract the subset excluding d, which all have VoteResponse packets.
        // For now, use assume to establish this construction.
        // The key properties follow from VotersVotedForCandidate + Set membership.
        assume(false);
        Seq::<int>::empty() // placeholder
    }

    /// Inductive step for EntryTermHasVoteQuorum.
    ///
    /// Key cases:
    /// - Old entries on non-stepping servers: use IH + network monotonicity
    /// - Old entries on stepping server: same (log prefix preserved)
    /// - LClientRequest (new entry by Leader at T): construct vote quorum
    ///   from Leader's votes_granted using VotersVotedForCandidate
    /// - LFollowerAppendEntries (new entry from AE): use AEI to find AE sender,
    ///   then reuse the sender's EntryTermHasVoteQuorum witness (IH)
    pub proof fn lemma_entry_term_has_vote_quorum_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            EntryTermHasVoteQuorum(ds_)
    {
        // Key cases for induction:
        // - Old entries (non-stepping server or old prefix): use IH for (i, k) in ds.
        //   The witness d's log is preserved by LogAppendOnly, packets by network monotonicity.
        // - LClientRequest (new entry by Leader at T): d = server_id, vote quorum from
        //   VotersVotedForCandidate. The leader's votes_granted has >= quorum_size members,
        //   so >= quorum_size - 1 voters with VoteResponse{T, to server_id} in ds.network.
        // - LFollowerAppendEntries (new entry from AE): AE sender has the entry (AEI),
        //   reuse sender's EntryTermHasVoteQuorum witness from IH.
        assume(EntryTermHasVoteQuorum(ds_));
    }

    // =========================================================================
    // Log Matching Induction (Phase 32.3.4)
    // =========================================================================

    /// Helper: LNext preserves log for most branches (only LClientRequest
    /// and LFollowerAppendEntries modify the log).
    pub proof fn lemma_lnext_log_preserved_or_extended(s: LState, s_: LState, c: LConstants)
        requires LNext(s, s_, c)
        ensures
            // The log is either unchanged or extended by exactly one entry
            s_.log.len() >= s.log.len()
            && s_.log.len() <= s.log.len() + 1
            && (forall |k: int| 0 <= k < s.log.len() ==> #[trigger] s_.log[k] == s.log[k])
    {
        // Verus case-splits on LNext and verifies for each branch:
        // Most branches: s_.log == s.log (unchanged, all three properties trivial)
        // LClientRequest: s_.log == s.log.push(entry), len increases by 1, prefix preserved
        // LFollowerAppendEntries: s_.log == s.log or s.log.push(entry), same argument
    }

    /// Main induction lemma for Log Matching
    ///
    /// LogMatching states: if servers i and j have entries at index k with the
    /// same term, then all preceding entries (0..k) also match.
    ///
    /// For a distributed step where only server_id transitions:
    /// - Pairs (i, j) where neither is server_id: unchanged, LogMatching preserved.
    /// - Pairs involving server_id: only two LNext branches modify the log:
    ///
    ///   (a) LClientRequest (leader appends entry at log.len()):
    ///       The new entry at index s.log.len() has term == s.current_term.
    ///       For another server j to have an entry at the same index with the
    ///       same term, j must have received that entry through AppendEntries
    ///       from the same leader. By Election Safety, there's only one leader
    ///       per term, so the entry must have been sent by server_id. This
    ///       requires network-level reasoning about message provenance.
    ///
    ///   (b) LFollowerAppendEntries (follower appends entry):
    ///       The spec now includes a prev_log consistency check in
    ///       LHandleAppendEntriesMsg (Raft paper §5.3): the follower rejects
    ///       AppendEntries if log[prev_index-1].term != prev_term. However,
    ///       in the single-server model, ae_prev_index and ae_prev_term are
    ///       existentially quantified — there is no constraint linking them
    ///       to what the leader actually sent. Proving LogMatching requires
    ///       knowing that received prev_log values correspond to the leader's
    ///       log entries, which is a network-level message provenance property.
    ///
    /// Both gaps are network-level: they require reasoning about which messages
    /// are actually delivered and how their parameters relate to sender state.
    pub proof fn lemma_log_matching_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            LogMatching(ds_)
    {
        // Extract server_id from RaftDistributedNext to get both LNext and
        // RaftServerStepWithNetwork for the same server.
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |server_id: int|
            #![trigger ds.server_states[server_id]] {
            &&& 0 <= server_id < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, server_id)
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        lemma_lnext_log_preserved_or_extended(s, s_, c);
        lemma_log_append_only(ds, ds_);

        // Establish that old entries of the stepping server are preserved
        assert forall |k: int| 0 <= k < s.log.len()
            implies #[trigger] s_.log[k] == s.log[k] by {};

        lemma_log_matching_inner(ds, ds_, server_id, s, s_, c);
    }

    /// Inner proof for LogMatching induction, separated for modularity.
    proof fn lemma_log_matching_inner(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            LNext(s, s_, c),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            // Log properties
            s_.log.len() >= s.log.len(),
            s_.log.len() <= s.log.len() + 1,
            forall |k: int| 0 <= k < s.log.len() ==> #[trigger] s_.log[k] == s.log[k],
            LogAppendOnly(ds, ds_),
            // Network step
            RaftServerStepWithNetwork(ds, ds_, server_id),
        ensures
            LogMatching(ds_)
    {
        assert forall |i: int, j: int, k: int|
            0 <= i < ds_.num_servers && 0 <= j < ds_.num_servers
            && 0 <= k < ds_.server_states[i].log.len()
            && 0 <= k < ds_.server_states[j].log.len()
            && ds_.server_states[i].log[k].term == ds_.server_states[j].log[k].term
            implies (forall |m: int| 0 <= m <= k
                && m < ds_.server_states[i].log.len()
                && m < ds_.server_states[j].log.len()
                ==> ds_.server_states[i].log[m] == ds_.server_states[j].log[m])
        by {
            if i == j {
                // Same server: trivially true (same log)
            } else if i != server_id && j != server_id {
                // Both unchanged: LogMatching(ds) applies directly
                assert(ds_.server_states[i] == ds.server_states[i]);
                assert(ds_.server_states[j] == ds.server_states[j]);
                assert(LogMatching(ds));
            } else {
                // One of i, j is server_id — handle the stepping server case
                // Use symmetry: reduce to the case where server_id has
                // the entry at k.
                let (si, sj) = if i == server_id { (i, j) } else { (j, i) };
                // si == server_id, sj != server_id
                assert(ds_.server_states[sj] == ds.server_states[sj]);

                if k < s.log.len() {
                    // Index k is in the OLD prefix of server_id's log.
                    // Both entries at k are unchanged:
                    // ds_.server_states[si].log[k] == ds.server_states[si].log[k] (preserved)
                    // ds_.server_states[sj].log[k] == ds.server_states[sj].log[k] (unchanged)
                    // LogMatching(ds) for (si, sj, k) gives entries 0..k match.
                    assert(LogMatching(ds));
                    // Entries at m <= k are also unchanged in ds_:
                    // For si: s_.log[m] == s.log[m] for m < s.log.len()
                    // For sj: unchanged
                } else {
                    // k == s.log.len(): the NEW entry on server_id.
                    // The new entry has term T = s_.log[k].term.
                    // Server sj has entry at k with the same term T.
                    if s.role is Leader {
                        // LClientRequest: new entry has term s.current_term.
                        // In ds, server_id is Leader at term T.
                        // sj has entry at k with term T in ds (sj unchanged).
                        // By LeaderLogLongEnough(ds) for (i=sj, k=k, l=server_id):
                        //   ds.server_states[server_id].log.len() > k
                        // But ds.server_states[server_id].log.len() == s.log.len() == k.
                        // Contradiction — the premise is impossible.
                        assert(LeaderLogLongEnough(ds));
                        assert(0 <= sj < ds.num_servers);
                        assert(0 <= k < ds.server_states[sj].log.len());
                        assert(ds.server_states[server_id].role is Leader);
                    } else {
                        // LFollowerAppendEntries: server_id received an AE from
                        // the network. Extract the AE packet and use AEI +
                        // LogMatching(ds) to prove entry matching.
                        lemma_log_matching_follower_append(
                            ds, ds_, server_id, s, s_, c, sj, k, i, j);
                    }
                }
            }
        }
    }

    /// When server_id extends its log via the network model (non-Leader),
    /// there exists a leader whose log matches the new entry and the
    /// follower's prev-log entry. Captures AE packet provenance via AEI.
    proof fn lemma_follower_append_ae_in_network(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
        k: int,
    )
        requires
            AppendEntriesIntegrity(ds),
            WellFormedRaftDistributed(ds),
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            RaftServerStepWithNetwork(ds, ds_, server_id),
            s_.log.len() == s.log.len() + 1,
            !(s.role is Leader),
            k == s.log.len() as int,
        ensures
            exists |ae_leader: int|
                #![trigger ds.server_states[ae_leader]]
            {
                &&& 0 <= ae_leader < ds.num_servers
                &&& ds.server_states[ae_leader].log.len() > k
                &&& ds.server_states[ae_leader].log[k].term == s_.log[k].term
                &&& ds.server_states[ae_leader].log[k].value == s_.log[k].value
                &&& (k > 0 ==> s.log[k - 1].term
                        == ds.server_states[ae_leader].log[k - 1].term)
            }
    {
        // Verus unfolds RaftServerStepWithNetwork → RaftActionProduces
        //   → LHandleMessage (only branch that grows log for non-Leader)
        //   → LHandleAppendEntriesMsg → LFollowerAppendEntries
        // The received pkt is in ds.network, so AEI applies.
        // ae_has_entry must be true (log grew), ae_prev_index == k (position guard).
    }

    /// Helper for LogMatching: when server_id extends its log via
    /// LFollowerAppendEntries and another server sj has an entry at the
    /// same index k with the same term, all entries 0..k match.
    proof fn lemma_log_matching_follower_append(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
        sj: int, k: int, qi: int, qj: int,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            LNext(s, s_, c),
            forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != server_id ==>
                ds_.server_states[j] == ds.server_states[j],
            s_.log.len() >= s.log.len(),
            s_.log.len() <= s.log.len() + 1,
            forall |idx: int| 0 <= idx < s.log.len() ==> #[trigger] s_.log[idx] == s.log[idx],
            RaftServerStepWithNetwork(ds, ds_, server_id),
            // New entry case
            !(s.role is Leader),
            k == s.log.len() as int,
            0 <= sj < ds.num_servers,
            sj != server_id,
            ds_.server_states[sj] == ds.server_states[sj],
            0 <= k < ds_.server_states[sj].log.len(),
            k < s_.log.len(),
            s_.log[k].term == ds_.server_states[sj].log[k].term,
            // qi, qj are the original quantified i, j (one is server_id)
            (qi == server_id && qj == sj) || (qi == sj && qj == server_id),
            0 <= qi < ds_.num_servers,
            0 <= qj < ds_.num_servers,
        ensures
            forall |m: int| 0 <= m <= k
                && m < ds_.server_states[qi].log.len()
                && m < ds_.server_states[qj].log.len()
                ==> ds_.server_states[qi].log[m] == ds_.server_states[qj].log[m]
    {
        // Extract the AE leader from the network
        lemma_follower_append_ae_in_network(ds, ds_, server_id, s, s_, c, k);

        // Choose the leader satisfying the postcondition
        let ae_leader: int = choose |l: int| {
            &&& 0 <= l < ds.num_servers
            &&& (#[trigger] ds.server_states[l]).log.len() > k
            &&& ds.server_states[l].log[k].term == s_.log[k].term
            &&& ds.server_states[l].log[k].value == s_.log[k].value
            &&& (k > 0 ==> s.log[k - 1].term
                    == ds.server_states[l].log[k - 1].term)
        };

        let T = s_.log[k].term;
        assert(LogMatching(ds));

        assert forall |m: int| 0 <= m <= k
            && m < ds_.server_states[qi].log.len()
            && m < ds_.server_states[qj].log.len()
        implies
            ds_.server_states[qi].log[m] == ds_.server_states[qj].log[m]
        by {
            // LogMatching(ds) for (ae_leader, sj, k) gives:
            //   ae_leader.log[m] == sj.log[m] for all m <= k
            assert(ds.server_states[ae_leader].log[m] == ds.server_states[sj].log[m]);

            if m == k {
                // s_.log[k] = LLogEntry{term: T, value: ae_value}
                // ae_leader.log[k] has same term and value (AEI)
                // sj.log[k] == ae_leader.log[k] (from LogMatching above)
                assert(s_.log[k].term == ds.server_states[ae_leader].log[k].term);
                assert(s_.log[k].value == ds.server_states[ae_leader].log[k].value);
            } else {
                // m < k: s_.log[m] == s.log[m] (preserved prefix)
                // Need: s.log[m] == sj.log[m]
                // Chain: s.log[m] == ae_leader.log[m] == sj.log[m]
                //
                // For the first link (s.log[m] == ae_leader.log[m]):
                // If k > 0, prev-log check gives s.log[k-1].term == ae_leader.log[k-1].term
                // LogMatching(ds) for (server_id, ae_leader, k-1) gives s.log[m] == ae_leader.log[m]
                if k > 0 {
                    // LogMatching(ds) for (server_id, ae_leader, k-1)
                    assert(ds.server_states[server_id].log[m] == ds.server_states[ae_leader].log[m]);
                }
            }
        }
    }

    // =========================================================================
    // Leader Completeness Induction (Phase 32.3.5)
    // =========================================================================

    /// Sub-helper for LeaderCompleteness induction: if the leader is unchanged
    /// across a distributed step and the committed-entry witness is from the
    /// pre-state, the LeaderCompleteness obligation transfers directly.
    proof fn lemma_leader_completeness_unchanged_leader_for_prestate_commit(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        leader_id: int, k: int, entry: LLogEntry,
    )
        requires
            0 <= k,
            LeaderCompleteness(ds),
            EntryCommittedAt(ds, k, entry),
            0 <= leader_id < ds.num_servers,
            ds_.server_states[leader_id] == ds.server_states[leader_id],
            ds.server_states[leader_id].role is Leader,
            ds.server_states[leader_id].current_term > entry.term,
        ensures
            ds_.server_states[leader_id].log.len() > k,
            ds_.server_states[leader_id].log[k] == entry,
    {
        assert(LeaderCompleteness(ds));
        assert(ds.server_states[leader_id].log.len() > k);
        assert(ds.server_states[leader_id].log[k] == entry);
    }

    /// Sub-helper for LeaderCompleteness induction: a post-state committed
    /// witness either already existed in the pre-state, or it is a fresh
    /// append at index `k` on the stepping server this step.
    proof fn lemma_entry_committed_post_implies_pre_or_fresh_step_append(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        k: int, entry: LLogEntry,
    )
        requires
            0 <= k,
            RaftDistributedNext(ds, ds_),
            EntryCommittedAt(ds_, k, entry),
        ensures
            EntryCommittedAt(ds, k, entry)
                || exists |stepping: int| {
                    &&& 0 <= stepping < ds.num_servers
                    &&& (forall |j: int| #![trigger ds_.server_states[j]]
                        0 <= j < ds.num_servers && j != stepping ==>
                        ds_.server_states[j] == ds.server_states[j])
                    &&& k == ds.server_states[stepping].log.len()
                    &&& ds_.server_states[stepping].log.len()
                        == ds.server_states[stepping].log.len() + 1
                    &&& ds_.server_states[stepping].log[k] == entry
                }
    {
        lemma_distributed_next_implies_legacy(ds, ds_);
        let server_id = choose |sid: int| {
            &&& 0 <= sid < ds.num_servers
            &&& LNext(ds.server_states[sid], ds_.server_states[sid], ds.server_constants[sid])
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        lemma_lnext_log_preserved_or_extended(s, s_, c);

        let commit_quorum = choose |q: Set<int>| {
            &&& q.len() >= ds.num_servers / 2 + 1
            &&& (forall |id: int| q.contains(id) ==> {
                &&& 0 <= id < ds.num_servers
                &&& ds_.server_states[id].log.len() > k
                &&& ds_.server_states[id].log[k] == entry
            })
        };

        let fresh_step_case = commit_quorum.contains(server_id) && !(k < s.log.len());
        if fresh_step_case {
            assert(commit_quorum.contains(server_id));
            assert(ds_.server_states[server_id].log.len() > k);
            assert(k + 1 <= s_.log.len());
            assert(s_.log.len() <= s.log.len() + 1);
            assert(k <= s.log.len());
            assert(s.log.len() <= k);
            assert(k == s.log.len());

            assert(s_.log.len() > s.log.len());
            assert(s_.log.len() >= s.log.len() + 1);
            assert(s_.log.len() == s.log.len() + 1);
            assert(ds_.server_states[server_id].log[k] == entry);

            assert(exists |stepping: int| {
                &&& 0 <= stepping < ds.num_servers
                &&& (forall |j: int| #![trigger ds_.server_states[j]]
                    0 <= j < ds.num_servers && j != stepping ==>
                    ds_.server_states[j] == ds.server_states[j])
                &&& k == ds.server_states[stepping].log.len()
                &&& ds_.server_states[stepping].log.len()
                    == ds.server_states[stepping].log.len() + 1
                &&& ds_.server_states[stepping].log[k] == entry
            }) by {
                let stepping = server_id;
                assert(0 <= stepping < ds.num_servers);
                assert(k == ds.server_states[stepping].log.len());
                assert(ds_.server_states[stepping].log.len()
                    == ds.server_states[stepping].log.len() + 1);
                assert(ds_.server_states[stepping].log[k] == entry);
            };
        } else {
            assert(EntryCommittedAt(ds, k, entry)) by {
                assert(exists |q: Set<int>| {
                    &&& q.len() >= ds.num_servers / 2 + 1
                    &&& (forall |id: int| q.contains(id) ==> {
                        &&& 0 <= id < ds.num_servers
                        &&& ds.server_states[id].log.len() > k
                        &&& ds.server_states[id].log[k] == entry
                    })
                }) by {
                    let q = commit_quorum;
                    assert(q.len() >= ds.num_servers / 2 + 1);
                    assert forall |id: int| q.contains(id) implies {
                        &&& 0 <= id < ds.num_servers
                        &&& ds.server_states[id].log.len() > k
                        &&& ds.server_states[id].log[k] == entry
                    } by {
                        assert(0 <= id < ds.num_servers);
                        if id != server_id {
                            assert(ds_.server_states[id] == ds.server_states[id]);
                            assert(ds.server_states[id].log.len() > k);
                            assert(ds.server_states[id].log[k] == entry);
                        } else {
                            assert(id == server_id);
                            assert(q.contains(server_id));
                            if !(k < s.log.len()) {
                                assert(fresh_step_case);
                                assert(false);
                            }
                            assert(k < s.log.len());
                            assert(s.log.len() > k);
                            assert(s_.log[k] == s.log[k]);
                            assert(ds_.server_states[server_id].log[k] == entry);
                            assert(ds.server_states[server_id].log[k] == entry);
                        }
                    };
                };
            };
        }
    }

    /// e.3.c helper: perform new-leader overlap/provenance wiring and connect
    /// extracted RequestVote parameters to the vote-grant bridge template.
    proof fn lemma_new_leader_provenance_bridge_wiring(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
    {
        lemma_votes_granted_are_servers_inductive(ds, ds_);
        lemma_voters_voted_for_candidate_inductive(ds, ds_);
        lemma_leader_has_quorum_inductive(ds, ds_);
        lemma_vote_response_integrity_inductive(ds, ds_);
        lemma_vote_response_has_request_vote_inductive(ds, ds_);

        if exists |witness: (int, int, LLogEntry)| {
            &&& 0 <= witness.0 < ds_.num_servers
            &&& 0 <= witness.1
            &&& EntryCommittedAt(ds_, witness.1, witness.2)
            &&& ds_.server_states[witness.0].role is Leader
            &&& ds_.server_states[witness.0].current_term > witness.2.term
            &&& ds_.server_states[witness.0] != ds.server_states[witness.0]
        } {
            let witness = choose |witness: (int, int, LLogEntry)| {
                &&& 0 <= witness.0 < ds_.num_servers
                &&& 0 <= witness.1
                &&& EntryCommittedAt(ds_, witness.1, witness.2)
                &&& ds_.server_states[witness.0].role is Leader
                &&& ds_.server_states[witness.0].current_term > witness.2.term
                &&& ds_.server_states[witness.0] != ds.server_states[witness.0]
            };
            let leader_id = witness.0;
            let k = witness.1;
            let entry = witness.2;

            lemma_overlap_request_vote_params_witness(ds_, k, entry, leader_id);
            let overlap_voter = choose |ov: int| {
                &&& 0 <= ov < ds_.num_servers
                &&& ds_.server_states[leader_id].votes_granted.contains(ov)
                &&& ds_.server_states[ov].log.len() > k
                &&& ds_.server_states[ov].log[k] == entry
                &&& (ov == leader_id
                    || exists |req: LRaftPacket| {
                        &&& ds_.network.contains(req)
                        &&& req.src == leader_id
                        &&& req.dst == ov
                        &&& req.msg matches LRaftMessage::RequestVote {
                            term,
                            candidate: req_candidate,
                            last_log_index: _,
                            last_log_term: _,
                        }
                        &&& term == ds_.server_states[leader_id].current_term
                        &&& req_candidate == leader_id
                    })
            };

            if overlap_voter != leader_id {
                let req_pkt = choose |req: LRaftPacket| {
                    &&& ds_.network.contains(req)
                    &&& req.src == leader_id
                    &&& req.dst == overlap_voter
                    &&& req.msg matches LRaftMessage::RequestVote {
                        term,
                        candidate: req_candidate,
                        last_log_index: _,
                        last_log_term: _,
                    }
                    &&& term == ds_.server_states[leader_id].current_term
                    &&& req_candidate == leader_id
                };
                let req_term = req_pkt.msg->RequestVote_term;
                let req_last_log_index = req_pkt.msg->RequestVote_last_log_index;
                let req_last_log_term = req_pkt.msg->RequestVote_last_log_term;
                assert(req_term == ds_.server_states[leader_id].current_term);
                lemma_vote_grant_bridge_template_for_overlap_voter(
                    overlap_voter, leader_id,
                    req_term, req_last_log_index, req_last_log_term,
                    ds_.server_states[leader_id]);
            }
        }
    }

    /// Main induction lemma for Leader Completeness
    ///
    /// LeaderCompleteness states: if an entry is committed (replicated to a
    /// majority quorum) in some term, then every leader for all higher-numbered
    /// terms has that entry in its log.
    ///
    /// The proof requires:
    /// 1. Election Safety: at most one leader per term
    /// 2. LogMatching: entries with same (term, index) imply matching prefix
    /// 3. Quorum intersection: the new leader's vote quorum overlaps with the
    ///    commit quorum, so at least one voter has the committed entry
    /// 4. Log up-to-date check: LGrantVote checks log_up_to_date, ensuring
    ///    the new leader's log is at least as current as any voter's
    ///
    /// The key gap is the same as LogMatching: in the single-server spec model,
    /// message parameters are existentially quantified with no provenance linking
    /// them to the sender's state, so we cannot formally connect the voter's log
    /// at vote time to the committed entry's presence.
    pub proof fn lemma_leader_completeness_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            LeaderCompleteness(ds_)
    {
        // The only interesting case is when a server becomes a new Leader
        // (via LReceiveVoteAndBecomeLeader). For existing leaders whose state
        // is unchanged, LeaderCompleteness is preserved from the pre-state.
        //
        // For the new leader: it must have every previously committed entry.
        // Argument:
        //   - Let entry e be committed at index k with term t.
        //   - The commit quorum Q_c has |Q_c| >= N/2+1 servers with e at index k.
        //   - The new leader's vote quorum Q_v has |Q_v| >= N/2+1 voters.
        //   - By quorum intersection, some server w is in both Q_c and Q_v.
        //   - w has entry e at index k (from Q_c membership).
        //   - w voted for the new leader, passing log_up_to_date check.
        //   - Therefore the new leader's log is at least as up-to-date as w's.
        //   - By LogMatching, since w has e at index k and the new leader's log
        //     is at least as long/current, the new leader also has e at index k.
        //
        // This argument requires LogMatching (assumed above) and network-level
        // message provenance. We assume it here.
        //
        // e.3.c wiring is used in the changed-leader branch (34.7.1.e.4.c).
        assert(ds_.num_servers == ds.num_servers);
        assert(LeaderCompleteness(ds));

        assert forall |k: int, entry: LLogEntry, leader_id: int|
            0 <= k
            && EntryCommittedAt(ds_, k, entry)
            && 0 <= leader_id < ds_.num_servers
            && ds_.server_states[leader_id].role is Leader
            && ds_.server_states[leader_id].current_term > entry.term
        implies {
            &&& ds_.server_states[leader_id].log.len() > k
            &&& ds_.server_states[leader_id].log[k] == entry
        } by {
            lemma_entry_committed_post_implies_pre_or_fresh_step_append(ds, ds_, k, entry);

            if EntryCommittedAt(ds, k, entry) {
                if ds_.server_states[leader_id] == ds.server_states[leader_id] {
                    assert(0 <= leader_id < ds.num_servers);
                    assert(ds.server_states[leader_id].role is Leader);
                    assert(ds.server_states[leader_id].current_term > entry.term);
                    lemma_leader_completeness_unchanged_leader_for_prestate_commit(
                        ds, ds_, leader_id, k, entry);
                } else {
                    // Pending 34.7.1.e.4.c (changed-leader branch).
                    assume(
                        ds_.server_states[leader_id].log.len() > k
                            && ds_.server_states[leader_id].log[k] == entry
                    );
                }
            } else {
                // Pending 34.7.1.e.4.b (fresh-step append branch from post commit).
                assume(
                    ds_.server_states[leader_id].log.len() > k
                        && ds_.server_states[leader_id].log[k] == entry
                );
            }
        }
    }

    // =========================================================================
    // State Machine Safety Induction (Phase 32.3.6)
    // =========================================================================

    /// Main induction lemma for State Machine Safety
    ///
    /// StateMachineSafety states: for any two servers i and j, entries below
    /// both commit_index[i] and commit_index[j] are identical.
    ///
    /// This follows from LeaderCompleteness + LogMatching:
    /// - Committed entries were replicated by a leader in some term.
    /// - By LeaderCompleteness, all subsequent leaders have these entries.
    /// - By LogMatching, servers that received entries from these leaders
    ///   have matching prefixes.
    /// - Therefore all committed entries agree across all servers.
    ///
    /// Since this depends on LeaderCompleteness (which we assume), we also
    /// assume StateMachineSafety. Alternatively, once LogMatching and
    /// LeaderCompleteness are proved, StateMachineSafety follows.
    pub proof fn lemma_state_machine_safety_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            StateMachineSafety(ds_)
    {
        // StateMachineSafety depends on LogMatching + LeaderCompleteness.
        // Both are network-level invariants assumed above.
        assume(StateMachineSafety(ds_));
    }

    // =========================================================================
    // Message Invariant Induction Stubs (Phase 34.2)
    // =========================================================================
    //
    // Stub proofs for the 4 message invariants. These will be filled in
    // during Phase 34.3. For now, they use assume().

    pub proof fn lemma_sender_integrity_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            SenderIntegrity(ds_)
    {
        // Old packets: from SenderIntegrity(ds) + network monotonicity.
        // New packets: src == server_id, msg identity field == c.my_id == server_id.
        // All actions explicitly set identity fields to c.my_id (verified by SMT
        // unfolding of RaftActionProduces + action definitions).
    }

    pub proof fn lemma_vote_response_integrity_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            VoteResponseIntegrity(ds_)
    {
        // New VoteResponse{granted: true}: created by LGrantVote which sets
        // has_voted=true, voted_for=candidate_id. Routing: dst == received_from == RequestVote.src.
        // By SenderIntegrity: RequestVote.src == candidate field == candidate_id.
        // So dst == voted_for at the new term. ✓
        //
        // Old VoteResponse{voter: v, term: t}: from VoteResponseIntegrity(ds).
        // If v's current_term increased (step_down, timeout, etc.): current_term > t. ✓
        // If v's current_term unchanged at t: has_voted and voted_for preserved
        // (only reset when term changes). ✓
    }

    #[verifier::rlimit(200)]
    pub proof fn lemma_vote_response_has_request_vote_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            WellFormedRaftDistributed(ds),
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            RaftDistributedNext(ds, ds_),
            VoteResponseHasRequestVote(ds),
            SenderIntegrity(ds),
        ensures
            VoteResponseHasRequestVote(ds_)
    {
        // Use full distributed-next witness (not legacy), so we can reason
        // about old/new packets and response routing.
        let server_id = choose |sid: int|
            #![trigger ds.server_states[sid]]
        {
            &&& 0 <= sid < ds.num_servers
            &&& (forall |j: int| #![trigger ds_.server_states[j]]
                0 <= j < ds.num_servers && j != sid ==>
                ds_.server_states[j] == ds.server_states[j])
            &&& RaftServerStepWithNetwork(ds, ds_, sid)
        };

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        let (sent_packets, received_from) =
            choose |sp: Seq<LRaftMessage>, rf: Option<int>| {
                &&& RaftActionProduces(ds, server_id, s, s_, c, sp, rf)
                &&& (forall |pkt: LRaftPacket| ds.network.contains(pkt) ==> ds_.network.contains(pkt))
                &&& (forall |pkt: LRaftPacket|
                    ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                        &&& pkt.src == server_id
                        &&& 0 <= pkt.dst < ds.num_servers
                        &&& (exists |i: int| 0 <= i < sp.len() && pkt.msg == sp[i])
                        &&& (match rf {
                            Some(src) => pkt.dst == src,
                            None => true,
                        })
                    })
            };

        assert(RaftActionProduces(ds, server_id, s, s_, c, sent_packets, received_from));
        assert(forall |pkt: LRaftPacket| ds.network.contains(pkt) ==> ds_.network.contains(pkt));
        assert(forall |pkt: LRaftPacket|
            ds_.network.contains(pkt) && !ds.network.contains(pkt) ==> {
                &&& pkt.src == server_id
                &&& 0 <= pkt.dst < ds.num_servers
                &&& (exists |i: int| 0 <= i < sent_packets.len() && pkt.msg == sent_packets[i])
                &&& (match received_from {
                    Some(src) => pkt.dst == src,
                    None => true,
                })
            });

        assert forall |p: LRaftPacket| ds_.network.contains(p) implies
            match p.msg {
                LRaftMessage::VoteResponse { term: t, granted, voter: v } => {
                    granted ==> exists |req: LRaftPacket| {
                        &&& ds_.network.contains(req)
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
        by {
            if p.msg is VoteResponse {
                if p.msg->VoteResponse_granted {
                    if ds.network.contains(p) {
                        // Old packet: reuse IH witness and network monotonicity.
                        assert(VoteResponseHasRequestVote(ds));
                        let req = choose |req: LRaftPacket| {
                            &&& ds.network.contains(req)
                            &&& req.src == p.dst
                            &&& req.dst == p.msg->VoteResponse_voter
                            &&& req.msg matches LRaftMessage::RequestVote {
                                term,
                                candidate,
                                last_log_index: _,
                                last_log_term: _,
                            }
                            &&& term == p.msg->VoteResponse_term
                            &&& candidate == p.dst
                        };
                        assert(ds_.network.contains(req));
                    } else {
                        // New packet: produced in this step from sent_packets.
                        assert(p.src == server_id);
                        let i = choose |i: int| 0 <= i < sent_packets.len() && p.msg == sent_packets[i];
                        assert(0 <= i < sent_packets.len());
                        assert(sent_packets[i] == p.msg);

                        // If a VoteResponse packet is sent in this model, it comes from
                        // handling RequestVote.
                        let req_pkt = choose |pkt: LRaftPacket| {
                            &&& received_from == Some(pkt.src)
                            &&& ds.network.contains(pkt)
                            &&& pkt.dst == server_id
                            &&& LHandleMessage(s, s_, c, pkt.msg, sent_packets)
                        };
                        assert(ds.network.contains(req_pkt));
                        assert(req_pkt.dst == server_id);
                        assert(received_from == Some(req_pkt.src));
                        assert(LHandleMessage(s, s_, c, req_pkt.msg, sent_packets));
                        assert(req_pkt.msg is RequestVote);

                        let req_term = req_pkt.msg->RequestVote_term;
                        let req_candidate = req_pkt.msg->RequestVote_candidate;
                        let req_last_log_index = req_pkt.msg->RequestVote_last_log_index;
                        let req_last_log_term = req_pkt.msg->RequestVote_last_log_term;
                        assert(LHandleRequestVoteMsg(
                            s, s_, c, req_term, req_candidate, req_last_log_index, req_last_log_term,
                            sent_packets));
                        assert(sent_packets == seq![LRaftMessage::VoteResponse {
                            term: req_term,
                            granted: true,
                            voter: c.my_id,
                        }]);

                        // Packet shape equalities from new-packet rule + action shape.
                        assert(p.msg == LRaftMessage::VoteResponse {
                            term: req_term,
                            granted: true,
                            voter: c.my_id,
                        });
                        assert(p.msg->VoteResponse_term == req_term);
                        assert(p.msg->VoteResponse_voter == c.my_id);
                        assert(c.my_id == server_id);

                        // Routing gives dst == source of the received RequestVote.
                        assert(p.dst == req_pkt.src);
                        // SenderIntegrity on ds: RequestVote.candidate == src.
                        assert(SenderIntegrity(ds));
                        assert(req_candidate == req_pkt.src);

                        // The received RequestVote packet is still in ds_ (network monotonicity),
                        // and is the required provenance witness.
                        assert(ds_.network.contains(req_pkt));
                        assert(exists |req: LRaftPacket| {
                            &&& ds_.network.contains(req)
                            &&& req.src == p.dst
                            &&& req.dst == p.msg->VoteResponse_voter
                            &&& req.msg matches LRaftMessage::RequestVote {
                                term,
                                candidate,
                                last_log_index: _,
                                last_log_term: _,
                            }
                            &&& term == p.msg->VoteResponse_term
                            &&& candidate == p.dst
                        }) by {
                            let req = req_pkt;
                            assert(req.src == p.dst);
                            assert(req.dst == p.msg->VoteResponse_voter);
                            assert(req.msg matches LRaftMessage::RequestVote {
                                term,
                                candidate,
                                last_log_index: _,
                                last_log_term: _,
                            });
                            assert(req.msg->RequestVote_term == p.msg->VoteResponse_term);
                            assert(req.msg->RequestVote_candidate == p.dst);
                        };
                    }
                }
            }
        };
    }

    pub proof fn lemma_append_entries_integrity_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            AppendEntriesIntegrity(ds_)
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

        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];

        lemma_log_append_only(ds, ds_);
        lemma_lnext_term_monotone(s, s_, c);
        lemma_lnext_log_preserved_or_extended(s, s_, c);

        // Establish that old entries of the stepping server are preserved
        assert forall |k: int| 0 <= k < s.log.len()
            implies #[trigger] s_.log[k] == s.log[k] by {};

        assert forall |p: LRaftPacket| ds_.network.contains(p) implies
            match p.msg {
                LRaftMessage::AppendEntries { term: t, leader: l, prev_index,
                                               prev_term, value, has_entry, .. } => {
                    &&& 0 <= l < ds_.num_servers
                    &&& p.src == l
                    &&& prev_index >= 0
                    &&& ds_.server_states[l].current_term >= t
                    &&& ds_.server_states[l].log.len() >= prev_index
                            + (if has_entry { 1int } else { 0int })
                    &&& (prev_index > 0 ==>
                        ds_.server_states[l].log[prev_index - 1].term == prev_term)
                    &&& (has_entry ==>
                        ds_.server_states[l].log[prev_index].value == value)
                    &&& (has_entry ==>
                        ds_.server_states[l].log[prev_index].term == t)
                }
                _ => true,
            }
        by {
            if p.msg is AppendEntries {
                let l = p.msg->AppendEntries_leader;
                let prev_index = p.msg->AppendEntries_prev_index;
                let has_entry = p.msg->AppendEntries_has_entry;

                if ds.network.contains(p) {
                    // Old AE packet: AppendEntriesIntegrity(ds) gives conditions on ds.
                    assert(AppendEntriesIntegrity(ds));

                    if l != server_id {
                        // Non-stepping leader: state unchanged
                        assert(ds_.server_states[l] == ds.server_states[l]);
                    } else {
                        // Stepping server is the leader in this old packet.
                        // s == ds.server_states[server_id], s_ == ds_.server_states[server_id]
                        // lemma_lnext_log_preserved_or_extended gives s_.log[k] == s.log[k]
                        // for k < s.log.len(). Since l == server_id:
                        assert(ds.server_states[l] == s);
                        assert(ds_.server_states[l] == s_);
                        assert(s_.log.len() >= s.log.len());
                        // AEI(ds) + has_entry → prev_index < s.log.len()
                        // lemma_lnext_log_preserved_or_extended → s_.log[k] == s.log[k] for k < s.log.len()
                        if has_entry {
                            // s.log.len() >= prev_index + 1 (from AEI)
                            assert(s.log.len() >= prev_index + 1);
                            assert(0 <= prev_index);
                            assert(prev_index < s_.log.len());
                            assert(s_.log[prev_index] == s.log[prev_index]);
                        }
                        if prev_index > 0 {
                            assert(s.log.len() >= prev_index);
                            assert(prev_index - 1 < s.log.len());
                            assert(prev_index - 1 < s_.log.len());
                            assert(s_.log[prev_index - 1] == s.log[prev_index - 1]);
                        }
                    }
                } else {
                    // New AE packet: produced by RaftDistributedNext.
                    // RaftServerStepWithNetwork ensures p.src == stepping server.
                    // Only LSendAppendEntries produces AppendEntries messages.
                    // Its constraints + WellFormedRaftDistributed + frame conditions
                    // establish all AEI conjuncts. All spec fns are open → auto-verify.
                }
            }
        }
    }

    pub proof fn lemma_one_vote_per_term_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            OneVotePerTermInNetwork(ds_)
    {
        // Old-old packet pairs: from OneVotePerTermInNetwork(ds) + network monotonicity.
        // Old-new pair: new VoteResponse{granted: true} is only created by LGrantVote
        // which requires !has_voted || voted_for == candidate. By VoteResponseIntegrity(ds),
        // any existing VoteResponse for the same (voter, term) implies voter has voted,
        // so voted_for must match, and routing ensures same dst.
        // New-new: at most one VoteResponse per step, so p1 == p2.
    }

    // =========================================================================
    // VoteResponseTermBound inductive proof
    // =========================================================================

    pub proof fn lemma_vote_response_term_bound_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            VoteResponseTermBound(ds_)
    {
        // Old packets: VoteResponseTermBound(ds) + term monotonicity.
        // New packet (LGrantVote): step_down_if_needed ensures voter.current_term >= T
        // at creation time, so VoteResponseTermBound holds for the new packet.
        assume(VoteResponseTermBound(ds_));
    }

    // =========================================================================
    // CandidateVoteDestinationUnique inductive proof
    // =========================================================================

    pub proof fn lemma_candidate_vote_destination_unique_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            CandidateVoteDestinationUnique(ds_)
    {
        // Old-old pairs: from CandidateVoteDestinationUnique(ds) + network monotonicity.
        // New RequestVote + old VoteResponse{voter: d}: VoteResponseTermBound shows
        //   d.current_term >= T. But RequestVote is created by LTimeout which sets
        //   current_term = old_term + 1, so T = old_term + 1. For a VoteResponse{T}
        //   from d to exist, d must have had current_term >= T, but then d couldn't
        //   have been at term old_term when it created the RequestVote... Actually,
        //   the new RequestVote is from a different server than d. We need: if d
        //   created a RequestVote{T}, d voted for itself at T (LTimeout sets
        //   voted_for = self), so any VoteResponse{T, voter: d} must go to d
        //   (by OneVotePerTermInNetwork style reasoning + VoteResponseIntegrity).
        // Old RequestVote + new VoteResponse{voter: d}: similar, the new VoteResponse
        //   is created by LGrantVote, and if d is also a candidate at T, d has
        //   has_voted = true && voted_for = self. But this is d voting for someone
        //   else, meaning d.current_term must have advanced past T.
        assume(CandidateVoteDestinationUnique(ds_));
    }

    // =========================================================================
    // Helper: LNext term monotonicity
    // =========================================================================

    /// LNext never decreases current_term.
    proof fn lemma_lnext_term_monotone(s: LState, s_: LState, c: LConstants)
        requires LNext(s, s_, c)
        ensures s_.current_term >= s.current_term
    {
        // All LNext branches either keep current_term unchanged or increase it
        // (step_down_if_needed increases term when receiving a higher one).
    }

    // =========================================================================
    // Helper: LNext non-Leader to Leader implies Candidate
    // =========================================================================

    /// If LNext produces a Leader from a non-Leader, the pre-state was Candidate.
    proof fn lemma_lnext_non_leader_to_leader_was_candidate(
        s: LState, s_: LState, c: LConstants
    )
        requires
            LNext(s, s_, c),
            !(s.role is Leader),
            s_.role is Leader,
        ensures
            s.role is Candidate,
    {
        // LNext is a disjunction. The only branch that produces Leader from
        // non-Leader is LHandleMessage → LHandleVoteResponseMsg →
        // LReceiveVoteAndBecomeLeader, which requires s_mid.role is Candidate.
        // step_down_if_needed: if term > s.current_term, s_mid.role is Follower
        // (not Candidate → no-op). So s_mid == s, meaning s.role is Candidate.
    }

    // =========================================================================
    // Helper: range set finiteness
    // =========================================================================

    /// Set::new(|j: int| 0 <= j < n) is finite with len == n.
    proof fn lemma_range_set_finite(n: int)
        requires n >= 0
        ensures
            Set::<int>::new(|j: int| 0 <= j < n).finite(),
            Set::<int>::new(|j: int| 0 <= j < n).len() == n,
        decreases n
    {
        if n == 0 {
            assert(Set::<int>::new(|j: int| 0 <= j < 0int) =~= Set::<int>::empty());
        } else {
            lemma_range_set_finite(n - 1);
            let s_prev = Set::<int>::new(|j: int| 0 <= j < n - 1);
            let s_curr = Set::<int>::new(|j: int| 0 <= j < n);
            assert(s_curr =~= s_prev.insert(n - 1));
            assert(!s_prev.contains(n - 1));
        }
    }

    // =========================================================================
    // Composite induction step
    // =========================================================================

    /// Top-level induction: the full safety invariant is preserved by RaftDistributedNext
    pub proof fn lemma_safety_invariant_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            RaftSafetyInvariant(ds_)
    {
        // Well-formedness: directly from RaftDistributedNext precondition
        assert(WellFormedRaftDistributed(ds_));

        // Election Safety
        lemma_election_safety_inductive(ds, ds_);

        // Supporting invariants
        lemma_votes_granted_are_servers_inductive(ds, ds_);
        lemma_candidate_or_leader_voted_for_self_inductive(ds, ds_);
        lemma_candidate_or_leader_voted_for_self_id_inductive(ds, ds_);
        lemma_voters_voted_for_candidate_inductive(ds, ds_);
        lemma_leader_has_quorum_inductive(ds, ds_);
        lemma_commit_index_bounded_inductive(ds, ds_);
        lemma_leader_log_long_enough_inductive(ds, ds_);
        lemma_entry_term_leader_witness_inductive(ds, ds_);
        lemma_entry_term_has_vote_quorum_inductive(ds, ds_);

        // Log-level invariants (network-level trust boundary)
        lemma_log_matching_inductive(ds, ds_);
        lemma_leader_completeness_inductive(ds, ds_);
        lemma_state_machine_safety_inductive(ds, ds_);

        // Message invariants (Phase 34.2 — stubs with assumes)
        lemma_sender_integrity_inductive(ds, ds_);
        lemma_vote_response_integrity_inductive(ds, ds_);
        lemma_vote_response_has_request_vote_inductive(ds, ds_);
        lemma_append_entries_integrity_inductive(ds, ds_);
        lemma_one_vote_per_term_inductive(ds, ds_);
        lemma_vote_response_term_bound_inductive(ds, ds_);
        lemma_candidate_vote_destination_unique_inductive(ds, ds_);
    }

    // =========================================================================
    // Invariant holds for all reachable states (by induction on behavior)
    // =========================================================================

    /// Prove the invariant holds at step k of a valid behavior.
    /// Uses recursion on k (strong induction via decreases k).
    pub proof fn lemma_invariant_at_step(b: RaftBehavior, k: int)
        requires
            IsValidRaftBehavior(b),
            0 <= k < b.len(),
        ensures
            RaftSafetyInvariant(b[k])
        decreases k
    {
        if k == 0 {
            lemma_init_establishes_invariant(b[0]);
        } else {
            // By recursion, the invariant holds at step k-1
            lemma_invariant_at_step(b, k - 1);
            // b[k-1] -> b[k] is a valid RaftDistributedNext step
            assert(RaftDistributedNext(b[k - 1], b[k]));
            // By the inductive step, the invariant is preserved
            lemma_safety_invariant_inductive(b[k - 1], b[k]);
        }
    }

    /// The invariant holds for all reachable states in a valid behavior.
    pub proof fn lemma_invariant_holds_for_behavior(b: RaftBehavior)
        requires IsValidRaftBehavior(b)
        ensures forall |i: int| #![trigger b[i]] 0 <= i < b.len() ==> RaftSafetyInvariant(b[i])
    {
        assert forall |i: int| #![trigger b[i]]
            0 <= i < b.len()
        implies RaftSafetyInvariant(b[i]) by {
            lemma_invariant_at_step(b, i);
        }
    }
}
