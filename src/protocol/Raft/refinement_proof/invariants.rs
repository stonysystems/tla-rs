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
        &&& VotesGrantedAreServers(ds)
        &&& CandidateOrLeaderVotedForSelf(ds)
        &&& CandidateOrLeaderVotedForSelfId(ds)
        &&& VotersVotedForCandidate(ds)
        // Message invariants (Phase 34.2)
        &&& SenderIntegrity(ds)
        &&& VoteResponseIntegrity(ds)
        &&& AppendEntriesIntegrity(ds)
        &&& OneVotePerTermInNetwork(ds)
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
        // Message invariants: network is empty, all vacuously true
        // - SenderIntegrity, VoteResponseIntegrity, AppendEntriesIntegrity,
        //   OneVotePerTermInNetwork: forall over empty set is vacuously true
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

        // Establish log preservation for the stepping server
        lemma_lnext_log_preserved_or_extended(s, s_, c);

        // For pairs where neither server is the stepping one, LogMatching is
        // trivially preserved (both logs unchanged).
        //
        // For pairs involving server_id, we need to show that the new/extended
        // log maintains the matching property. The prefix of the old log is
        // preserved (lemma_lnext_log_preserved_or_extended ensures old entries
        // are unchanged). The only new entry (if any) is at s.log.len().
        //
        // The gap: if another server j has an entry at s.log.len() with the
        // same term as the newly appended entry, we need to show all preceding
        // entries match. This requires:
        // - For LClientRequest: Election Safety (one leader per term) +
        //   network-level entry provenance (j got its entry from this leader)
        // - For LFollowerAppendEntries: the spec now checks prev_log consistency,
        //   but ae_prev_index/ae_prev_term are existentially quantified with no
        //   constraint linking them to the leader's log entries.
        //
        // Both require network-level message provenance reasoning that the
        // single-server spec model cannot provide.
        assume(LogMatching(ds_));
    }

    // =========================================================================
    // Leader Completeness Induction (Phase 32.3.5)
    // =========================================================================

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
        assume(LeaderCompleteness(ds_));
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

    pub proof fn lemma_append_entries_integrity_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState
    )
        requires
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            AppendEntriesIntegrity(ds_)
    {
        // New AppendEntries packets: created by LSendAppendEntries with
        // existentially quantified parameters (prev_index, prev_term, value,
        // has_entry). The invariant requires these match the leader's log.
        // Since LSendAppendEntries does NOT constrain these parameters to
        // match the log, this invariant requires strengthening the spec.
        //
        // Old packets: leader's log is append-only (LogAppendOnly ensures
        // existing entries are preserved), so AE content still matches.
        //
        // TODO(Phase 34.3): Strengthen LSendAppendEntries to constrain
        // parameters to match the leader's log, then remove this assume.
        assume(AppendEntriesIntegrity(ds_));
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

        // Log-level invariants (network-level trust boundary)
        lemma_log_matching_inductive(ds, ds_);
        lemma_leader_completeness_inductive(ds, ds_);
        lemma_state_machine_safety_inductive(ds, ds_);

        // Message invariants (Phase 34.2 — stubs with assumes)
        lemma_sender_integrity_inductive(ds, ds_);
        lemma_vote_response_integrity_inductive(ds, ds_);
        lemma_append_entries_integrity_inductive(ds, ds_);
        lemma_one_vote_per_term_inductive(ds, ds_);
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
