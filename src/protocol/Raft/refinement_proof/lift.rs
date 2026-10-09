//! The raw Raft protocol, without any proof-only state, and the theorem that
//! every one of its executions is an execution of the proof model.
//!
//! The safety proof (induction.rs, refinement.rs, dynamic_*.rs) is about
//! `RaftDistributedState`, which carries ghost history next to the protocol
//! state. If a ghost rule ever blocked a step the protocol can take, that
//! proof would silently cover fewer executions than the protocol has. This
//! file closes that gap: `lemma_lift_behavior` builds, for each raw behavior,
//! a proof-model behavior with the same protocol state at every step, and the
//! final theorems state safety directly over raw behaviors.

use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::membership::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::invariants::*;
use crate::protocol::Raft::refinement_proof::message_invariants::*;
use crate::protocol::Raft::refinement_proof::induction::*;
use crate::protocol::Raft::refinement_proof::refinement::*;
use crate::protocol::Raft::refinement_proof::dynamic_invariant::*;
use vstd::prelude::*;

verus! {

    // =========================================================================
    // The raw protocol (trusted specification)
    // =========================================================================

    /// A cluster: per-server protocol state, constants, and the network.
    pub struct RaftRawState {
        pub server_states: Seq<LState>,
        pub server_constants: Seq<LConstants>,
        pub network: Set<LRaftPacket>,
        pub num_servers: int,
    }

    pub open spec fn WellFormedRaw(rs: RaftRawState) -> bool {
        &&& rs.num_servers > 0
        &&& rs.num_servers <= u64::MAX as int
        &&& rs.server_states.len() == rs.num_servers
        &&& rs.server_constants.len() == rs.num_servers
        &&& (forall |i: int| #![trigger rs.server_constants[i]] 0 <= i < rs.num_servers ==> {
            &&& rs.server_constants[i].my_id == i
            &&& rs.server_constants[i].quorum_size == rs.num_servers / 2 + 1
            &&& rs.server_constants[i].servers =~= Set::<int>::range(0, rs.num_servers)
        })
    }

    pub open spec fn RawInit(rs: RaftRawState) -> bool {
        &&& WellFormedRaw(rs)
        &&& (forall |i: int| #![trigger rs.server_states[i]] #![trigger rs.server_constants[i]]
            0 <= i < rs.num_servers ==> LInit(rs.server_states[i], rs.server_constants[i]))
        &&& rs.network == Set::<LRaftPacket>::empty()
    }

    /// One protocol action of `server_id`: a local action, or handling a
    /// packet addressed to it that is in the network.
    pub open spec fn RawActionProduces(
        rs: RaftRawState, server_id: int,
        s: LState, s_: LState, c: LConstants,
        sent_packets: Seq<LRaftMessage>,
        received_from: Option<int>,
    ) -> bool {
        ||| (received_from is None && LTimeout(s, s_, c, sent_packets))
        ||| (received_from is None && (exists |value: int| LClientRequest(s, s_, c, value, sent_packets)))
        ||| (received_from is None && (exists |phase: LMembershipPhase|
                LAppendConfigurationEntry(s, s_, c, phase, sent_packets)))
        ||| (received_from is None && (exists |follower: int, ev: int,
                ep: LLogValue, pli: int, plt: int, he: bool|
                LSendAppendEntries(s, s_, c, follower, ev, ep, pli, plt, he, sent_packets)))
        ||| (received_from is None && (exists |nci: int| LTryAdvanceCommitIndex(s, s_, c, nci, sent_packets)))
        ||| (exists |pkt: LRaftPacket| #![trigger rs.network.contains(pkt)] {
                &&& received_from == Some(pkt.src)
                &&& rs.network.contains(pkt)
                &&& pkt.dst == server_id
                &&& LHandleMessage(s, s_, c, pkt.msg, sent_packets)
            })
    }

    /// The network keeps every packet (so delivery may repeat and reorder)
    /// and gains any subset of the step's messages (so packets may be lost).
    /// Responses go back to the sender of the handled packet.
    pub open spec fn RawStepWitness(
        rs: RaftRawState, rs_: RaftRawState, server_id: int,
        sent_packets: Seq<LRaftMessage>, received_from: Option<int>,
    ) -> bool {
        &&& RawActionProduces(rs, server_id, rs.server_states[server_id],
            rs_.server_states[server_id], rs.server_constants[server_id], sent_packets, received_from)
        &&& (forall |pkt: LRaftPacket| rs.network.contains(pkt) ==> rs_.network.contains(pkt))
        &&& (forall |pkt: LRaftPacket| #![trigger rs_.network.contains(pkt)] #![trigger rs.network.contains(pkt)]
            rs_.network.contains(pkt) && !rs.network.contains(pkt) ==> {
                &&& pkt.src == server_id
                &&& 0 <= pkt.dst < rs.num_servers
                &&& (exists |i: int| 0 <= i < sent_packets.len() && pkt.msg == sent_packets[i])
                &&& (match received_from {
                    Some(src) => pkt.dst == src,
                    None => true,
                })
            })
    }

    pub open spec fn RawNormalNext(rs: RaftRawState, rs_: RaftRawState) -> bool {
        &&& WellFormedRaw(rs)
        &&& WellFormedRaw(rs_)
        &&& rs_.num_servers == rs.num_servers
        &&& rs_.server_constants == rs.server_constants
        &&& exists |server_id: int| #![trigger rs.server_states[server_id]] {
            &&& 0 <= server_id < rs.num_servers
            &&& (forall |j: int| #![trigger rs_.server_states[j]]
                0 <= j < rs.num_servers && j != server_id ==>
                rs_.server_states[j] == rs.server_states[j])
            &&& exists |sent_packets: Seq<LRaftMessage>, received_from: Option<int>|
                #![trigger RawStepWitness(rs, rs_, server_id, sent_packets, received_from)]
                RawStepWitness(rs, rs_, server_id, sent_packets, received_from)
        }
    }

    /// A crash-reboot: durable term, vote and log survive.
    pub open spec fn RawReboot(rs: RaftRawState, rs_: RaftRawState, server_id: int) -> bool {
        &&& WellFormedRaw(rs)
        &&& 0 <= server_id < rs.num_servers
        &&& LReboot(rs.server_states[server_id], rs_.server_states[server_id])
        &&& rs_ == (RaftRawState {
            server_states: rs.server_states.update(server_id, rs_.server_states[server_id]),
            ..rs
        })
    }

    pub open spec fn RawNext(rs: RaftRawState, rs_: RaftRawState) -> bool {
        ||| RawNormalNext(rs, rs_)
        ||| exists |server_id: int| RawReboot(rs, rs_, server_id)
    }

    pub type RaftRawBehavior = Seq<RaftRawState>;

    pub open spec fn IsValidRawBehavior(rb: RaftRawBehavior) -> bool {
        &&& rb.len() > 0
        &&& RawInit(rb[0])
        &&& (forall |i: int| #![trigger rb[i]] 0 <= i < rb.len() - 1 ==> RawNext(rb[i], rb[i + 1]))
    }

    /// The protocol state inside a proof-model state.
    pub open spec fn project(ds: RaftDistributedState) -> RaftRawState {
        RaftRawState {
            server_states: ds.server_states,
            server_constants: ds.server_constants,
            network: ds.network,
            num_servers: ds.num_servers,
        }
    }

    // =========================================================================
    // A server never runs again as a candidate in a term it has won
    // =========================================================================

    pub open spec fn ElectionRecordsNotCandidate(ds: RaftDistributedState) -> bool {
        forall |v: int, t: int| #![trigger ds.election_log_len.dom().contains((v, t))]
            ds.election_log_len.dom().contains((v, t)) && 0 <= v < ds.num_servers
            ==> !(ds.server_states[v].role is Candidate && ds.server_states[v].current_term == t)
    }

    /// Only a timeout makes a server a candidate, and it raises the term.
    proof fn lemma_lnext_candidate_same_term(s: LState, s_: LState, c: LConstants)
        requires
            LNext(s, s_, c),
            s_.role is Candidate,
            s_.current_term == s.current_term,
        ensures
            s.role is Candidate,
    {
    }

    pub proof fn lemma_election_records_not_candidate_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            ElectionRecordsNotCandidate(ds),
            RaftSafetyInvariant(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            ElectionRecordsNotCandidate(ds_),
    {
        if !RaftDistributedNormalNext(ds, ds_) {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            return;
        }
        let (server_id, sp, rf) = lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        assert(RaftServerStepWitness(ds, ds_, server_id, sp, rf));
        lemma_lnext_term_monotone(s, s_, c);
        assert forall |v: int, t: int| #![trigger ds_.election_log_len.dom().contains((v, t))]
            ds_.election_log_len.dom().contains((v, t)) && 0 <= v < ds_.num_servers
            implies !(ds_.server_states[v].role is Candidate && ds_.server_states[v].current_term == t) by {
            if ds.election_log_len.dom().contains((v, t)) {
                if v == server_id && s_.role is Candidate && s_.current_term == t {
                    assert(ElectionLogLenBounded(ds));
                    assert(s.current_term >= t);
                    lemma_lnext_candidate_same_term(s, s_, c);
                }
            }
        }
    }

    // =========================================================================
    // Ghost records never conflict with a protocol step
    // =========================================================================

    /// A step that grants a vote sends exactly one VoteResponse, from the
    /// stepping server, for the term of the RequestVote it handles. If the
    /// server already voted in that term, its log has not grown since: any
    /// entry gained in the term has the term itself, while the candidate's
    /// log summary is from an earlier term, so the vote would be refused.
    pub proof fn lemma_granted_vote_record_consistent(
        ds: RaftDistributedState, server_id: int,
        s_: LState, sp: Seq<LRaftMessage>, rf: Option<int>, i: int,
    )
        requires
            RaftSafetyInvariant(ds),
            0 <= server_id < ds.num_servers,
            RaftActionProduces(ds, server_id, ds.server_states[server_id], s_,
                ds.server_constants[server_id], sp, rf),
            0 <= i < sp.len(),
            sp[i] is VoteResponse,
            sp[i]->VoteResponse_granted,
        ensures ({
            let s = ds.server_states[server_id];
            let vt = sp[i]->VoteResponse_term;
            &&& sp[i]->VoteResponse_voter == server_id
            &&& (ds.vote_log_len.dom().contains((server_id, vt))
                ==> ds.vote_log_len[(server_id, vt)] == s.log.len())
        }),
    {
        let s = ds.server_states[server_id];
        let c = ds.server_constants[server_id];
        let pkt = choose |pkt: LRaftPacket| #![trigger ds.network.contains(pkt)] {
            &&& rf == Some(pkt.src)
            &&& ds.network.contains(pkt)
            &&& pkt.dst == server_id
            &&& LHandleMessage(s, s_, c, pkt.msg, sp)
        };
        assert(pkt.msg is RequestVote);
        let t = pkt.msg->RequestVote_term;
        let li = pkt.msg->RequestVote_last_log_index;
        let lt = pkt.msg->RequestVote_last_log_term;
        let s_mid = step_down_if_needed(s, t);
        assert(t >= s_mid.current_term && log_up_to_date(s_mid, lt, li));
        assert(i == 0 && sp[i]->VoteResponse_term == t);
        if ds.vote_log_len.dom().contains((server_id, t)) {
            let big_l = ds.vote_log_len[(server_id, t)];
            assert(VoteLogLenBounded(ds));
            assert(big_l <= s.log.len() && s.current_term >= t);
            assert(s_mid == s);
            if big_l < s.log.len() {
                let last = s.log.len() - 1;
                assert(VoteLogLenEntryTermBound(ds));
                assert(ds.server_states[(server_id, t).0].log[last].term >= (server_id, t).1);
                assert(CurrentTermGeLogTerms(ds));
                assert(ds.server_states[server_id].log[last].term <= ds.server_states[server_id].current_term);
                assert(RequestVoteLastLogTermBound(ds));
                assert(RequestVoteSummaryAlwaysValid(ds));
                assert(SenderIntegrity(ds));
                assert(TermsNonNegative(ds));
                assert(ds.server_states[server_id].current_term >= 0);
                assert(false);
            }
        }
    }

    // =========================================================================
    // Lifting one step
    // =========================================================================

    /// Every action is an `LNext` step; a promotion keeps the term and
    /// starts from a candidate.
    proof fn lemma_action_is_lnext(
        ds: RaftDistributedState, server_id: int,
        s: LState, s_: LState, c: LConstants, sp: Seq<LRaftMessage>, rf: Option<int>,
    )
        requires
            RaftActionProduces(ds, server_id, s, s_, c, sp, rf),
        ensures
            LNext(s, s_, c),
            !(s.role is Leader) && s_.role is Leader
                ==> s.role is Candidate && s_.current_term == s.current_term,
    {
        if !(s.role is Leader) && s_.role is Leader {
            lemma_lnext_non_leader_to_leader_was_candidate(s, s_, c);
        }
    }

    /// The ghost state a protocol step records.
    pub open spec fn lifted_vote_log_len(
        ds: RaftDistributedState, server_id: int, sp: Seq<LRaftMessage>,
    ) -> Map<(int, int), int> {
        if exists |i: int| #![trigger sp[i]] 0 <= i < sp.len() && sp[i] is VoteResponse && sp[i]->VoteResponse_granted {
            let i = choose |i: int| #![trigger sp[i]] 0 <= i < sp.len() && sp[i] is VoteResponse && sp[i]->VoteResponse_granted;
            ds.vote_log_len.insert((server_id, sp[i]->VoteResponse_term),
                ds.server_states[server_id].log.len() as int)
        } else {
            ds.vote_log_len
        }
    }

    pub open spec fn lifted_election_log_len(
        ds: RaftDistributedState, server_id: int, s_: LState,
    ) -> Map<(int, int), int> {
        let s = ds.server_states[server_id];
        if !(s.role is Leader) && s_.role is Leader {
            ds.election_log_len.insert((server_id, s_.current_term), s.log.len() as int)
        } else {
            ds.election_log_len
        }
    }

    pub open spec fn lifted_state(
        ds: RaftDistributedState, rs_: RaftRawState,
        server_id: int, sp: Seq<LRaftMessage>, rf: Option<int>,
    ) -> RaftDistributedState {
        let s = ds.server_states[server_id];
        let s_ = rs_.server_states[server_id];
        let c = ds.server_constants[server_id];
        RaftDistributedState {
            server_states: rs_.server_states,
            server_constants: rs_.server_constants,
            network: rs_.network,
            num_servers: rs_.num_servers,
            vote_log_len: lifted_vote_log_len(ds, server_id, sp),
            configuration_commit_certificates:
                next_configuration_commit_certificates(ds, server_id, s, s_, c, rf),
            log_commit_certificates: next_log_commit_certificates(ds, server_id, s, s_, c, rf),
            election_log_len: lifted_election_log_len(ds, server_id, s_),
            committed_history: RecordCommittedPrefix(ds.committed_history, s_),
        }
    }

    proof fn lemma_lifted_votes(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, sp: Seq<LRaftMessage>, rf: Option<int>,
    )
        requires
            RaftSafetyInvariant(ds),
            0 <= server_id < ds.num_servers,
            RaftActionProduces(ds, server_id, ds.server_states[server_id],
                ds_.server_states[server_id], ds.server_constants[server_id], sp, rf),
            ds_.vote_log_len == lifted_vote_log_len(ds, server_id, sp),
        ensures
            forall |v: int, t: int| #![trigger ds_.vote_log_len[(v, t)]] #![trigger ds.vote_log_len[(v, t)]] ds.vote_log_len.dom().contains((v, t))
                ==> ds_.vote_log_len.dom().contains((v, t))
                    && ds_.vote_log_len[(v, t)] == ds.vote_log_len[(v, t)],
            ({
                ||| (exists |vt: int| #![trigger ds_.vote_log_len.dom().contains((server_id, vt))] {
                    &&& (exists |i: int| #![trigger sp[i]]
                        0 <= i < sp.len()
                        && sp[i] is VoteResponse
                        && sp[i]->VoteResponse_term == vt
                        && sp[i]->VoteResponse_granted
                        && sp[i]->VoteResponse_voter == server_id)
                    &&& ds_.vote_log_len.dom().contains((server_id, vt))
                    &&& ds_.vote_log_len[(server_id, vt)] == ds.server_states[server_id].log.len()
                    &&& ds_.vote_log_len
                        == ds.vote_log_len.insert(
                            (server_id, vt), ds.server_states[server_id].log.len() as int)
                })
                ||| (
                    !(exists |i: int| #![trigger sp[i]]
                        0 <= i < sp.len()
                        && (sp[i] is VoteResponse)
                        && sp[i]->VoteResponse_granted)
                    && ds_.vote_log_len == ds.vote_log_len
                )
            }),
    {
        if exists |i: int| #![trigger sp[i]] 0 <= i < sp.len() && sp[i] is VoteResponse && sp[i]->VoteResponse_granted {
            let i = choose |i: int| #![trigger sp[i]] 0 <= i < sp.len() && sp[i] is VoteResponse && sp[i]->VoteResponse_granted;
            let vt = sp[i]->VoteResponse_term;
            lemma_granted_vote_record_consistent(ds, server_id, ds_.server_states[server_id], sp, rf, i);
            assert(sp[i] is VoteResponse && sp[i]->VoteResponse_term == vt
                && sp[i]->VoteResponse_granted && sp[i]->VoteResponse_voter == server_id);
            assert(ds_.vote_log_len.dom().contains((server_id, vt)));
        } else {
            assert(!(exists |i: int| #![trigger sp[i]]
                0 <= i < sp.len() && (sp[i] is VoteResponse) && sp[i]->VoteResponse_granted));
        }
    }

    proof fn lemma_lifted_elections(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, sp: Seq<LRaftMessage>, rf: Option<int>,
    )
        requires
            ElectionRecordsNotCandidate(ds),
            0 <= server_id < ds.num_servers,
            RaftActionProduces(ds, server_id, ds.server_states[server_id],
                ds_.server_states[server_id], ds.server_constants[server_id], sp, rf),
            ds_.election_log_len == lifted_election_log_len(ds, server_id, ds_.server_states[server_id]),
        ensures ({
            let s = ds.server_states[server_id];
            let s_ = ds_.server_states[server_id];
            &&& (forall |v: int, t: int| #![trigger ds_.election_log_len[(v, t)]] #![trigger ds.election_log_len[(v, t)]] ds.election_log_len.dom().contains((v, t))
                ==> ds_.election_log_len.dom().contains((v, t))
                    && ds_.election_log_len[(v, t)] == ds.election_log_len[(v, t)])
            &&& (!(s.role is Leader) && s_.role is Leader ==> {
                &&& ds_.election_log_len.dom().contains((server_id, s_.current_term))
                &&& ds_.election_log_len[(server_id, s_.current_term)] == s.log.len()
            })
            &&& (forall |v: int, t: int|
                #![trigger ds_.election_log_len.dom().contains((v, t))]
                ds_.election_log_len.dom().contains((v, t))
                && !ds.election_log_len.dom().contains((v, t))
                ==> v == server_id
                    && t == s_.current_term
                    && !(s.role is Leader)
                    && s_.role is Leader)
        }),
    {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        lemma_action_is_lnext(ds, server_id, s, s_, ds.server_constants[server_id], sp, rf);
        if !(s.role is Leader) && s_.role is Leader {
            assert(!ds.election_log_len.dom().contains((server_id, s_.current_term)));
        }
    }

    pub proof fn lemma_lift_normal(ds: RaftDistributedState, rs_: RaftRawState) -> (ds_: RaftDistributedState)
        requires
            RaftSafetyInvariant(ds),
            ElectionRecordsNotCandidate(ds),
            RawNormalNext(project(ds), rs_),
        ensures
            RaftDistributedNormalNext(ds, ds_),
            project(ds_) == rs_,
    {
        let rs = project(ds);
        let server_id = choose |server_id: int| #![trigger rs.server_states[server_id]] {
            &&& 0 <= server_id < rs.num_servers
            &&& (forall |j: int| #![trigger rs_.server_states[j]]
                0 <= j < rs.num_servers && j != server_id ==>
                rs_.server_states[j] == rs.server_states[j])
            &&& exists |sent_packets: Seq<LRaftMessage>, received_from: Option<int>|
                #![trigger RawStepWitness(rs, rs_, server_id, sent_packets, received_from)]
                RawStepWitness(rs, rs_, server_id, sent_packets, received_from)
        };
        let (sp, rf) = choose |sp: Seq<LRaftMessage>, rf: Option<int>|
            #![trigger RawStepWitness(rs, rs_, server_id, sp, rf)]
            RawStepWitness(rs, rs_, server_id, sp, rf);
        let ds_ = lifted_state(ds, rs_, server_id, sp, rf);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        assert(rs.network == ds.network);
        assert(RaftActionProduces(ds, server_id, s, s_, c, sp, rf));
        lemma_lifted_votes(ds, ds_, server_id, sp, rf);
        lemma_lifted_elections(ds, ds_, server_id, sp, rf);
        assert(RaftServerStepWitness(ds, ds_, server_id, sp, rf));
        assert(RaftServerStepWithNetwork(ds, ds_, server_id));
        assert(project(ds_) =~= rs_);
        ds_
    }

    pub proof fn lemma_lift_reboot(ds: RaftDistributedState, rs_: RaftRawState, sid: int) -> (ds_: RaftDistributedState)
        requires
            RawReboot(project(ds), rs_, sid),
        ensures
            RaftDistributedReboot(ds, ds_, sid),
            project(ds_) == rs_,
    {
        let ds_ = RaftDistributedState { server_states: rs_.server_states, ..ds };
        assert(ds_ == (RaftDistributedState {
            server_states: ds.server_states.update(sid, ds_.server_states[sid]),
            ..ds
        }));
        assert(project(ds_) =~= rs_);
        ds_
    }

    pub proof fn lemma_lift_step(ds: RaftDistributedState, rs_: RaftRawState) -> (ds_: RaftDistributedState)
        requires
            RaftSafetyInvariant(ds),
            ElectionRecordsNotCandidate(ds),
            RawNext(project(ds), rs_),
        ensures
            RaftDistributedNext(ds, ds_),
            project(ds_) == rs_,
    {
        if RawNormalNext(project(ds), rs_) {
            lemma_lift_normal(ds, rs_)
        } else {
            let sid = choose |sid: int| RawReboot(project(ds), rs_, sid);
            lemma_lift_reboot(ds, rs_, sid)
        }
    }

    // =========================================================================
    // Lifting a behavior
    // =========================================================================

    /// The proof-model state for an initial raw state: no history yet.
    pub open spec fn lifted_init(rs: RaftRawState) -> RaftDistributedState {
        RaftDistributedState {
            server_states: rs.server_states,
            server_constants: rs.server_constants,
            network: rs.network,
            num_servers: rs.num_servers,
            vote_log_len: Map::<(int, int), int>::empty(),
            configuration_commit_certificates: Map::<int, ConfigurationCommitCertificate>::empty(),
            log_commit_certificates: Map::<int, LogCommitCertificate>::empty(),
            election_log_len: Map::<(int, int), int>::empty(),
            committed_history: Seq::<LLogEntry>::empty(),
        }
    }

    /// One proof-model step, kept folded while a behavior is assembled.
    #[verifier::opaque]
    pub open spec fn lifted_step(ds: RaftDistributedState, ds_: RaftDistributedState) -> bool {
        RaftDistributedNext(ds, ds_)
    }

    pub open spec fn lifted_chain(b: RaftBehavior) -> bool {
        &&& b.len() > 0
        &&& RaftDistributedInit(b[0])
        &&& forall |i: int| #![trigger b[i]] 0 <= i < b.len() - 1 ==> lifted_step(b[i], b[i + 1])
    }

    proof fn lemma_lifted_chain_is_valid(b: RaftBehavior)
        requires
            lifted_chain(b),
        ensures
            IsValidRaftBehavior(b),
    {
        assert forall |i: int| #![trigger b[i]] 0 <= i < b.len() - 1
            implies RaftDistributedNext(b[i], b[i + 1]) by {
            assert(lifted_step(b[i], b[i + 1]));
            reveal(lifted_step);
        }
    }

    proof fn lemma_lift_prefix(rb: RaftRawBehavior, n: int) -> (b: RaftBehavior)
        requires
            IsValidRawBehavior(rb),
            1 <= n <= rb.len(),
        ensures
            b.len() == n,
            lifted_chain(b),
            forall |i: int| #![trigger b[i]] 0 <= i < n ==> project(b[i]) == rb[i],
            DynamicInvariant(b[n - 1]),
            ElectionRecordsNotCandidate(b[n - 1]),
        decreases n,
    {
        if n == 1 {
            let ds0 = lifted_init(rb[0]);
            assert(RaftDistributedInit(ds0));
            lemma_dynamic_invariant_init(ds0);
            assert(project(ds0) =~= rb[0]);
            let b = seq![ds0];
            assert(b[0] == ds0);
            b
        } else {
            let b0 = lemma_lift_prefix(rb, n - 1);
            let last = b0[n - 2];
            assert(project(last) == rb[n - 2]);
            assert(RawNext(rb[n - 2], rb[n - 1]));
            let ds_ = lemma_lift_step(last, rb[n - 1]);
            lemma_dynamic_invariant_inductive(last, ds_);
            lemma_election_records_not_candidate_inductive(last, ds_);
            assert(lifted_step(last, ds_)) by { reveal(lifted_step); }
            let b = b0.push(ds_);
            assert forall |i: int| #![trigger b[i]] 0 <= i < n implies project(b[i]) == rb[i] by {
                if i < n - 1 { assert(b[i] == b0[i]); }
            }
            assert forall |i: int| #![trigger b[i]] 0 <= i < b.len() - 1
                implies lifted_step(b[i], b[i + 1]) by {
                if i < n - 2 {
                    assert(b[i] == b0[i] && b[i + 1] == b0[i + 1]);
                    assert(lifted_step(b0[i], b0[i + 1]));
                } else {
                    assert(b[i] == last && b[i + 1] == ds_);
                }
            }
            assert(b[0] == b0[0]);
            b
        }
    }

    /// Lift theorem: every execution of the raw protocol is an execution of
    /// the proof model, with the same protocol state at every step.
    pub proof fn lemma_lift_behavior(rb: RaftRawBehavior) -> (b: RaftBehavior)
        requires
            IsValidRawBehavior(rb),
        ensures
            IsValidRaftBehavior(b),
            b.len() == rb.len(),
            forall |i: int| #![trigger b[i]] 0 <= i < rb.len() ==> project(b[i]) == rb[i],
    {
        let b = lemma_lift_prefix(rb, rb.len() as int);
        lemma_lifted_chain_is_valid(b);
        b
    }

    // =========================================================================
    // Safety of the raw protocol
    // =========================================================================

    /// In every reachable state of the raw protocol, servers agree on every
    /// index both have committed, and no term has two leaders.
    pub proof fn lemma_raw_behaviors_are_safe(rb: RaftRawBehavior, idx: int)
        requires
            IsValidRawBehavior(rb),
            0 <= idx < rb.len(),
        ensures ({
            let rs = rb[idx];
            &&& forall |i: int, j: int, k: int|
                #![trigger rs.server_states[i], rs.server_states[j].log[k]]
                0 <= i < rs.num_servers && 0 <= j < rs.num_servers
                && 0 <= k < rs.server_states[i].commit_index
                && 0 <= k < rs.server_states[j].commit_index
                && k < rs.server_states[i].log.len()
                && k < rs.server_states[j].log.len()
                ==> rs.server_states[i].log[k] == rs.server_states[j].log[k]
            &&& forall |i: int, j: int| #![trigger rs.server_states[i], rs.server_states[j]]
                0 <= i < rs.num_servers && 0 <= j < rs.num_servers
                && rs.server_states[i].role is Leader
                && rs.server_states[j].role is Leader
                && rs.server_states[i].current_term == rs.server_states[j].current_term
                ==> i == j
        }),
    {
        let b = lemma_lift_behavior(rb);
        lemma_invariant_holds_throughout_behavior(b, idx);
        assert(project(b[idx]) == rb[idx]);
        assert(StateMachineSafety(b[idx]));
        assert(ElectionSafety(b[idx]));
    }

    /// `h` is a sequential committed log that only ever grows and contains
    /// every server's committed prefix at every step of `rb`.
    pub open spec fn RawRefinementCorrect(rb: RaftRawBehavior, h: Seq<RaftSystemState>) -> bool {
        &&& h.len() == rb.len()
        &&& h.len() > 0
        &&& RaftSystemInit(h[0], Set::<int>::range(0, rb[0].num_servers))
        &&& (forall |i: int| #![trigger h[i]] 0 <= i < h.len() - 1 ==> RaftSystemNext(h[i], h[i + 1]))
        &&& (forall |i: int, sid: int| #![trigger h[i], rb[i].server_states[sid]]
            0 <= i < rb.len() && 0 <= sid < rb[i].num_servers
            ==> committed_prefix_in_log(rb[i].server_states[sid], h[i].committed_log))
    }

    /// A server's committed prefix is a prefix of `log`.
    pub open spec fn committed_prefix_in_log(s: LState, log: Seq<int>) -> bool {
        &&& s.commit_index <= log.len()
        &&& s.commit_index <= s.log.len()
        &&& forall |k: int| #![trigger log[k]]
            0 <= k < s.commit_index ==> log[k] == s.log[k].value
    }

    /// `b` is a valid proof-model behavior, kept folded so that indexing
    /// into `b` does not unfold its transition relation.
    #[verifier::opaque]
    pub open spec fn lifted_valid(b: RaftBehavior) -> bool {
        IsValidRaftBehavior(b)
    }

    proof fn lemma_raw_commit_in_abstract_log(
        rb: RaftRawBehavior, b: RaftBehavior, h: Seq<RaftSystemState>, i: int, sid: int,
    )
        requires
            lifted_valid(b),
            b.len() == rb.len(),
            forall |x: int| #![trigger b[x]] 0 <= x < rb.len() ==> project(b[x]) == rb[x],
            RaftSystemBehaviorRefinementCorrect(b, h),
            0 <= i < rb.len(),
            0 <= sid < rb[i].num_servers,
        ensures
            committed_prefix_in_log(rb[i].server_states[sid], h[i].committed_log),
    {
        assert(project(b[i]) == rb[i]);
        reveal(lifted_valid);
        lemma_invariant_holds_throughout_behavior(b, i);
        assert(RaftSystemRefinement(b[i], h[i]));
        let s = b[i].server_states[sid];
        assert(CommitIndexBounded(b[i]));
        assert(CommitHistoryValid(b[i]));
        assert(s.commit_index <= s.log.len());
        assert(s.commit_index <= b[i].committed_history.len());
        assert forall |k: int| #![trigger h[i].committed_log[k]]
            0 <= k < s.commit_index implies h[i].committed_log[k] == s.log[k].value by {
            lemma_local_commit_matches_history(b[i], sid, k);
        }
    }

    proof fn lemma_raw_refinement_from_lifted(rb: RaftRawBehavior, b: RaftBehavior, h: Seq<RaftSystemState>)
        requires
            lifted_valid(b),
            b.len() == rb.len(),
            forall |x: int| #![trigger b[x]] 0 <= x < rb.len() ==> project(b[x]) == rb[x],
            RaftSystemBehaviorRefinementCorrect(b, h),
        ensures
            RawRefinementCorrect(rb, h),
    {
        assert(project(b[0]) == rb[0]);
        assert forall |i: int, sid: int| #![trigger h[i], rb[i].server_states[sid]]
            0 <= i < rb.len() && 0 <= sid < rb[i].num_servers
            implies committed_prefix_in_log(rb[i].server_states[sid], h[i].committed_log) by {
            lemma_raw_commit_in_abstract_log(rb, b, h, i, sid);
        }
    }

    /// The raw protocol refines a sequential log: for every raw behavior there
    /// is an abstract behavior that only ever extends one committed log, and
    /// every server's committed prefix is a prefix of it at every step.
    pub proof fn lemma_raw_refinement_correct(rb: RaftRawBehavior)
        requires
            IsValidRawBehavior(rb),
        ensures
            exists |h: Seq<RaftSystemState>| #![trigger RawRefinementCorrect(rb, h)] RawRefinementCorrect(rb, h),
    {
        let b = lemma_lift_behavior(rb);
        lemma_refinement_correct(b);
        let h = choose |h: Seq<RaftSystemState>| RaftSystemBehaviorRefinementCorrect(b, h);
        reveal(lifted_valid);
        lemma_raw_refinement_from_lifted(rb, b, h);
    }

} // verus!
