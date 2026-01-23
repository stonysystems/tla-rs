// Test for LReplicaNextProcess1b predicate
// Tests: Cross-component dispatching - routes to Proposer AND Acceptor
// This is a key multi-component dispatch pattern in RSL protocol
//
// Pattern demonstrated:
// - Conditional branching based on multiple conditions
// - Calling LProposerProcess1b when processing
// - Calling LAcceptorTruncateLog when processing
// - Both components updated in single step when processing
// - No change to state when not processing

use vstd::prelude::*;
use vstd::set::*;
use vstd::map::*;
use vstd::seq::*;

verus! {
    // === SPEC TYPES ===

    pub type OperationNumber = int;
    pub type Votes = Map<OperationNumber, int>;

    // Simplified packet
    pub struct RslPacket {
        pub src: int,
        pub bal_1b: int,
        pub log_truncation_point: OperationNumber,
    }

    // Simplified proposer
    pub struct LProposer {
        pub my_index: int,
        pub current_state: int,
        pub max_ballot_i_sent_1a: int,
        pub received_1b_packets: Set<RslPacket>,
        pub valid_sources: Set<int>,
    }

    // Simplified acceptor
    pub struct LAcceptor {
        pub max_bal: int,
        pub votes: Votes,
        pub log_truncation_point: OperationNumber,
    }

    // Simplified replica state
    pub struct LReplica {
        pub proposer: LProposer,
        pub acceptor: LAcceptor,
        pub learner: int,
    }

    // === HELPER PREDICATES ===

    pub open spec fn RemoveVotesBefore(
        votes: Votes,
        votes_: Votes,
        log_truncation_point: OperationNumber
    ) -> bool
    {
        &&& (forall |opn: OperationNumber| #![auto] votes_.contains_key(opn) ==> votes.contains_key(opn) && votes_[opn] == votes[opn])
        &&& (forall |opn: OperationNumber| #![auto] opn < log_truncation_point ==> !votes_.contains_key(opn))
        &&& (forall |opn: OperationNumber| #![auto] opn >= log_truncation_point && votes.contains_key(opn) ==> votes_.contains_key(opn))
    }

    pub open spec fn LAcceptorTruncateLog(
        s: LAcceptor,
        s_: LAcceptor,
        opn: OperationNumber
    ) -> bool
    {
        if opn <= s.log_truncation_point {
            s_ == s
        } else {
            &&& s_.max_bal == s.max_bal
            &&& s_.log_truncation_point == opn
            &&& RemoveVotesBefore(s.votes, s_.votes, opn)
        }
    }

    pub open spec fn LProposerProcess1b(
        s: LProposer,
        s_: LProposer,
        p: RslPacket
    ) -> bool
    {
        &&& s_.my_index == s.my_index
        &&& s_.current_state == s.current_state
        &&& s_.max_ballot_i_sent_1a == s.max_ballot_i_sent_1a
        &&& s_.received_1b_packets == s.received_1b_packets + set![p]
        &&& s_.valid_sources == s.valid_sources
    }

    // === MAIN PREDICATE ===
    // LReplicaNextProcess1b - dispatches to both Proposer and Acceptor
    // Simplified: uses a 'should_process' parameter to abstract the complex condition

    pub open spec fn LReplicaNextProcess1b(
        s: LReplica,
        s_: LReplica,
        received_packet: RslPacket,
        sent_packets: Seq<RslPacket>,
        should_process: bool  // Abstracts: src in config && ballot matches && state == 1 && no duplicate
    ) -> bool
    {
        if should_process {
            // Process: dispatch to both Proposer and Acceptor
            &&& LProposerProcess1b(s.proposer, s_.proposer, received_packet)
            &&& LAcceptorTruncateLog(s.acceptor, s_.acceptor, received_packet.log_truncation_point)
            &&& sent_packets == Seq::<RslPacket>::empty()
            &&& s_.learner == s.learner
        } else {
            // No change
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    // === EXEC TYPES ===

    pub struct CVotes {
        pub ghost_state: Ghost<Votes>,
    }

    impl CVotes {
        pub open spec fn well_formed(&self) -> bool { true }

        #[verifier::external_body]
        pub fn filter_by_threshold(&self, threshold: i64) -> (result: CVotes)
            ensures RemoveVotesBefore(self@, result@, threshold as int)
        {
            unimplemented!()
        }

        pub fn clone_ghost(&self) -> (result: CVotes)
            ensures result@ == self@
        {
            CVotes { ghost_state: Ghost(self.ghost_state@) }
        }
    }

    impl View for CVotes {
        type V = Votes;
        open spec fn view(&self) -> Votes {
            self.ghost_state@
        }
    }

    pub struct CPacketSet {
        pub ghost_set: Ghost<Set<RslPacket>>,
    }

    impl CPacketSet {
        pub fn insert(&self, p: &CRslPacket) -> (result: CPacketSet)
            ensures result@ == self@ + set![p@]
        {
            CPacketSet { ghost_set: Ghost(self.ghost_set@ + set![p@]) }
        }

        pub fn clone_ghost(&self) -> (result: CPacketSet)
            ensures result@ == self@
        {
            CPacketSet { ghost_set: Ghost(self.ghost_set@) }
        }
    }

    impl View for CPacketSet {
        type V = Set<RslPacket>;
        open spec fn view(&self) -> Set<RslPacket> {
            self.ghost_set@
        }
    }

    pub struct CValidSources {
        pub ghost_set: Ghost<Set<int>>,
    }

    impl CValidSources {
        pub fn clone_ghost(&self) -> (result: CValidSources)
            ensures result@ == self@
        {
            CValidSources { ghost_set: Ghost(self.ghost_set@) }
        }
    }

    impl View for CValidSources {
        type V = Set<int>;
        open spec fn view(&self) -> Set<int> {
            self.ghost_set@
        }
    }

    pub struct CRslPacket {
        pub src: i64,
        pub bal_1b: i64,
        pub log_truncation_point: i64,
    }

    impl CRslPacket {
        pub open spec fn well_formed(&self) -> bool { true }
    }

    impl View for CRslPacket {
        type V = RslPacket;
        open spec fn view(&self) -> RslPacket {
            RslPacket {
                src: self.src as int,
                bal_1b: self.bal_1b as int,
                log_truncation_point: self.log_truncation_point as int,
            }
        }
    }

    pub struct CProposer {
        pub my_index: i64,
        pub current_state: i64,
        pub max_ballot_i_sent_1a: i64,
        pub received_1b_packets: CPacketSet,
        pub valid_sources: CValidSources,
    }

    impl CProposer {
        pub open spec fn well_formed(&self) -> bool { true }
    }

    impl View for CProposer {
        type V = LProposer;
        open spec fn view(&self) -> LProposer {
            LProposer {
                my_index: self.my_index as int,
                current_state: self.current_state as int,
                max_ballot_i_sent_1a: self.max_ballot_i_sent_1a as int,
                received_1b_packets: self.received_1b_packets@,
                valid_sources: self.valid_sources@,
            }
        }
    }

    pub struct CAcceptor {
        pub max_bal: i64,
        pub votes: CVotes,
        pub log_truncation_point: i64,
    }

    impl CAcceptor {
        pub open spec fn well_formed(&self) -> bool {
            self.votes.well_formed()
        }
    }

    impl View for CAcceptor {
        type V = LAcceptor;
        open spec fn view(&self) -> LAcceptor {
            LAcceptor {
                max_bal: self.max_bal as int,
                votes: self.votes@,
                log_truncation_point: self.log_truncation_point as int,
            }
        }
    }

    pub struct CReplica {
        pub proposer: CProposer,
        pub acceptor: CAcceptor,
        pub learner: i64,
    }

    impl CReplica {
        pub open spec fn well_formed(&self) -> bool {
            self.proposer.well_formed() && self.acceptor.well_formed()
        }
    }

    impl View for CReplica {
        type V = LReplica;
        open spec fn view(&self) -> LReplica {
            LReplica {
                proposer: self.proposer@,
                acceptor: self.acceptor@,
                learner: self.learner as int,
            }
        }
    }

    // === EXEC HELPER FUNCTIONS ===

    fn c_proposer_process_1b(s: &CProposer, p: &CRslPacket) -> (result: CProposer)
        requires s.well_formed(), p.well_formed()
        ensures LProposerProcess1b(s@, result@, p@)
    {
        CProposer {
            my_index: s.my_index,
            current_state: s.current_state,
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            received_1b_packets: s.received_1b_packets.insert(p),
            valid_sources: s.valid_sources.clone_ghost(),
        }
    }

    fn c_acceptor_truncate_log(s: &CAcceptor, opn: i64) -> (result: CAcceptor)
        requires s.well_formed()
        ensures LAcceptorTruncateLog(s@, result@, opn as int)
    {
        if opn <= s.log_truncation_point {
            CAcceptor {
                max_bal: s.max_bal,
                votes: s.votes.clone_ghost(),
                log_truncation_point: s.log_truncation_point,
            }
        } else {
            CAcceptor {
                max_bal: s.max_bal,
                votes: s.votes.filter_by_threshold(opn),
                log_truncation_point: opn,
            }
        }
    }

    // === MAIN EXEC FUNCTION ===
    // Implements LReplicaNextProcess1b with cross-component dispatch
    // Takes should_process as input (computed externally from complex conditions)

    pub fn c_replica_next_process_1b(
        s: &CReplica,
        received_packet: &CRslPacket,
        should_process: bool,
    ) -> (result: (CReplica, Vec<CRslPacket>))
        requires
            s.well_formed(),
            received_packet.well_formed(),
        ensures
            result.0.well_formed(),
            LReplicaNextProcess1b(s@, result.0@, received_packet@, result.1@.map(|i, p: CRslPacket| p@), should_process),
    {
        if should_process {
            // Process the 1b message: dispatch to BOTH components
            let new_proposer = c_proposer_process_1b(&s.proposer, received_packet);
            let new_acceptor = c_acceptor_truncate_log(&s.acceptor, received_packet.log_truncation_point);

            let new_replica = CReplica {
                proposer: new_proposer,
                acceptor: new_acceptor,
                learner: s.learner,
            };

            let empty_packets: Vec<CRslPacket> = Vec::new();
            proof {
                assert(LProposerProcess1b(s.proposer@, new_replica.proposer@, received_packet@));
                assert(LAcceptorTruncateLog(s.acceptor@, new_replica.acceptor@, received_packet.log_truncation_point as int));
                assert(new_replica.learner as int == s.learner as int);
                assert(empty_packets@.map(|i, p: CRslPacket| p@) =~= Seq::<RslPacket>::empty());
            }

            (new_replica, empty_packets)
        } else {
            // No change - clone the replica
            let same_proposer = CProposer {
                my_index: s.proposer.my_index,
                current_state: s.proposer.current_state,
                max_ballot_i_sent_1a: s.proposer.max_ballot_i_sent_1a,
                received_1b_packets: s.proposer.received_1b_packets.clone_ghost(),
                valid_sources: s.proposer.valid_sources.clone_ghost(),
            };
            let same_acceptor = CAcceptor {
                max_bal: s.acceptor.max_bal,
                votes: s.acceptor.votes.clone_ghost(),
                log_truncation_point: s.acceptor.log_truncation_point,
            };
            proof {
                assert(same_proposer@ == s.proposer@);
                assert(same_acceptor@ == s.acceptor@);
            }
            let same_replica = CReplica {
                proposer: same_proposer,
                acceptor: same_acceptor,
                learner: s.learner,
            };
            let empty_packets: Vec<CRslPacket> = Vec::new();
            proof {
                assert(same_replica@ == s@);
                assert(empty_packets@.map(|i, p: CRslPacket| p@) =~= Seq::<RslPacket>::empty());
            }
            (same_replica, empty_packets)
        }
    }
}

fn main() {}
