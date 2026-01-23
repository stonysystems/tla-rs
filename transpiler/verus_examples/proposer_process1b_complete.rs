// Test for LProposerProcess1b predicate
// Tests: set addition (s.received_1b_packets + set![p])
// Pattern: Adding a packet to a set of received packets

use vstd::prelude::*;
use vstd::set::*;

verus! {
    // === SPEC TYPES ===

    // Simplified packet type
    pub struct RslPacket {
        pub src: int,
        pub msg: int,  // Simplified message
    }

    // Simplified proposer state with focus on received_1b_packets
    pub struct LProposer {
        pub constants: int,
        pub current_state: int,
        pub request_queue: int,  // Simplified
        pub max_ballot_i_sent_1a: int,  // Simplified ballot
        pub next_operation_number_to_propose: int,
        pub received_1b_packets: Set<RslPacket>,
        pub highest_seqno_requested_by_client_this_view: int,  // Simplified
        pub incomplete_batch_timer: int,  // Simplified
        pub election_state: int,  // Simplified
    }

    // === SPEC PREDICATE ===
    // LProposerProcess1b: Adds received packet to the set

    pub open spec fn LProposerProcess1b(
        s: LProposer,
        s_: LProposer,
        p: RslPacket
    ) -> bool
    // recommends are omitted for testing
    {
        s_ == LProposer {
            constants: s.constants,
            current_state: s.current_state,
            request_queue: s.request_queue,
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: s.next_operation_number_to_propose,
            received_1b_packets: s.received_1b_packets + set![p],
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view,
            incomplete_batch_timer: s.incomplete_batch_timer,
            election_state: s.election_state,
        }
    }

    // === EXEC TYPES ===

    // Concrete packet type
    #[derive(Clone)]
    pub struct CRslPacket {
        pub src: i64,
        pub msg: i64,
    }

    impl CRslPacket {
        pub open spec fn well_formed(&self) -> bool { true }
    }

    impl View for CRslPacket {
        type V = RslPacket;
        open spec fn view(&self) -> RslPacket {
            RslPacket {
                src: self.src as int,
                msg: self.msg as int,
            }
        }
    }

    // Ghost wrapper for set of packets
    pub struct CPacketSet {
        pub ghost_set: Ghost<Set<RslPacket>>,
    }

    impl CPacketSet {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn empty() -> (result: CPacketSet)
            ensures result@ == Set::<RslPacket>::empty()
        {
            CPacketSet { ghost_set: Ghost(Set::empty()) }
        }

        // Add a packet to the set
        pub fn insert(&self, p: &CRslPacket) -> (result: CPacketSet)
            ensures result@ == self@ + set![p@]
        {
            CPacketSet { ghost_set: Ghost(self.ghost_set@ + set![p@]) }
        }

        pub fn clone_for_view(&self) -> (result: CPacketSet)
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

    // Concrete proposer type
    pub struct CProposer {
        pub constants: i64,
        pub current_state: i64,
        pub request_queue: i64,
        pub max_ballot_i_sent_1a: i64,
        pub next_operation_number_to_propose: i64,
        pub received_1b_packets: CPacketSet,
        pub highest_seqno_requested_by_client_this_view: i64,
        pub incomplete_batch_timer: i64,
        pub election_state: i64,
    }

    impl CProposer {
        pub open spec fn well_formed(&self) -> bool {
            self.received_1b_packets.well_formed()
        }
    }

    impl View for CProposer {
        type V = LProposer;
        open spec fn view(&self) -> LProposer {
            LProposer {
                constants: self.constants as int,
                current_state: self.current_state as int,
                request_queue: self.request_queue as int,
                max_ballot_i_sent_1a: self.max_ballot_i_sent_1a as int,
                next_operation_number_to_propose: self.next_operation_number_to_propose as int,
                received_1b_packets: self.received_1b_packets@,
                highest_seqno_requested_by_client_this_view: self.highest_seqno_requested_by_client_this_view as int,
                incomplete_batch_timer: self.incomplete_batch_timer as int,
                election_state: self.election_state as int,
            }
        }
    }

    // === EXEC FUNCTION ===
    // Implements LProposerProcess1b

    pub fn c_proposer_process_1b(s: &CProposer, p: &CRslPacket) -> (result: CProposer)
        requires
            s.well_formed(),
            p.well_formed(),
        ensures
            result.well_formed(),
            LProposerProcess1b(s@, result@, p@),
    {
        CProposer {
            constants: s.constants,
            current_state: s.current_state,
            request_queue: s.request_queue,
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: s.next_operation_number_to_propose,
            received_1b_packets: s.received_1b_packets.insert(p),
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view,
            incomplete_batch_timer: s.incomplete_batch_timer,
            election_state: s.election_state,
        }
    }
}

fn main() {}
