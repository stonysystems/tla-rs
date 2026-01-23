// Complete LProposer Init example with both spec and exec
// Tests: cross-predicate calls, enum variant check, recommends clause
// Based on RSL proposer.rs LProposerInit predicate

use vstd::prelude::*;
use vstd::map::*;
use vstd::set::*;

verus! {
    // === SPEC TYPES ===

    // Type aliases
    pub type AbstractEndPoint = int;
    pub type OperationNumber = int;

    pub struct Ballot {
        pub seqno: int,
        pub proposer_id: int,
    }

    pub struct Request {
        pub client: AbstractEndPoint,
        pub seqno: int,
    }

    // Simplified configuration
    pub struct LConfiguration {
        pub replica_ids: Seq<AbstractEndPoint>,
    }

    // Simplified parameters
    pub struct LParameters {
        pub baseline_view_timeout_period: int,
    }

    pub struct LConstants {
        pub config: LConfiguration,
        pub params: LParameters,
    }

    pub struct LReplicaConstants {
        pub my_index: int,
        pub all: LConstants,
    }

    pub open spec fn WellFormedLConfiguration(c: LConfiguration) -> bool {
        c.replica_ids.len() > 0
    }

    // Election state
    pub struct ElectionState {
        pub constants: LReplicaConstants,
        pub current_view: Ballot,
        pub current_view_suspectors: Set<int>,
        pub epoch_end_time: int,
        pub epoch_length: int,
        pub requests_received_this_epoch: Seq<Request>,
        pub requests_received_prev_epochs: Seq<Request>,
    }

    // Incomplete batch timer enum
    pub enum IncompleteBatchTimer {
        IncompleteBatchTimerOn{ when: int },
        IncompleteBatchTimerOff{},
    }

    // RslPacket placeholder (simplified)
    pub struct RslPacket {
        pub src: AbstractEndPoint,
    }

    // Proposer struct
    pub struct LProposer {
        pub constants: LReplicaConstants,
        pub current_state: int,
        pub request_queue: Seq<Request>,
        pub max_ballot_i_sent_1a: Ballot,
        pub next_operation_number_to_propose: int,
        pub received_1b_packets: Set<RslPacket>,
        pub highest_seqno_requested_by_client_this_view: Map<AbstractEndPoint, int>,
        pub incomplete_batch_timer: IncompleteBatchTimer,
        pub election_state: ElectionState,
    }

    // === SPEC PREDICATES ===

    // ElectionStateInit predicate (from election.rs)
    pub open spec fn ElectionStateInit(es: ElectionState, c: LReplicaConstants) -> bool
        recommends
            c.all.config.replica_ids.len() > 0
    {
        &&& es.constants == c
        &&& es.current_view == Ballot{seqno: 1, proposer_id: 0}
        &&& es.current_view_suspectors == Set::<int>::empty()
        &&& es.epoch_end_time == 0
        &&& es.epoch_length == c.all.params.baseline_view_timeout_period
        &&& es.requests_received_this_epoch == Seq::<Request>::empty()
        &&& es.requests_received_prev_epochs == Seq::<Request>::empty()
    }

    // LProposerInit predicate (from proposer.rs)
    pub open spec fn LProposerInit(s: LProposer, c: LReplicaConstants) -> bool
        recommends
            WellFormedLConfiguration(c.all.config)
    {
        &&& s.constants == c
        &&& s.current_state == 0
        &&& s.request_queue == Seq::<Request>::empty()
        &&& s.max_ballot_i_sent_1a == Ballot{seqno: 0, proposer_id: c.my_index}
        &&& s.next_operation_number_to_propose == 0
        &&& s.received_1b_packets == Set::<RslPacket>::empty()
        &&& s.highest_seqno_requested_by_client_this_view == Map::<AbstractEndPoint, int>::empty()
        &&& ElectionStateInit(s.election_state, c)
        &&& s.incomplete_batch_timer is IncompleteBatchTimerOff
    }

    // === EXEC TYPES ===

    pub struct CBallot {
        pub seqno: i64,
        pub proposer_id: i64,
    }

    impl CBallot {
        pub open spec fn well_formed(&self) -> bool { true }
    }

    impl View for CBallot {
        type V = Ballot;
        open spec fn view(&self) -> Ballot {
            Ballot {
                seqno: self.seqno as int,
                proposer_id: self.proposer_id as int,
            }
        }
    }

    pub struct CConfiguration {
        // Simplified - would have CVec<i64> for replica_ids
        pub num_replicas: i64,
    }

    impl CConfiguration {
        pub open spec fn well_formed(&self) -> bool {
            self.num_replicas > 0
        }
    }

    impl View for CConfiguration {
        type V = LConfiguration;
        open spec fn view(&self) -> LConfiguration {
            // Simplified - just create a seq of appropriate length
            LConfiguration {
                replica_ids: Seq::new(self.num_replicas as nat, |i: int| i),
            }
        }
    }

    pub struct CParameters {
        pub baseline_view_timeout_period: i64,
    }

    impl CParameters {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn clone_for_view(&self) -> (result: CParameters)
            ensures result@ == self@
        {
            CParameters { baseline_view_timeout_period: self.baseline_view_timeout_period }
        }
    }

    impl View for CParameters {
        type V = LParameters;
        open spec fn view(&self) -> LParameters {
            LParameters {
                baseline_view_timeout_period: self.baseline_view_timeout_period as int,
            }
        }
    }

    pub struct CConstants {
        pub config: CConfiguration,
        pub params: CParameters,
    }

    impl CConstants {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.config.well_formed()
            &&& self.params.well_formed()
        }

        pub fn clone_for_view(&self) -> (result: CConstants)
            requires self.well_formed()
            ensures
                result@ == self@,
                result.well_formed(),
                result.config.num_replicas == self.config.num_replicas,
        {
            CConstants {
                config: CConfiguration { num_replicas: self.config.num_replicas },
                params: self.params.clone_for_view(),
            }
        }
    }

    impl View for CConstants {
        type V = LConstants;
        open spec fn view(&self) -> LConstants {
            LConstants {
                config: self.config@,
                params: self.params@,
            }
        }
    }

    pub struct CReplicaConstants {
        pub my_index: i64,
        pub all: CConstants,
    }

    impl CReplicaConstants {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.my_index >= 0
            &&& self.all.well_formed()
            &&& self.my_index < self.all.config.num_replicas
        }

        pub fn clone_for_view(&self) -> (result: CReplicaConstants)
            requires self.well_formed()
            ensures
                result@ == self@,
                result.well_formed(),
                result.my_index == self.my_index,
                result.all.config.num_replicas == self.all.config.num_replicas,
        {
            CReplicaConstants {
                my_index: self.my_index,
                all: self.all.clone_for_view(),
            }
        }
    }

    impl View for CReplicaConstants {
        type V = LReplicaConstants;
        open spec fn view(&self) -> LReplicaConstants {
            LReplicaConstants {
                my_index: self.my_index as int,
                all: self.all@,
            }
        }
    }

    // Empty collections (simplified)
    pub struct CRequestQueue {}

    impl CRequestQueue {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn empty() -> (result: CRequestQueue)
            ensures result@ == Seq::<Request>::empty()
        {
            CRequestQueue {}
        }
    }

    impl View for CRequestQueue {
        type V = Seq<Request>;
        open spec fn view(&self) -> Seq<Request> {
            Seq::<Request>::empty()
        }
    }

    pub struct CPacketSet {}

    impl CPacketSet {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn empty() -> (result: CPacketSet)
            ensures result@ == Set::<RslPacket>::empty()
        {
            CPacketSet {}
        }
    }

    impl View for CPacketSet {
        type V = Set<RslPacket>;
        open spec fn view(&self) -> Set<RslPacket> {
            Set::<RslPacket>::empty()
        }
    }

    pub struct CSeqnoMap {}

    impl CSeqnoMap {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn empty() -> (result: CSeqnoMap)
            ensures result@ == Map::<AbstractEndPoint, int>::empty()
        {
            CSeqnoMap {}
        }
    }

    impl View for CSeqnoMap {
        type V = Map<AbstractEndPoint, int>;
        open spec fn view(&self) -> Map<AbstractEndPoint, int> {
            Map::<AbstractEndPoint, int>::empty()
        }
    }

    pub struct CSuspectorSet {}

    impl CSuspectorSet {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn empty() -> (result: CSuspectorSet)
            ensures result@ == Set::<int>::empty()
        {
            CSuspectorSet {}
        }
    }

    impl View for CSuspectorSet {
        type V = Set<int>;
        open spec fn view(&self) -> Set<int> {
            Set::<int>::empty()
        }
    }

    pub enum CIncompleteBatchTimer {
        CIncompleteBatchTimerOn{ when: i64 },
        CIncompleteBatchTimerOff{},
    }

    impl CIncompleteBatchTimer {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn off() -> (result: CIncompleteBatchTimer)
            ensures result@ is IncompleteBatchTimerOff
        {
            CIncompleteBatchTimer::CIncompleteBatchTimerOff{}
        }
    }

    impl View for CIncompleteBatchTimer {
        type V = IncompleteBatchTimer;
        open spec fn view(&self) -> IncompleteBatchTimer {
            match self {
                CIncompleteBatchTimer::CIncompleteBatchTimerOn{ when } => {
                    IncompleteBatchTimer::IncompleteBatchTimerOn{ when: *when as int }
                }
                CIncompleteBatchTimer::CIncompleteBatchTimerOff{} => {
                    IncompleteBatchTimer::IncompleteBatchTimerOff{}
                }
            }
        }
    }

    pub struct CElectionState {
        pub constants: CReplicaConstants,
        pub current_view: CBallot,
        pub current_view_suspectors: CSuspectorSet,
        pub epoch_end_time: i64,
        pub epoch_length: i64,
        pub requests_received_this_epoch: CRequestQueue,
        pub requests_received_prev_epochs: CRequestQueue,
    }

    impl CElectionState {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.constants.well_formed()
            &&& self.current_view.well_formed()
            &&& self.current_view_suspectors.well_formed()
            &&& self.requests_received_this_epoch.well_formed()
            &&& self.requests_received_prev_epochs.well_formed()
        }
    }

    impl View for CElectionState {
        type V = ElectionState;
        open spec fn view(&self) -> ElectionState {
            ElectionState {
                constants: self.constants@,
                current_view: self.current_view@,
                current_view_suspectors: self.current_view_suspectors@,
                epoch_end_time: self.epoch_end_time as int,
                epoch_length: self.epoch_length as int,
                requests_received_this_epoch: self.requests_received_this_epoch@,
                requests_received_prev_epochs: self.requests_received_prev_epochs@,
            }
        }
    }

    pub struct CProposer {
        pub constants: CReplicaConstants,
        pub current_state: i64,
        pub request_queue: CRequestQueue,
        pub max_ballot_i_sent_1a: CBallot,
        pub next_operation_number_to_propose: i64,
        pub received_1b_packets: CPacketSet,
        pub highest_seqno_requested_by_client_this_view: CSeqnoMap,
        pub incomplete_batch_timer: CIncompleteBatchTimer,
        pub election_state: CElectionState,
    }

    impl CProposer {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.constants.well_formed()
            &&& self.request_queue.well_formed()
            &&& self.max_ballot_i_sent_1a.well_formed()
            &&& self.received_1b_packets.well_formed()
            &&& self.highest_seqno_requested_by_client_this_view.well_formed()
            &&& self.incomplete_batch_timer.well_formed()
            &&& self.election_state.well_formed()
        }
    }

    impl View for CProposer {
        type V = LProposer;
        open spec fn view(&self) -> LProposer {
            LProposer {
                constants: self.constants@,
                current_state: self.current_state as int,
                request_queue: self.request_queue@,
                max_ballot_i_sent_1a: self.max_ballot_i_sent_1a@,
                next_operation_number_to_propose: self.next_operation_number_to_propose as int,
                received_1b_packets: self.received_1b_packets@,
                highest_seqno_requested_by_client_this_view: self.highest_seqno_requested_by_client_this_view@,
                incomplete_batch_timer: self.incomplete_batch_timer@,
                election_state: self.election_state@,
            }
        }
    }

    // === EXEC HELPER FUNCTION ===

    // Exec version of ElectionStateInit
    fn c_election_state_init(c: &CReplicaConstants) -> (result: CElectionState)
        requires
            c.well_formed(),
        ensures
            result.well_formed(),
            ElectionStateInit(result@, c@),
    {
        CElectionState {
            constants: c.clone_for_view(),
            current_view: CBallot {
                seqno: 1,
                proposer_id: 0,
            },
            current_view_suspectors: CSuspectorSet::empty(),
            epoch_end_time: 0,
            epoch_length: c.all.params.baseline_view_timeout_period,
            requests_received_this_epoch: CRequestQueue::empty(),
            requests_received_prev_epochs: CRequestQueue::empty(),
        }
    }

    // === EXEC FUNCTION (transpiler-generated pattern) ===

    pub fn c_proposer_init(c: &CReplicaConstants) -> (result: CProposer)
        requires
            c.well_formed(),
        ensures
            result.well_formed(),
            LProposerInit(result@, c@),
    {
        CProposer {
            constants: c.clone_for_view(),
            current_state: 0,
            request_queue: CRequestQueue::empty(),
            max_ballot_i_sent_1a: CBallot {
                seqno: 0,
                proposer_id: c.my_index,
            },
            next_operation_number_to_propose: 0,
            received_1b_packets: CPacketSet::empty(),
            highest_seqno_requested_by_client_this_view: CSeqnoMap::empty(),
            incomplete_batch_timer: CIncompleteBatchTimer::off(),
            election_state: c_election_state_init(c),
        }
    }
}

fn main() {}
