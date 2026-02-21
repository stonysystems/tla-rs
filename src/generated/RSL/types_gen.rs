// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::common::collections::hashsets::HashSetWellFormed;
use crate::common::collections::seq_is_unique_v::*;
use crate::common::collections::seqs::*;
use crate::common::framework::environment_s::{LIoOp, LPacket};
use crate::common::native::io_s::{AbstractEndPoint, EndPoint};
use crate::implementation::common::generic_refinement::*;
use crate::implementation::common::marshalling::*;
use crate::implementation::RSL::appinterface::{CAppStateIsAbstractable, CAppStateIsValid};
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::acceptor::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::{RslIo, RslPacket};
use crate::protocol::RSL::executor::*;
use crate::protocol::RSL::learner::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::parameters::*;
use crate::protocol::RSL::proposer::*;
use crate::protocol::RSL::replica::*;
use crate::protocol::RSL::replica::LScheduler;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
use std::collections::{HashMap, HashSet};
use vstd::prelude::*;
use vstd::seq::*;
use vstd::{map::*, modes::*, seq_lib::*};
use vstd::{set::*, set_lib::*};

pub use crate::implementation::RSL::types_i::*;
pub use crate::implementation::RSL::cmessage::*;
pub use crate::implementation::RSL::appinterface::{CAppState, CAppStateInit, CAppMessage};
pub use crate::implementation::RSL::CStateMachine::*;
pub use crate::implementation::RSL::cconfiguration::{CConfiguration, ReplicaIndexValid};
pub use crate::implementation::RSL::cconstants::{CConstants, CReplicaConstants};
pub use crate::implementation::RSL::acceptorimpl::CAcceptor;
pub use crate::implementation::RSL::learnerimpl::CLearner;
pub use crate::implementation::RSL::ElectionImpl::{CElectionState, COutstandingOperation, CRequestHeader};
pub use crate::implementation::RSL::cbroadcast::*;
pub use crate::implementation::common::upper_bound::*;
pub use crate::implementation::common::upper_bound_i::*;

verus! {

pub type COperationNumber = u64;
pub type CRequestBatch = Vec<CRequest>;
pub type CReplyCache = HashMap<EndPoint, CReply>;
pub type CVotes = HashMap<COperationNumber, CVote>;
pub type CLearnerState = HashMap<COperationNumber, CLearnerTuple>;
pub type CRslIo = LIoOp<EndPoint, CMessage>;

#[derive(Clone, Copy)]
pub struct CClockReading {
    pub t: u64,
}

impl CClockReading {
    pub fn clone_up_to_view(&self) -> (result: Self)
    ensures
        result@ == self@,
    {
        CClockReading {
            t: self.t,
        }
    }
}

impl CClockReading {
    pub open spec fn valid(&self) -> bool {
        true
    }
}

impl View for CClockReading {
    type V = ClockReading;

    open spec fn view(&self) -> ClockReading {
        ClockReading {
            t: self.t as int,
        }
    }
}

#[derive(Clone, Copy)]
pub struct CParameters {
    pub max_log_length: u64,
    pub baseline_view_timeout_period: u64,
    pub heartbeat_period: u64,
    pub max_integer_val: u64,
    pub max_batch_size: u64,
    pub max_batch_delay: u64,
}

impl CParameters {
    pub fn clone_up_to_view(&self) -> (result: Self)
    ensures
        result@ == self@,
    {
        CParameters {
            max_log_length: self.max_log_length,
            baseline_view_timeout_period: self.baseline_view_timeout_period,
            heartbeat_period: self.heartbeat_period,
            max_integer_val: self.max_integer_val,
            max_batch_size: self.max_batch_size,
            max_batch_delay: self.max_batch_delay,
        }
    }
}



/// Helper for match arms that are provably unreachable.
/// The requires clause is `false`, so Verus verifies this can never be called.
#[verifier(external_body)]
pub fn unreachable_value<T>() -> (result: T)
    requires false,
{
    panic!("unreachable")
}

// Manual helper code for RSL concrete types generation.
//
// This file is intended to be injected by transpiler generate-types via
// `output.manual_code` in `types_transpile.toml`.
//
// IMPORTANT: Contents here live inside an existing `verus! { ... }` block in
// generated output. Do not add `use` statements or a nested `verus!` block.
//
// Helper functions shared with types_i.rs (COperationNumber helpers, CBalLt/Leq/Eq,
// CRequestBatch helpers, CReplyCache helpers, CVotes helpers, CLearnerTuple,
// CLearnerState helpers) are defined in types_i.rs and bulk re-exported via:
//   pub use crate::implementation::RSL::types_i::*;
// in the re_exports section of types_transpile.toml.
//
// CRslIo is generated via [extra_type_aliases] in types_transpile.toml.

// =============================================================================
// CParameters (manual validity/view + static defaults)
// =============================================================================

impl CParameters{
    pub open spec fn valid(self) -> bool
    {
        &&& self.max_integer_val > self.max_log_length > 0
        &&& self.max_integer_val > self.max_batch_delay
        &&& self.max_integer_val < 0x8000_0000_0000_0000
        &&& self.baseline_view_timeout_period > 0
        &&& self.max_integer_val > self.heartbeat_period > 0
        &&& self.max_batch_size > 0
    }

    pub open spec fn view(self) -> LParameters
    {
        LParameters{
            max_log_length: self.max_log_length as int,
            baseline_view_timeout_period: self.baseline_view_timeout_period as int,
            heartbeat_period: self.heartbeat_period as int,
            max_integer_val: UpperBound::UpperBoundFinite{n: self.max_integer_val as int},
            max_batch_size: self.max_batch_size as int,
            max_batch_delay: self.max_batch_delay as int,
        }
    }
}

impl View for CParameters {
    type V = LParameters;

    open spec fn view(&self) -> LParameters {
        LParameters {
            max_log_length: self.max_log_length as int,
            baseline_view_timeout_period: self.baseline_view_timeout_period as int,
            heartbeat_period: self.heartbeat_period as int,
            max_integer_val: UpperBound::UpperBoundFinite{n: self.max_integer_val as int},
            max_batch_size: self.max_batch_size as int,
            max_batch_delay: self.max_batch_delay as int,
        }
    }
}

// Foundational type blocks (`CConfiguration`, `CConstants`, `CReplicaConstants`)
// have been re-homed to implementation/RSL/{cconfiguration,cconstants}.rs.

// Component block A (`CAcceptor`, `CLearner`, `CElectionState`, `COutstandingOperation`)
// has been re-homed to implementation/RSL/{acceptorimpl,learnerimpl,ElectionImpl}.rs.

// =============================================================================
// Component extension section (part 2 extraction)
// =============================================================================

#[derive(Clone)]
pub struct CExecutor {
    pub constants: CReplicaConstants,
    pub app: CAppState,
    pub ops_complete: u64,
    pub max_bal_reflected: CBallot,
    pub next_op_to_execute: COutstandingOperation,
    pub reply_cache: CReplyCache,
}

impl CExecutor {
    pub open spec fn valid(&self) -> bool {
        self.abstractable()
            && self.constants.valid()
            && CAppStateIsValid(&self.app)
            && self.max_bal_reflected.valid()
            && self.next_op_to_execute.valid()
            && creplycache_is_valid(&self.reply_cache)
    }

    pub open spec fn abstractable(&self) -> bool {
        self.constants.abstractable()
            && CAppStateIsAbstractable(&self.app)
            && self.max_bal_reflected.abstractable()
            && self.next_op_to_execute.abstractable()
            && creplycache_is_abstractable(&self.reply_cache)
    }

    pub open spec fn view(&self) -> LExecutor
        recommends
            self.abstractable(){
        let res = LExecutor {
            constants: self.constants.view(),
            app: self.app,
            ops_complete: self.ops_complete as int,
            max_bal_reflected: self.max_bal_reflected.view(),
            next_op_to_execute: self.next_op_to_execute.view(),
            reply_cache: abstractify_creplycache(&self.reply_cache),
        };
        res
    }

    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result: Self)
        ensures
            result@ == self@,
            result.valid() == self.valid(),
    {
        self.clone()
    }
}

impl View for CExecutor {
    type V = LExecutor;

    open spec fn view(&self) -> LExecutor {
        let res = LExecutor {
            constants: self.constants.view(),
            app: self.app,
            ops_complete: self.ops_complete as int,
            max_bal_reflected: self.max_bal_reflected.view(),
            next_op_to_execute: self.next_op_to_execute.view(),
            reply_cache: abstractify_creplycache(&self.reply_cache),
        };
        res
    }
}

// =============================================================================
// CIncompleteBatchTimer (generated enum)
// =============================================================================

#[derive(Clone)]
pub enum CIncompleteBatchTimer {
    CIncompleteBatchTimerOn {
        when: u64,
    },
    CIncompleteBatchTimerOff,
}

impl CIncompleteBatchTimer{
    pub open spec fn abstractable(self) -> bool {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => true,
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => true,
        }
    }

    pub open spec fn valid(self) -> bool {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => self.abstractable(),
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => self.abstractable(),
        }
    }

    pub open spec fn view(self) -> IncompleteBatchTimer
        recommends
        self.abstractable(),
    {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => IncompleteBatchTimer::IncompleteBatchTimerOn {when:when as int},
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => IncompleteBatchTimer::IncompleteBatchTimerOff{},
        }
    }
}

impl View for CIncompleteBatchTimer {
    type V = IncompleteBatchTimer;

    open spec fn view(&self) -> IncompleteBatchTimer {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => IncompleteBatchTimer::IncompleteBatchTimerOn {when:*when as int},
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => IncompleteBatchTimer::IncompleteBatchTimerOff{},
        }
    }
}

// =============================================================================
// CProposer (generated + impl methods)
// =============================================================================

pub struct CProposer {
    pub constants: CReplicaConstants,
    pub current_state: u64,
    pub request_queue: Vec<CRequest>,
    pub max_ballot_i_sent_1a: CBallot,
    pub next_operation_number_to_propose: u64,
    pub received_1b_packets: HashSet<CPacket>,
    pub highest_seqno_requested_by_client_this_view: HashMap<EndPoint, u64>,
    pub incomplete_batch_timer: CIncompleteBatchTimer,
    pub election_state: CElectionState,
    pub max_log_truncation_point: COperationNumber,
    pub max_opn_with_proposal: COperationNumber,
}

// Clone impl for CProposer is in ProposerImpl.rs (needs local helper access)

impl CProposer{
    pub open spec fn abstractable(self) -> bool {
        &&& self.constants.abstractable()
        &&& (forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].abstractable())
        &&& self.max_ballot_i_sent_1a.abstractable()
        &&& (forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.abstractable())
        &&& (forall |k:EndPoint| #[trigger] self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.abstractable())
        &&& self.incomplete_batch_timer.abstractable()
        &&& self.election_state.abstractable()
    }

    pub open spec fn valid(self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        &&& (forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].valid())
        &&& self.max_ballot_i_sent_1a.valid()
        &&& (forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.valid())
        &&& (forall |k:EndPoint| #[trigger] self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.valid_public_key())
        &&& self.incomplete_batch_timer.valid()
        &&& self.election_state.valid()
    }

    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result: Self)
        ensures
            self == result,
            result@ == self@,
            result.valid() == self.valid(),
    {
        self.clone()
    }

    pub open spec fn view(self) -> LProposer
    recommends self.valid(),
    {
        LProposer{
            constants: self.constants.view(),
            current_state: self.current_state as int,
            request_queue: self.request_queue@.map(|i, r:CRequest| r.view()),
            max_ballot_i_sent_1a: self.max_ballot_i_sent_1a.view(),
            next_operation_number_to_propose: self.next_operation_number_to_propose as int,
            received_1b_packets: self.received_1b_packets@.map(|p:CPacket| p.view()),
            highest_seqno_requested_by_client_this_view: Map::new(
                |ak: AbstractEndPoint| exists |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak,
                |ak: AbstractEndPoint| {
                    let k = choose |k: EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak;
                    self.highest_seqno_requested_by_client_this_view@[k] as int
                }
            ),
            incomplete_batch_timer: self.incomplete_batch_timer.view(),
            election_state: self.election_state.view(),
        }
    }
}

impl View for CProposer {
    type V = LProposer;

    open spec fn view(&self) -> LProposer {
        LProposer{
            constants: self.constants.view(),
            current_state: self.current_state as int,
            request_queue: self.request_queue@.map(|i, r:CRequest| r.view()),
            max_ballot_i_sent_1a: self.max_ballot_i_sent_1a.view(),
            next_operation_number_to_propose: self.next_operation_number_to_propose as int,
            received_1b_packets: self.received_1b_packets@.map(|p:CPacket| p.view()),
            highest_seqno_requested_by_client_this_view: Map::new(
                |ak: AbstractEndPoint| exists |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak,
                |ak: AbstractEndPoint| {
                    let k = choose |k: EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak;
                    self.highest_seqno_requested_by_client_this_view@[k] as int
                }
            ),
            incomplete_batch_timer: self.incomplete_batch_timer.view(),
            election_state: self.election_state.view(),
        }
    }
}

// =============================================================================
// CReplica (generated)
// =============================================================================

#[derive(Clone)]
pub struct CReplica {
    pub constants: CReplicaConstants,
    pub nextHeartbeatTime: u64,
    pub proposer: CProposer,
    pub acceptor: CAcceptor,
    pub learner: CLearner,
    pub executor: CExecutor,
}

impl CReplica{
    pub open spec fn valid(self) -> bool {
        self.abstractable()
        &&
        self.constants.valid()
        &&
        self.proposer.valid()
        &&
        self.acceptor.valid()
        &&
        self.learner.valid()
        &&
        self.executor.valid()
        &&
        self.constants@ == self.acceptor.constants@
        &&
        self.constants@ == self.proposer.constants@
        &&
        self.constants@ == self.learner.constants@
        &&
        self.constants@ == self.executor.constants@
    }

    pub open spec fn abstractable(self) -> bool{
        self.constants.abstractable()
        &&
        self.proposer.abstractable()
        &&
        self.acceptor.abstractable()
        &&
        self.learner.abstractable()
        &&
        self.executor.abstractable()
    }

    pub open spec fn view(self) -> LReplica
    recommends
        self.abstractable()
    {
        LReplica{
            constants:self.constants@,
            nextHeartbeatTime:self.nextHeartbeatTime as int,
            proposer:self.proposer@,
            acceptor:self.acceptor@,
            learner:self.learner@,
            executor:self.executor@
        }
    }
}

impl CReplica {
    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result: Self)
        ensures
            self == result,
            result@ == self@,
            result.valid() == self.valid(),
    {
        self.clone()
    }
}

impl View for CReplica {
    type V = LReplica;

    open spec fn view(&self) -> LReplica {
        LReplica{
            constants:self.constants@,
            nextHeartbeatTime:self.nextHeartbeatTime as int,
            proposer:self.proposer@,
            acceptor:self.acceptor@,
            learner:self.learner@,
            executor:self.executor@
        }
    }
}

// =============================================================================
// CScheduler (generated)
// =============================================================================

#[derive(Clone)]
pub struct CScheduler {
    pub replica: CReplica,
    pub nextActionIndex: u64,
}

impl CScheduler {
    pub open spec fn valid(&self) -> bool {
        &&& self.replica.valid()
        &&& 0 <= self.nextActionIndex < 10  // LReplicaNumActions() == 10
    }
}

impl View for CScheduler {
    type V = LScheduler;

    open spec fn view(&self) -> LScheduler {
        LScheduler {
            replica: self.replica@,
            nextActionIndex: self.nextActionIndex as int,
        }
    }
}

// =============================================================================
// Abstractify functions for CRslIo → RslIo conversion
// =============================================================================

/// Convert a concrete LPacket<EndPoint, CMessage> to spec RslPacket
pub open spec fn abstractify_clpacket(p: LPacket<EndPoint, CMessage>) -> RslPacket {
    LPacket {
        dst: p.dst@,
        src: p.src@,
        msg: p.msg.view(),
    }
}

/// Convert a concrete CRslIo to spec RslIo
pub open spec fn abstractify_crslio(io: CRslIo) -> RslIo {
    match io {
        LIoOp::Send{s} => LIoOp::Send{s: abstractify_clpacket(s)},
        LIoOp::Receive{r} => LIoOp::Receive{r: abstractify_clpacket(r)},
        LIoOp::TimeoutReceive => LIoOp::TimeoutReceive,
        LIoOp::ReadClock{t} => LIoOp::ReadClock{t: t},
    }
}

/// Convert a sequence of CRslIo to Seq<RslIo>
pub open spec fn abstractify_crslio_seq(ios: Seq<CRslIo>) -> Seq<RslIo> {
    ios.map(|i, io: CRslIo| abstractify_crslio(io))
}
} // verus!
