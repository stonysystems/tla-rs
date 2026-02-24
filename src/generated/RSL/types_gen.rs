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
use crate::protocol::RSL::replica::LScheduler;
use crate::protocol::RSL::replica::*;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
use std::collections::{HashMap, HashSet};
use vstd::prelude::*;
use vstd::seq::*;
use vstd::{map::*, modes::*, seq_lib::*};
use vstd::{set::*, set_lib::*};

pub use crate::implementation::common::upper_bound::*;
pub use crate::implementation::common::upper_bound_i::*;
pub use crate::implementation::RSL::acceptorimpl::CAcceptor;
pub use crate::implementation::RSL::appinterface::{CAppMessage, CAppState, CAppStateInit};
pub use crate::implementation::RSL::cbroadcast::*;
pub use crate::implementation::RSL::cconfiguration::{CConfiguration, ReplicaIndexValid};
pub use crate::implementation::RSL::cconstants::{CConstants, CReplicaConstants};
pub use crate::implementation::RSL::cmessage::*;
pub use crate::implementation::RSL::learnerimpl::CLearner;
pub use crate::implementation::RSL::types_i::*;
pub use crate::implementation::RSL::CStateMachine::*;
pub use crate::implementation::RSL::ElectionImpl::{
    CElectionState, COutstandingOperation, CRequestHeader,
};
pub use crate::implementation::RSL::ExecutorImpl::{CExecutor, CIncompleteBatchTimer};
pub use crate::implementation::RSL::ProposerImpl::CProposer;
pub use crate::implementation::RSL::ReplicaImpl::{
    abstractify_clpacket, abstractify_crslio, abstractify_crslio_seq, CReplica, CScheduler,
};

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
} // verus!
