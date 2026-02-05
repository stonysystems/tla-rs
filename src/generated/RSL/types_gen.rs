// Types for generated RSL modules
//
// Re-exports all implementation types so generated function files only need:
//   use crate::generated::RSL::types_gen::*;
// Types unique to this module: CScheduler, CClockReading, CRslIo,
// abstractify_clpacket/crslio functions, unreachable_value helper.

// =============================================================================
// Re-exports from implementation modules
// =============================================================================

// Core types and type aliases (CBallot, CRequest, CReply, CVote, CLearnerTuple, etc.)
pub use crate::implementation::RSL::types_i::*;
// Message types (CMessage, CPacket)
pub use crate::implementation::RSL::cmessage::*;
// Configuration, Constants, Parameters
pub use crate::implementation::RSL::cconfiguration::*;
pub use crate::implementation::RSL::cconstants::*;
pub use crate::implementation::RSL::cparameters::*;
// Component state types
pub use crate::implementation::RSL::acceptorimpl::{CAcceptor, CIsLogTruncationPointValid};
pub use crate::implementation::RSL::learnerimpl::CLearner;
pub use crate::implementation::RSL::ElectionImpl::CElectionState;
pub use crate::implementation::RSL::ExecutorImpl::{CExecutor, COutstandingOperation};
pub use crate::implementation::RSL::ProposerImpl::{CIncompleteBatchTimer, CProposer};
pub use crate::implementation::RSL::ReplicaImpl::CReplica;
// Application interface
pub use crate::implementation::RSL::appinterface::{CAppMessage, CAppState, CAppStateInit};
// State machine
pub use crate::implementation::RSL::CStateMachine::*;
// Broadcast helpers
pub use crate::implementation::RSL::cbroadcast::*;
// Upper bound helpers
pub use crate::implementation::common::upper_bound::*;
pub use crate::implementation::common::upper_bound_i::*;

// =============================================================================
// Imports for types defined in this module
// =============================================================================

use crate::common::framework::environment_s::{LIoOp, LPacket};
use crate::common::native::io_s::EndPoint;
use crate::protocol::RSL::environment::{RslIo, RslPacket};
use crate::protocol::RSL::replica::LScheduler;
use crate::protocol::RSL::types::*;
use vstd::prelude::*;
use vstd::seq::*;

verus! {

// =============================================================================
// Type Aliases (unique to generated module)
// =============================================================================

/// Concrete RSL I/O type (maps to spec's RslIo = LIoOp<AbstractEndPoint, RslMessage>)
pub type CRslIo = LIoOp<crate::common::native::io_s::EndPoint, CMessage>;

// =============================================================================
// CScheduler Struct (generated-only, not in implementation)
// =============================================================================

/// Concrete scheduler struct (maps to spec's LScheduler)
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
// CClockReading Struct (generated-only, not in implementation)
// =============================================================================

/// Concrete clock reading struct (maps to spec's ClockReading)
#[derive(Clone)]
pub struct CClockReading {
    pub t: u64,
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

/// Helper for match arms that are provably unreachable.
/// The requires clause is `false`, so Verus verifies this can never be called.
#[verifier(external_body)]
pub fn unreachable_value<T>() -> (result: T)
    requires false,
{
    panic!("unreachable")
}

} // verus!
