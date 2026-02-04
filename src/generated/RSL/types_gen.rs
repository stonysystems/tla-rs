// Types for generated RSL modules
//
// Re-exports types from the implementation module (types_i.rs) to avoid
// duplicate type definitions. Only types unique to the generated module
// (CScheduler, CClockReading, CRslIo) are defined here.

// Re-export all implementation types used by generated code
pub use crate::implementation::RSL::types_i::*;

use crate::common::framework::environment_s::LIoOp;
use crate::implementation::RSL::cmessage::CMessage;
use crate::implementation::RSL::ReplicaImpl::CReplica;
use crate::protocol::RSL::replica::LScheduler;
use crate::protocol::RSL::types::*;
use vstd::prelude::*;

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
    pub nextActionIndex: i64,
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

} // verus!
