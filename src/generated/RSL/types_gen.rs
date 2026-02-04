// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::common::collections::hashsets::HashSetWellFormed;
use crate::common::framework::environment_s::LIoOp;
use crate::common::native::io_s::EndPoint;
use crate::implementation::RSL::appinterface::CAppMessage;
use crate::implementation::RSL::cmessage::{CMessage, CPacket};
use crate::implementation::RSL::ReplicaImpl::CReplica;
use crate::protocol::RSL::environment::RslIo;
use crate::protocol::RSL::replica::LScheduler;
use crate::protocol::RSL::types::*;
use std::collections::{HashMap, HashSet};
use vstd::prelude::*;

verus! {

// =============================================================================
// Type Aliases
// =============================================================================

/// Concrete operation number type (maps to spec's OperationNumber = int)
pub type COperationNumber = u64;

/// Concrete request batch type (maps to spec's RequestBatch = Seq<Request>)
pub type CRequestBatch = Vec<CRequest>;

/// Concrete reply cache type (maps to spec's ReplyCache = Map<AbstractEndPoint, Reply>)
pub type CReplyCache = HashMap<EndPoint, CReply>;

/// Concrete votes type (maps to spec's Votes = Map<OperationNumber, Vote>)
pub type CVotes = HashMap<COperationNumber, CVote>;

/// Concrete learner state type (maps to spec's LearnerState = Map<OperationNumber, LearnerTuple>)
pub type CLearnerState = HashMap<COperationNumber, CLearnerTuple>;

/// Concrete RSL I/O type (maps to spec's RslIo = LIoOp<AbstractEndPoint, RslMessage>)
pub type CRslIo = LIoOp<EndPoint, CMessage>;

// =============================================================================
// Ballot Comparison Functions
// =============================================================================

/// Concrete ballot less-than comparison
pub fn CBalLt(ba: &CBallot, bb: &CBallot) -> (r: bool)
    requires
        ba.well_formed(),
        bb.well_formed(),
    ensures
        r == BalLt(ba@, bb@),
{
    ba.seqno < bb.seqno
        || (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)
}

/// Concrete ballot less-than-or-equal comparison
pub fn CBalLeq(ba: &CBallot, bb: &CBallot) -> (r: bool)
    requires
        ba.well_formed(),
        bb.well_formed(),
    ensures
        r == BalLeq(ba@, bb@),
{
    ba.seqno < bb.seqno
        || (ba.seqno == bb.seqno && ba.proposer_id <= bb.proposer_id)
}

// =============================================================================
// CScheduler Struct
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
// Trait Implementations for Type Aliases
// =============================================================================

/// Trait for well-formedness of CRequestBatch
pub trait CRequestBatchWellFormed {
    spec fn well_formed(&self) -> bool;
}

impl CRequestBatchWellFormed for CRequestBatch {
    open spec fn well_formed(&self) -> bool {
        forall|i: int| 0 <= i < self@.len() ==> (#[trigger] self@[i]).well_formed()
    }
}

/// Trait for valid check on CReplyCache
pub trait CReplyCacheValid {
    spec fn valid(&self) -> bool;
}

impl CReplyCacheValid for CReplyCache {
    open spec fn valid(&self) -> bool {
        forall|k: EndPoint| self@.contains_key(k) ==> (#[trigger] self@[k]).well_formed()
    }
}

/// Trait for valid check on CVotes
pub trait CVotesValid {
    spec fn valid(&self) -> bool;
}

impl CVotesValid for CVotes {
    open spec fn valid(&self) -> bool {
        forall|k: COperationNumber| self@.contains_key(k) ==> (#[trigger] self@[k]).well_formed()
    }
}

/// Trait for valid check on CLearnerState
pub trait CLearnerStateValid {
    spec fn valid(&self) -> bool;
}

impl CLearnerStateValid for CLearnerState {
    open spec fn valid(&self) -> bool {
        forall|k: COperationNumber| self@.contains_key(k) ==> (#[trigger] self@[k]).well_formed()
    }
}

// =============================================================================
// Core Data Structures
// =============================================================================

#[derive(Clone)]
pub struct CRequest {
    pub client: EndPoint,
    pub seqno: i64,
    pub request: CAppMessage,
}

impl CRequest {
    pub open spec fn well_formed(&self) -> bool {
        &&& self.client.well_formed()
        &&& self.request.well_formed()
    }
}

impl View for CRequest {
    type V = Request;

    open spec fn view(&self) -> Request {
        Request {
            client: self.client@,
            seqno: self.seqno as int,
            request: self.request@,
        }
    }
}

#[derive(Clone)]
pub struct CBallot {
    pub seqno: i64,
    pub proposer_id: i64,
}

impl CBallot {
    pub open spec fn well_formed(&self) -> bool {
        true
    }

    /// Alias for well_formed() for compatibility with generated code
    pub open spec fn valid(&self) -> bool {
        self.well_formed()
    }
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

#[derive(Clone)]
pub struct CClockReading {
    pub t: i64,
}

impl CClockReading {
    pub open spec fn well_formed(&self) -> bool {
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

#[derive(Clone)]
pub struct CReply {
    pub client: EndPoint,
    pub seqno: i64,
    pub reply: CAppMessage,
}

impl CReply {
    pub open spec fn well_formed(&self) -> bool {
        &&& self.client.well_formed()
        &&& self.reply.well_formed()
    }
}

impl View for CReply {
    type V = Reply;

    open spec fn view(&self) -> Reply {
        Reply {
            client: self.client@,
            seqno: self.seqno as int,
            reply: self.reply@,
        }
    }
}

#[derive(Clone)]
pub struct CVote {
    pub max_value_bal: CBallot,
    pub max_val: CRequestBatch,
}

impl CVote {
    pub open spec fn well_formed(&self) -> bool {
        &&& self.max_value_bal.well_formed()
        &&& self.max_val.well_formed()
    }
}

impl View for CVote {
    type V = Vote;

    open spec fn view(&self) -> Vote {
        Vote {
            max_value_bal: self.max_value_bal@,
            max_val: self.max_val@,
        }
    }
}

#[derive(Clone)]
pub struct CLearnerTuple {
    pub received_2b_message_senders: HashSet<EndPoint>,
    pub candidate_learned_value: CRequestBatch,
}

impl CLearnerTuple {
    pub open spec fn well_formed(&self) -> bool {
        &&& self.candidate_learned_value.well_formed()
    }
}

impl View for CLearnerTuple {
    type V = LearnerTuple;

    open spec fn view(&self) -> LearnerTuple {
        LearnerTuple {
            received_2b_message_senders: self.received_2b_message_senders@,
            candidate_learned_value: self.candidate_learned_value@,
        }
    }
}

} // verus!
