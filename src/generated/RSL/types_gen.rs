// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use vstd::prelude::*;
use std::collections::HashSet;
use crate::common::collections::hashsets::HashSetWellFormed;
use crate::common::framework::environment_s::LIoOp;
use crate::common::native::io_s::EndPoint;
use crate::implementation::RSL::appinterface::CAppMessage;
use crate::implementation::RSL::cmessage::CPacket;
use crate::implementation::RSL::types_i::CRequestBatch;
use crate::implementation::RSL::ReplicaImpl::CReplica;
use crate::protocol::RSL::environment::RslIo;
use crate::protocol::RSL::replica::LScheduler;
use crate::protocol::RSL::types::*;

verus! {

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
pub struct CLearnerTuple {
    pub received_2b_message_senders: HashSet<EndPoint>,
    pub candidate_learned_value: CRequestBatch,
}

impl CLearnerTuple {
    pub open spec fn well_formed(&self) -> bool {
        &&& self.received_2b_message_senders.well_formed()
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

/// Concrete IO operation type for RSL protocol
/// Maps to spec type: RslIo = LIoOp<AbstractEndPoint, RslMessage>
#[derive(Clone)]
pub enum CRslIo {
    CSend { s: CPacket },
    CReceive { r: CPacket },
    CTimeoutReceive,
    CReadClock { t: i64 },
}

impl CRslIo {
    pub open spec fn well_formed(&self) -> bool {
        match self {
            CRslIo::CSend { s } => s.valid(),
            CRslIo::CReceive { r } => r.valid(),
            CRslIo::CTimeoutReceive => true,
            CRslIo::CReadClock { t } => true,
        }
    }

    pub open spec fn valid(&self) -> bool {
        self.well_formed()
    }

    /// Get the received packet (for CReceive variant)
    pub fn get_r(&self) -> (result: &CPacket)
        requires self is CReceive
        ensures result.valid()
    {
        match self {
            CRslIo::CReceive { r } => r,
            _ => unreachable!(),
        }
    }

    /// Get the send packet (for CSend variant)
    pub fn get_s(&self) -> (result: &CPacket)
        requires self is CSend
        ensures result.valid()
    {
        match self {
            CRslIo::CSend { s } => s,
            _ => unreachable!(),
        }
    }

    /// Get the clock time (for CReadClock variant)
    pub fn get_t(&self) -> (result: i64)
        requires self is CReadClock
    {
        match self {
            CRslIo::CReadClock { t } => *t,
            _ => unreachable!(),
        }
    }
}

impl View for CRslIo {
    type V = RslIo;

    open spec fn view(&self) -> RslIo {
        match self {
            CRslIo::CSend { s } => LIoOp::Send { s: s@ },
            CRslIo::CReceive { r } => LIoOp::Receive { r: r@ },
            CRslIo::CTimeoutReceive => LIoOp::TimeoutReceive,
            CRslIo::CReadClock { t } => LIoOp::ReadClock { t: *t as int },
        }
    }
}

/// Concrete scheduler type for RSL protocol
/// Maps to spec type: LScheduler
#[derive(Clone)]
pub struct CScheduler {
    pub replica: CReplica,
    pub nextActionIndex: i64,
}

impl CScheduler {
    pub open spec fn well_formed(&self) -> bool {
        &&& self.replica.valid()
    }

    pub open spec fn valid(&self) -> bool {
        self.well_formed()
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

} // verus!
