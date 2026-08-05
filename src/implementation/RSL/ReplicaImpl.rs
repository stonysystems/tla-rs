use crate::common::collections::count_matches::*;
use crate::common::collections::vecs::*;
use crate::common::framework::environment_s::{LIoOp, LPacket};
use crate::common::native::io_s::EndPoint;
use crate::generated::RSL::types_gen::CRslIo;
use crate::implementation::common::upper_bound::*;
use crate::implementation::common::upper_bound_i::*;
use crate::implementation::RSL::acceptorimpl::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::learnerimpl::*;
use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::ElectionImpl::COutstandingOperation;
use crate::implementation::RSL::ExecutorImpl::*;
use crate::implementation::RSL::ProposerImpl::*;
use crate::implementation::RSL::{cconfiguration::*, ProposerImpl::*};
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::{
    acceptor::*, configuration::*, constants::*, executor::*, learner::*, message::*, proposer::*,
    types::*,
};
use crate::protocol::RSL::{environment::*, replica::*};
use std::collections::*;
use vstd::prelude::*;
use vstd::std_specs::hash::*;
use vstd::{map::*, map_lib::*, prelude::*, seq::*};

verus! {
    broadcast use crate::common::native::io_s::axiom_endpoint_key_model;

pub struct CReplica {
    pub constants: CReplicaConstants,
    pub nextHeartbeatTime: u64,
    pub proposer: CProposer,
    pub acceptor: CAcceptor,
    pub learner: CLearner,
    pub executor: CExecutor,
}

// Verus cannot attach a specification to a derived Clone for a type whose
// clone is not a copy, so `#[derive(Clone)]` left `.clone()` opaque to every
// proof. Delegating to the spec'd `clone_up_to_view` gives the same postcondition
// without adding any trusted code.
impl Clone for CReplica {
    fn clone(&self) -> (result: Self)
    ensures
        result@ == self@,
        result.valid() == self.valid(),
    {
        self.clone_up_to_view()
    }
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
    pub fn clone_up_to_view(&self) -> (result: Self)
        ensures
            result@ == self@,
            result.valid() == self.valid(),
    {
        let constants = self.constants.clone();
        let proposer = self.proposer.clone_up_to_view();
        let acceptor = self.acceptor.clone_up_to_view();
        let learner = self.learner.clone_up_to_view();
        let executor = self.executor.clone_up_to_view();

        CReplica {
            constants,
            nextHeartbeatTime: self.nextHeartbeatTime,
            proposer,
            acceptor,
            learner,
            executor,
        }
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

pub struct CScheduler {
    pub replica: CReplica,
    pub nextActionIndex: u64,
}

impl Clone for CScheduler {
    fn clone(&self) -> (result: Self)
    ensures
        result@ == self@,
        result.valid() == self.valid(),
    {
        self.clone_up_to_view()
    }
}

impl CScheduler {
    pub fn clone_up_to_view(&self) -> (result: Self)
    ensures
        result@ == self@,
        result.valid() == self.valid(),
    {
        CScheduler {
            replica: self.replica.clone(),
            nextActionIndex: self.nextActionIndex,
        }
    }

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

impl CReplica {

    pub fn CReplicaInit(c: CReplicaConstants) -> (result: Self)
        requires c.valid()
        ensures result.valid(), result.constants@ == c@, LReplicaInit(result@, c@)
    {
        crate::generated::RSL::replica_gen::CReplicaInit(&c)
    }

    pub fn Packet1bHasUniqueSrc(s:&HashSet<CPacket>, pkt:&CPacket) -> (res:bool)
        requires pkt.msg is CMessage1b,
        ensures res == (forall |op:CPacket| #![trigger s@.contains(op)] s@.contains(op) ==> op.src@ != pkt.src@)
    {
        crate::implementation::RSL::gen_helpers::Packet1bHasUniqueSrc(s, pkt)
    }

    #[verifier::external_body]
    pub fn print(s: &str) {
        println!("{}", s);
    }

    #[verifier::external_body]
    pub fn CReplicaNextProcessInvalid(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
        requires old(self).valid(), received_packet.valid(), received_packet.msg is CMessageInvalid,
        ensures self.valid(), res.valid(),
            LReplicaNextProcessInvalid(old(self)@, self@, received_packet@, res@)
    {
        let _ = crate::generated::RSL::replica_gen::CReplicaNextProcessInvalid(self, &received_packet);
        OutboundPackets::PacketSequence { s: vec![] }
    }

    #[verifier::external_body]
    pub fn CReplicaNextProcessRequest(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
        requires old(self).valid(), received_packet.valid(), received_packet.msg is CMessageRequest,
        ensures self.valid(), res.valid(),
            Replica_Common_Postconditions(old(self)@, *self, received_packet, res),
            LReplicaNextProcessRequest(old(self)@, self@, received_packet@, res@)
    {
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextProcessRequest(self, &received_packet);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextProcess1a(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
        requires old(self).valid(), received_packet.valid(), received_packet.msg is CMessage1a,
        ensures self.valid(), res.valid(),
            Replica_Common_Postconditions(old(self)@, *self, received_packet, res),
            LReplicaNextProcess1a(old(self)@, self@, received_packet@, res@)
    {
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextProcess1a(self, &received_packet);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextProcess1b(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
        requires old(self).valid(), received_packet.valid(), received_packet.msg is CMessage1b,
        ensures self.valid(), res.valid(),
            Replica_Common_Postconditions(old(self)@, *self, received_packet, res),
            LReplicaNextProcess1b(old(self)@, self@, received_packet@, res@)
    {
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextProcess1b(self, &received_packet);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextProcessStartingPhase2(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
        requires old(self).valid(), received_packet.valid(), received_packet.msg is CMessageStartingPhase2,
        ensures self.valid(), res.valid(),
            Replica_Common_Postconditions(old(self)@, *self, received_packet, res),
            LReplicaNextProcessStartingPhase2(old(self)@, self@, received_packet@, res@)
    {
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextProcessStartingPhase2(self, &received_packet);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextProcess2a(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
        requires old(self).valid(), received_packet.valid(), received_packet.msg is CMessage2a,
        ensures self.valid(), res.valid(),
            Replica_Common_Postconditions(old(self)@, *self, received_packet, res),
            LReplicaNextProcess2a(old(self)@, self@, received_packet@, res@)
    {
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextProcess2a(self, &received_packet);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextProcess2b(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
        requires old(self).valid(), received_packet.valid(), received_packet.msg is CMessage2b,
        ensures self.valid(), res.valid(),
            Replica_Common_Postconditions(old(self)@, *self, received_packet, res),
            LReplicaNextProcess2b(old(self)@, self@, received_packet@, res@)
    {
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextProcess2b(self, &received_packet);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextProcessReply(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
        requires old(self).valid(), received_packet.valid(), received_packet.msg is CMessageReply,
        ensures self.valid(), res.valid(),
            LReplicaNextProcessReply(old(self)@, self@, received_packet@, res@)
    {
        let _ = crate::generated::RSL::replica_gen::CReplicaNextProcessReply(self, &received_packet);
        OutboundPackets::PacketSequence { s: vec![] }
    }

    #[verifier::external_body]
    pub fn CReplicaNextProcessAppStateSupply(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
        requires old(self).valid(), received_packet.valid(), received_packet.msg is CMessageAppStateSupply,
        ensures self.valid(), res.valid(),
            Replica_Common_Postconditions(old(self)@, *self, received_packet, res),
            LReplicaNextProcessAppStateSupply(old(self)@, self@, received_packet@, res@)
    {
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextProcessAppStateSupply(self, &received_packet);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextProcessAppStateRequest(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
        requires old(self).valid(), received_packet.valid(), received_packet.msg is CMessageAppStateRequest,
        ensures self.valid(), res.valid(),
            Replica_Common_Postconditions(old(self)@, *self, received_packet, res),
            LReplicaNextProcessAppStateRequest(old(self)@, self@, received_packet@, res@)
    {
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextProcessAppStateRequest(self, &received_packet);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextProcessHeartbeat(&mut self, received_packet: CPacket, clock: u64) -> (res: OutboundPackets)
        requires old(self).valid(), received_packet.valid(), received_packet.msg is CMessageHeartbeat,
        ensures self.valid(), res.valid(),
            Replica_Common_Postconditions(old(self)@, *self, received_packet, res),
            LReplicaNextProcessHeartbeat(old(self)@, self@, received_packet@, clock as int, res@)
    {
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextProcessHeartbeat(self, &received_packet, &clock);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(&mut self) -> (res: OutboundPackets)
        requires old(self).valid(),
        ensures self.valid(), res.valid(),
            Replica_Common_Postconditions_NoPacket(old(self)@, *self, res),
            LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(old(self)@, self@, res@)
    {
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(self);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextSpontaneousMaybeEnterPhase2(&mut self) -> (res: OutboundPackets)
        requires old(self).valid(),
        ensures self.valid(), res.valid(),
            Replica_Common_Postconditions_NoPacket(old(self)@, *self, res),
            LReplicaNextSpontaneousMaybeEnterPhase2(old(self)@, self@, res@)
    {
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextSpontaneousMaybeEnterPhase2(self);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextSpontaneousMaybeMakeDecision(&mut self) -> (res: OutboundPackets)
        requires old(self).valid(),
        ensures self.valid(), res.valid(),
            Replica_Common_Postconditions_NoPacket(old(self)@, *self, res),
            LReplicaNextSpontaneousMaybeMakeDecision(old(self)@, self@, res@)
    {
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextSpontaneousMaybeMakeDecision(self);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextSpontaneousMaybeExecute(&mut self) -> (res: OutboundPackets)
        requires old(self).valid(),
        ensures self.valid(), res.valid(),
            Replica_Common_Postconditions_NoPacket(old(self)@, *self, res),
            LReplicaNextSpontaneousMaybeExecute(old(self)@, self@, res@)
    {
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextSpontaneousMaybeExecute(self);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextReadClockMaybeSendHeartbeat(&mut self, clock: u64) -> (res: OutboundPackets)
        requires old(self).valid(),
        ensures self.valid(), res.valid(),
            LReplicaNextReadClockMaybeSendHeartbeat(old(self)@, self@, ClockReading{t: clock as int}, res@)
    {
        use crate::generated::RSL::types_gen::CClockReading;
        let c = CClockReading { t: clock };
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextReadClockMaybeSendHeartbeat(self, &c);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextReadClockCheckForViewTimeout(&mut self, clock: u64) -> (res: OutboundPackets)
        requires old(self).valid(),
        ensures self.valid(), res.valid(),
            LReplicaNextReadClockCheckForViewTimeout(old(self)@, self@, ClockReading{t: clock as int}, res@)
    {
        use crate::generated::RSL::types_gen::CClockReading;
        let c = CClockReading { t: clock };
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextReadClockCheckForViewTimeout(self, &c);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextReadClockCheckForQuorumOfViewSuspicions(&mut self, clock: u64) -> (res: OutboundPackets)
        requires old(self).valid(),
        ensures self.valid(), res.valid(),
            LReplicaNextReadClockCheckForQuorumOfViewSuspicions(old(self)@, self@, ClockReading{t: clock as int}, res@)
    {
        use crate::generated::RSL::types_gen::CClockReading;
        let c = CClockReading { t: clock };
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextReadClockCheckForQuorumOfViewSuspicions(self, &c);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(&mut self) -> (res: OutboundPackets)
        requires old(self).valid(),
        ensures self.valid(), res.valid(),
            Replica_Common_Postconditions_NoPacket(old(self)@, *self, res),
            LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(old(self)@, self@, res@)
    {
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(self);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

    #[verifier::external_body]
    pub fn CReplicaNextReadClockMaybeNominateValueAndSend2a(&mut self, clock: u64) -> (res: OutboundPackets)
        requires old(self).valid(),
        ensures self.valid(), res.valid(),
            LReplicaNextReadClockMaybeNominateValueAndSend2a(old(self)@, self@, ClockReading{t: clock as int}, res@)
    {
        use crate::generated::RSL::types_gen::CClockReading;
        let c = CClockReading { t: clock };
        let sent_packets = crate::generated::RSL::replica_gen::CReplicaNextReadClockMaybeNominateValueAndSend2a(self, &c);
        OutboundPackets::PacketSequence { s: sent_packets }
    }

} // end Phase 48.6.b &mut self impl

pub open spec fn ConstantsStayConstant_Replica(replica: LReplica, replica_: CReplica) -> bool
    recommends
        replica_.constants.abstractable()
    {
        replica_.constants@ == replica.constants
        && replica.constants == replica.proposer.constants
        && replica.constants == replica.acceptor.constants
        && replica.constants == replica.learner.constants
        && replica.constants == replica.executor.constants
        && replica_.constants@ == replica_.proposer.constants@
        && replica_.constants@ == replica_.acceptor.constants@
        && replica_.constants@ == replica_.learner.constants@
        && replica_.constants@ == replica_.executor.constants@

    }

// Pre-Conditions


pub open spec fn Replica_Common_Preconditions(replica:CReplica, inp:CPacket) ->bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_Process_Heartbeat_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessageHeartbeat
    && replica.valid()
    && inp.valid()
  }

  pub open spec fn Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_MaybeEnterPhase2_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_Process_Request_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessageRequest
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_1a_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessage1a
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_1b_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessage1b
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_StartingPhase2_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessageStartingPhase2
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_2a_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessage2a
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_2b_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessage2b
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_AppStateRequest_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessageAppStateRequest
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_AppStateSupply_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {

    inp.msg is CMessageAppStateSupply
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

// // Post-Conditions predicates

pub open spec fn CReplicaConstantsIsValid(s:CReplicaConstants) -> bool
{
    s.abstractable()
    && s.valid()
    && 0 <= s.my_index < s.all.config.replica_ids.len()
}

pub open spec fn Replica_Common_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    CReplicaConstantsIsValid(replica_.constants)
    // CPacketIsSendable(inp) has to be implemented in packetparsing.rs
    && replica_.abstractable()
    && ConstantsStayConstant_Replica(replica, replica_)
    && replica_.valid()
    && packets_sent.valid()
    // && packets_sent.OutboundPacketsHasCorrectSrc(replica_.constants.all.config.replica_ids[replica_.constants.my_index as int])
    && packets_sent.abstractable()
}

pub open spec fn Replica_Common_Postconditions_NoPacket(replica: LReplica, replica_: CReplica, packets_sent: OutboundPackets) -> bool {
    replica_.constants.valid()
    // CPacketIsSendable(inp) has to be implemented in packetparsing.rs
    && replica_.abstractable()
    && ConstantsStayConstant_Replica(replica, replica_)
    && replica_.valid()
    && packets_sent.valid()
    // && packets_sent.OutboundPacketsHasCorrectSrc(replica_.constants.all.config.replica_ids[replica_.constants.my_index as int])
    && packets_sent.abstractable()
}

pub open spec fn Replica_Next_Process_AppStateSupply_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageAppStateSupply
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessAppStateSupply(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_AppStateRequest_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageAppStateRequest
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessAppStateRequest(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_2b_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessage2b
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcess2b(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_2a_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessage2a
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcess2a(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_StartingPhase2_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageStartingPhase2
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessStartingPhase2(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_1b_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessage1b
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcess1b(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_1a_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessage1a
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcess1a(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_Request_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageRequest
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessRequest(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_Heartbeat_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, clock: u64, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageHeartbeat
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessHeartbeat(
        replica,
        replica_@,
        inp.view(),
        clock as int,
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextReadClockMaybeNominateValueAndSend2a(replica,
         replica_@,
        clock,
        packets_sent@)
}

pub open spec fn Replica_Next_ReadClock_CheckForViewTimeout_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextReadClockCheckForViewTimeout(replica,
         replica_@,
        clock,
        packets_sent@)
}

pub open spec fn Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(replica,
         replica_@,
        clock,
        packets_sent@)
}

pub open spec fn Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextReadClockMaybeSendHeartbeat(replica,
         replica_@,
        clock,
        packets_sent@)
}

pub open spec fn Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(replica: LReplica, replica_: CReplica, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(replica,
         replica_@,
        packets_sent@)
}

pub open spec fn Replica_Next_MaybeEnterPhase2_Postconditions(replica: LReplica, replica_: CReplica, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousMaybeEnterPhase2(replica,
         replica_@,
        packets_sent@)
}

pub open spec fn Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(replica,
         replica_@,
        packets_sent@)
}

pub open spec fn Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousMaybeMakeDecision(replica,
         replica_@,
        packets_sent@)
}

pub open spec fn Replica_Next_Spontaneous_MaybeExecute_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousMaybeExecute(replica,
         replica_@,
        packets_sent@)
}

} // verus!
