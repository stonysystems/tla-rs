use crate::common::native::io_s::*;
use crate::implementation::RSL::{
    cbroadcast::*, cmessage::*, netrsl_i::*, replicaimpl_class::*, replicaimpl_delivery::*,
    ReplicaImpl::*,
};
use crate::protocol::RSL::environment::*;
use crate::verus_extra::seq_lib_v::*;
use vstd::prelude::*;
use vstd::slice::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus! {

    pub fn replica_next_process_packet_invalid(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket)
    {

    }

    pub fn replica_next_process_packet_request(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
        requires old(r).valid(), pkt.valid(), pkt.msg is CMessageRequest,
    {
        let outpackets = CReplica::CReplicaNextProcessRequestOutbound(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    pub fn replica_next_process_packet_1a(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
        requires old(r).valid(), pkt.valid(), pkt.msg is CMessage1a,
    {
        let outpackets = CReplica::CReplicaNextProcess1aOutbound(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    pub fn replica_next_process_packet_1b(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
        requires old(r).valid(), pkt.valid(), pkt.msg is CMessage1b,
    {
        let outpackets = CReplica::CReplicaNextProcess1bOutbound(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    pub fn replica_next_process_packet_starting_phase2(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
        requires old(r).valid(), pkt.valid(), pkt.msg is CMessageStartingPhase2,
    {
        let outpackets = CReplica::CReplicaNextProcessStartingPhase2Outbound(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    pub fn replica_next_process_packet_2a(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
        requires old(r).valid(), pkt.valid(), pkt.msg is CMessage2a,
    {
        let outpackets = CReplica::CReplicaNextProcess2aOutbound(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    pub fn replica_next_process_packet_2b(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
        requires old(r).valid(), pkt.valid(), pkt.msg is CMessage2b,
    {
        let outpackets = CReplica::CReplicaNextProcess2bOutbound(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    pub fn replica_next_process_packet_reply(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
        requires old(r).valid(), pkt.valid(), pkt.msg is CMessageReply,
    {
        let outpackets = CReplica::CReplicaNextProcessReplyOutbound(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    pub fn replica_next_process_packet_appstate_request(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
        requires old(r).valid(), pkt.valid(), pkt.msg is CMessageAppStateRequest,
    {
        let outpackets = CReplica::CReplicaNextProcessAppStateRequestOutbound(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    pub fn replica_next_process_packet_appstate_supply(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
        requires old(r).valid(), pkt.valid(), pkt.msg is CMessageAppStateSupply,
    {
        let outpackets = CReplica::CReplicaNextProcessAppStateSupplyOutbound(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    pub fn replica_next_process_packet_without_reading_clock(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
        requires old(r).valid(), pkt.valid(),
    {
        let mut ok = true;
        let msg_clone = pkt.msg.clone_up_to_view();
        proof {
            broadcast use axiom_cmessage_view;
            assert(msg_clone == pkt.msg);
        }
        match msg_clone {
            CMessage::CMessageInvalid{} => {
            }
            CMessage::CMessageRequest{..} => {
                ok = replica_next_process_packet_request(r, netc, pkt);
            }
            CMessage::CMessage1a{..} => {
                ok = replica_next_process_packet_1a(r, netc, pkt);
            }
            CMessage::CMessage1b{..} => {
                ok = replica_next_process_packet_1b(r, netc, pkt);
            }
            CMessage::CMessageStartingPhase2{..} => {
                ok = replica_next_process_packet_starting_phase2(r, netc, pkt);
            }
            CMessage::CMessage2a{..} => {
                ok = replica_next_process_packet_2a(r, netc, pkt);
            }
            CMessage::CMessage2b{..} => {
                ok = replica_next_process_packet_2b(r, netc, pkt);
            }
            CMessage::CMessageReply{..} => {
                ok = replica_next_process_packet_reply(r, netc, pkt);
            }
            CMessage::CMessageAppStateRequest{..} => {
                ok = replica_next_process_packet_appstate_request(r, netc, pkt);
            }
            CMessage::CMessageAppStateSupply{..} => {
                ok = replica_next_process_packet_appstate_supply(r, netc, pkt);
            }
            _ => {}
        }
        ok
    }
}
