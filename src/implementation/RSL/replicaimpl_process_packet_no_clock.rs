use builtin::*;
use builtin_macros::*;
use crate::implementation::common::function::*;
use vstd::prelude::*;
use vstd::slice::*;
use crate::verus_extra::seq_lib_v::*;
use crate::common::native::io_s::*;
use crate::protocol::RSL::environment::*;
use crate::implementation::RSL::{replicaimpl_class::*, cmessage::*, cbroadcast::*, replicaimpl_delivery::*, netrsl_i::*, ReplicaImpl::*};
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus!{

    pub fn replica_next_process_packet_invalid(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket)
    {

    }

    #[verifier(external_body)]
    pub fn replica_next_process_packet_request(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
    {   
        let outpackets = CReplica::CReplicaNextProcessRequest(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    #[verifier(external_body)]
    pub fn replica_next_process_packet_1a(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
    {   
        let outpackets = CReplica::CReplicaNextProcess1a(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    #[verifier(external_body)]
    pub fn replica_next_process_packet_1b(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
    {   
        let outpackets = CReplica::CReplicaNextProcess1b(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    #[verifier(external_body)]
    pub fn replica_next_process_packet_starting_phase2(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
    {   
        let outpackets = CReplica::CReplicaNextProcessStartingPhase2(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    #[verifier(external_body)]
    pub fn replica_next_process_packet_2a(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
    {   
        let outpackets = CReplica::CReplicaNextProcess2a(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    #[verifier(external_body)]
    pub fn replica_next_process_packet_2b(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
    {   
        let outpackets = CReplica::CReplicaNextProcess2b(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    #[verifier(external_body)]
    pub fn replica_next_process_packet_reply(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
    {   
        let outpackets = CReplica::CReplicaNextProcessReply(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    #[verifier(external_body)]
    pub fn replica_next_process_packet_appstate_request(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
    {   
        let outpackets = CReplica::CReplicaNextProcessAppStateRequest(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    #[verifier(external_body)]
    pub fn replica_next_process_packet_appstate_supply(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
    {   
        let outpackets = CReplica::CReplicaNextProcessAppStateSupply(&mut r.replica, pkt);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    #[verifier(external_body)]
    pub fn replica_next_process_packet_without_reading_clock(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
    {
        let mut ok = true;
        match pkt.msg {
            CMessage::CMessageInvalid{} => {
                // ok = true
            }
            CMessage::CMessageRequest{seqno_req, ..} => {
                // println!("receive request");
                ok = replica_next_process_packet_request(r, netc, pkt);
            }
            CMessage::CMessage1a{bal_1a} => {
                println!("receive 1a");
                ok = replica_next_process_packet_1a(r, netc, pkt);
            }
            CMessage::CMessage1b{bal_1b, log_truncation_point, ..} => {
                println!("receive 1b");
                ok = replica_next_process_packet_1b(r, netc, pkt);
            }
            CMessage::CMessageStartingPhase2{bal_2, logTruncationPoint_2} => {
                println!("receive starting phase 2");
                ok = replica_next_process_packet_starting_phase2(r, netc, pkt);
            }
            CMessage::CMessage2a{bal_2a, opn_2a, ..} => {
                // println!("receive 2a");
                ok = replica_next_process_packet_2a(r, netc, pkt);
            }
            CMessage::CMessage2b{bal_2b, opn_2b, ..} => {
                // println!("receive 2b");
                ok = replica_next_process_packet_2b(r, netc, pkt);
            }
            CMessage::CMessageReply{seqno_reply, ..} => {
                ok = replica_next_process_packet_reply(r, netc, pkt);
            }
            CMessage::CMessageAppStateRequest{bal_state_req, opn_state_req} => {
                ok = replica_next_process_packet_appstate_request(r, netc, pkt);
            }
            CMessage::CMessageAppStateSupply{bal_state_supply, opn_state_supply, ..} => {
                ok = replica_next_process_packet_appstate_supply(r, netc, pkt);
            }
            _ => {}
        }
        ok
    }
}