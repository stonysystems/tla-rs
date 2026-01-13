use builtin::*;
use builtin_macros::*;
use crate::implementation::common::function::*;
use vstd::prelude::*;
use vstd::slice::*;
use crate::verus_extra::seq_lib_v::*;
use crate::common::native::io_s::*;
use crate::protocol::RSL::environment::*;
use crate::implementation::RSL::{replicaimpl_class::*, cmessage::*, cbroadcast::*, netrsl_i::*};
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus!{
    pub fn deliver_packet(r: &mut ReplicaImpl, netc:&mut NetClient, packet:&Option<CPacket>) -> (ok:bool)
    {
        let mut ok:bool = true;
        match packet {
            Some(packet) => {
                let (is_ok, net_event) = send_packet(packet, netc);
                ok = is_ok;
            }
            None => {

            }
        }
        if !ok {
            // print
        } 
        ok
    }

    pub fn deliver_packet_sequence(r: &mut ReplicaImpl, netc:&mut NetClient, packets:&Vec<CPacket>) -> (ok:bool)
    {
        let mut ok = true;
        let (is_ok, net_event) = send_packet_seq(packets, netc);

        if !ok {
            // print
        } 
        ok
    }

    pub fn deliver_broadcast(r: &mut ReplicaImpl, netc:&mut NetClient, broadcast:&CBroadcast) -> (ok:bool)
    {
        let mut ok = true;
        let (is_ok, net_event) = send_broadcast(broadcast, netc);

        if !ok {
            // print
        } 
        ok
    }

    pub fn deliver_outbound_packets(r: &mut ReplicaImpl, netc:&mut NetClient, outpackets:&OutboundPackets) -> (ok:bool)
    {
        match outpackets {
            OutboundPackets::OutboundPacket{p} => {
                deliver_packet(r, netc, p)
            }
            OutboundPackets::PacketSequence{s} => {
                deliver_packet_sequence(r, netc, s)
            }
            OutboundPackets::Broadcast{broadcast} => {
                deliver_broadcast(r, netc, broadcast)
            }
        }
    }
}