use builtin::*;
use builtin_macros::*;
use crate::implementation::common::function::*;
use vstd::prelude::*;
use vstd::slice::*;
use crate::verus_extra::seq_lib_v::*;
use crate::common::native::io_s::*;
use crate::protocol::RSL::environment::*;
use crate::implementation::RSL::{
    replicaimpl_class::*, 
    cmessage::*, cbroadcast::*, 
    replicaimpl_delivery::*, 
    netrsl_i::*, 
    ReplicaImpl::*,
    replicaimpl_read_clock::*,
    replicaimpl_process_packet_no_clock::*,
};
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus!{
    pub fn replica_next_process_packet_timeout(r:&mut ReplicaImpl)
    {

    }

    #[verifier::external_body]
    pub fn replica_next_process_packet_heartbeat(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
    {
        let mut ok:bool = true;
        ok = replica_next_read_clock_and_process_packet(r, netc, pkt);
        ok
    }

    #[verifier::external_body]
    pub fn replica_next_process_packet_non_heartbeat(r:&mut ReplicaImpl, netc:&mut NetClient, pkt:CPacket) -> (ok:bool)
    {
        let mut ok:bool = true;
        ok = replica_next_process_packet_without_reading_clock(r, netc, pkt);
        ok
    }

    #[verifier::external_body]
    pub fn replica_next_process_packet_x(r:&mut ReplicaImpl, netc:&mut NetClient) -> (res:(bool, Ghost<Seq<NetEvent>>, Ghost<Seq<RslIo>>))
        requires
            old(r).valid(),
    {
        let mut ok:bool = false;
        let ghost mut net_event = Seq::<NetEvent>::empty();
        let ghost mut ios_his = Seq::<RslIo>::empty();
        let (rr, received_event) = receive_packet(netc, &r.localAddr);

        match rr {
            ReceiveResult::Fail{} => {

            }
            ReceiveResult::Timeout{} => {
                ok = true;
                // replica_next_process_packet_timeout()
                // net_event = event_log;
                // ios_his = ios;
            }
            ReceiveResult::Packet{cpacket} => {
                match cpacket.msg {
                    CMessage::CMessageHeartbeat{bal_heartbeat, suspicious, opn_ckpt} => {
                        // println!("receive heartbeat");
                        // let (is_ok, event_log, ios) = 
                        ok = replica_next_process_packet_heartbeat(r, netc, cpacket);
                        // net_event = event_log;
                        // ios_his = ios;
                    }
                    _ => {
                        // let (is_ok, event_log, ios) = 
                        // ok = is_ok;
                        // net_event = event_log;
                        // ios_his = ios;
                        ok = replica_next_process_packet_non_heartbeat(r, netc, cpacket);
                    }
                }
            }
        }
        (ok, Ghost(net_event), Ghost(ios_his))
    }
}