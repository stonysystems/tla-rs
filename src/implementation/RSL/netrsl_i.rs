use crate::common::collections::seq_is_unique_v::{endpoints_contain, seq_is_unique};
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::implementation::common::marshalling::*;
use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
use std::collections::*;
use vstd::prelude::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus! {

    pub enum ReceiveResult {
        Fail,
        Timeout,
        Packet{cpacket: CPacket},
    }

    #[verifier::external_body]
    pub fn print(s: &str) {
        println!("{}", s);
    }

    #[verifier(external_body)]
    pub fn rsl_demarshall_data_method(buffer: &Vec<u8>) -> (out: CMessage)
    {
        match CMessage::deserialize(&buffer, 0)
        {
            None => {
                print("invalid message");
                CMessage::CMessageInvalid{}
            },
            Some((cmessage, count)) => {
                if count != buffer.len() {print("count and length mismatch"); return CMessage::CMessageInvalid{};}
                else {
                    // print("receive valid msg");
                    cmessage
                }
            }
        }
    }

    #[verifier(external_body)]
    pub fn receive_packet(netc: &mut NetClient, local_addr: &EndPoint) -> (rc: (ReceiveResult, Ghost<NetEvent>))
    {
        let timeout = 0;
        let netr = netc.receive(timeout);

        match netr {
            NetcReceiveResult::Error => {
                let dummy = NetEvent::TimeoutReceive{};
                println!("receive error");
                (ReceiveResult::Fail, Ghost(dummy))
            },
            NetcReceiveResult::TimedOut{} => {
                // println!("receive timeout");
                (ReceiveResult::Timeout{}, Ghost(NetEvent::TimeoutReceive{}))
            },
            NetcReceiveResult::Received{sender, message} => {
                // println!("receive success");
                let rslmessage = rsl_demarshall_data_method(&message);

                let src_ep = sender;
                let cpacket = CPacket{dst: local_addr.clone_up_to_view(), src: src_ep,msg: rslmessage};
                let ghost net_event: NetEvent = LIoOp::Receive{
                    r: LPacket{dst: local_addr@, src: src_ep@, msg: message@}
                };
                netc.recycle_buffer(message);
                (ReceiveResult::Packet{cpacket}, Ghost(net_event))
            }
        }
    }

    #[verifier(external_body)]
    pub fn send_packet(cpacket: &CPacket, netc: &mut NetClient) -> (rc:(bool, Ghost<Option<NetEvent>>))
    {
        let mut buf = netc.take_buffer();
        cpacket.msg.serialize(&mut buf);
        let ghost bytes = buf@;
        match netc.send(&cpacket.dst, buf)
        {
            Ok(_) => {
                let ghost lpacket = LPacket::<AbstractEndPoint, Seq<u8>>{ dst: cpacket.dst@, src: netc.my_end_point(), msg: bytes };
                let ghost net_event = LIoOp::Send{s:  lpacket};
                (true, Ghost(Some(net_event)))
            },
            Err(_) => {
                (false, Ghost(None))
            }
        }
    }

    pub fn send_packet_seq(cpackets: &Vec<CPacket>, netc: &mut NetClient) -> (rc:(bool, Ghost<Seq<NetEvent>>))
    {
        let ghost net_events = Seq::<NetEvent>::empty();

        let mut i:usize = 0;
        while i < cpackets.len()
            decreases cpackets.len() - i,
        {
            let cpacket: &CPacket = &cpackets[i];
            let (ok, Ghost(net_event)) = send_packet(cpacket, netc);
            if !ok {
                return (false, Ghost(Seq::<NetEvent>::empty()));
            }
            i = i + 1;
        }
        (true, Ghost(net_events))
    }

    pub fn send_broadcast(broadcast: &CBroadcast, netc: &mut NetClient) -> (rc:(bool, Ghost<Seq<NetEvent>>))
    {
        let ghost net_events = Seq::<NetEvent>::empty();

        match broadcast{
            CBroadcast::CBroadcastNop {  } => {
                (true, Ghost(net_events))
            }
            CBroadcast::CBroadcast { src, dsts, msg } => {
                let mut i:usize = 0;
                while i < dsts.len()
                    decreases dsts.len() - i,
                {
                    let dstEp:EndPoint = dsts[i].clone_up_to_view();
                    let cpacket: CPacket = CPacket{dst: dstEp, src: src.clone_up_to_view(), msg: msg.clone_up_to_view()};
                    let (ok, Ghost(net_event)) = send_packet(&cpacket, netc);
                    if !ok {
                        return (false, Ghost(Seq::<NetEvent>::empty()));
                    }
                    i = i + 1;
                }
                (true, Ghost(net_events))
            }
        }
    }

    #[verifier(external_body)]
    pub fn read_clock(netc: &mut NetClient) -> (clock:u64)
    {
        let t = netc.get_time();
        t
    }
}
