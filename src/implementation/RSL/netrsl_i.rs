use crate::common::collections::seq_is_unique_v::{endpoints_contain, seq_is_unique};
use crate::common::framework::environment_s::*;
use crate::common::framework::environment_s::*;
// use crate::common::native::io_s::AbstractEndPoint::*;
use crate::common::native::io_s::*;
use crate::common::native::io_s::{abstractify_end_points, EndPoint};
use crate::implementation::common::marshalling::*;
use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
use builtin::*;
use builtin_macros::*;
use std::collections::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus! {

    // define_enum_and_derive_marshalable! {
    //     #[derive(Clone)]
    //     pub enum CMessage {
    //         #[tag = 0]
    //         CMessageInvalid{},
    //         #[tag = 1]
    //         CMessageRequest{
    //             #[o=o0] seqno_req:u64,
    //             #[o=o1] val:CAppMessage,
    //         },
    //         #[tag = 2]
    //         CMessage1a{
    //             #[o=o0] bal_1a:CBallot,
    //         },
    //         #[tag = 3]
    //         CMessage1b{
    //             #[o=o0] bal_1b:CBallot,
    //             #[o=o1] log_truncation_point:COperationNumber,
    //             // #[o=o2] votes:CVotes,
    //         },
    //         #[tag = 4]
    //         CMessage2a{
    //             #[o=o0] bal_2a:CBallot,
    //             #[o=o1] opn_2a:COperationNumber,
    //             #[o=o2] val_2a:CRequestBatch,
    //         },
    //         #[tag = 5]
    //         CMessage2b{
    //             #[o=o0] bal_2b:CBallot,
    //             #[o=o1] opn_2b:COperationNumber,
    //             #[o=o2] val_2b:CRequestBatch,
    //         },
    //         #[tag = 6]
    //         CMessageHeartbeat{
    //             #[o=o0] bal_heartbeat:CBallot,
    //             // #[o=o1] suspicious:bool,
    //             #[o=o1] opn_ckpt:COperationNumber,
    //         },
    //         #[tag = 7]
    //         CMessageReply{
    //             #[o=o0] seqno_reply:u64,
    //             #[o=o1] reply:CAppMessage,
    //         },
    //         #[tag = 8]
    //         CMessageAppStateRequest{
    //             #[o=o0] bal_state_req:CBallot,
    //             #[o=o1] opn_state_req:COperationNumber,
    //         },
    //         #[tag = 9]
    //         CMessageAppStateSupply{
    //             #[o=o0] bal_state_supply:CBallot,
    //             #[o=o1] opn_state_supply:COperationNumber,
    //             #[o=o2] app_state:CAppState,
    //             #[o=o3] reply_cache:CReplyCache,
    //         },
    //         #[tag = 10]
    //         CMessageStartingPhase2{
    //             #[o=o0] bal_2:CBallot,
    //             #[o=o1] logTruncationPoint_2:COperationNumber,
    //         },
    //     }
    //     [rlimit attr = verifier::rlimit(25)]
    // }

    // #[derive(Clone)]
    // pub struct CPacket{
    //     pub dst: EndPoint,
    //     pub src: EndPoint,
    //     pub msg: CMessage,
    // }

    // impl CPacket{
    //     pub open spec fn abstractable(self) -> bool
    //     {
    //         &&& self.dst.abstractable()
    //         &&& self.src.abstractable()
    //         &&& self.msg.abstractable()
    //     }

    //     pub open spec fn valid(self) -> bool
    //     {
    //         &&& self.dst.valid_public_key()
    //         &&& self.src.valid_public_key()
    //         &&& self.msg.valid()
    //     }

    //     // pub open spec fn view(self) -> RslPacket
    //     //     recommends self.abstractable()
    //     // {
    //     //     LPacket{
    //     //         dst: self.dst@,
    //     //         src: self.src@,
    //     //         msg: self.msg@,
    //     //     }
    //     // }
    // }

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
    pub fn deserialize_cappmessage(data: &Vec<u8>, start: usize) -> Option<(CAppMessage, usize)> {
        if start >= data.len() {
            return None;
        }
        let tag = data[start];
        if tag == 0 {
            // println!("valid cappmessage");
            Some((CAppMessage::CAppIncrement {}, start + 1))
        } else if tag == 1 {
            let (response, end) = u64::deserialize(data, start + 1)?;
            Some((CAppMessage::CAppReply { response }, end))
        } else {
            // println!("invalid cappmessage");
            None
        }
    }

    #[verifier(external_body)]
    pub fn deserialize_crequest(data: &Vec<u8>, start: usize) -> Option<(CRequest, usize)> {
        let (client, mid1) = EndPoint::deserialize(data, start)?;
        let (seqno, mid2) = u64::deserialize(data, mid1)?;
        let (request, end) = deserialize_cappmessage(data, mid2)?;
        Some((CRequest {
            client,
            seqno,
            request,
        }, end))
    }

    #[verifier(external_body)]
    pub fn deserialize_crequestbatch(data: &Vec<u8>, start: usize) -> Option<(Vec<CRequest>, usize)> {
        let (len, mut mid) = match usize::deserialize(data, start) {
            Some(x) => x,
            None => return None,
        };

        let mut batch = Vec::with_capacity(len);
        let mut i = 0;
        while i < len {
            let (req, next) = match deserialize_crequest(data, mid) {
                Some(x) => x,
                None => {
                    println!("Failed to deserialize CRequest at index {}", i);
                    return None;
                }
            };
            batch.push(req);
            mid = next;
            i += 1;
        }

        Some((batch, mid))
    }


    #[verifier(external_body)]
    pub fn deserialize_cmessagerequest(buffer: &Vec<u8>, start: usize) -> Option<(CMessage, usize)> {
        if start + 9 > buffer.len() {
            return None;
        }

        let mut mid = start;

        mid += 1;

        let (seqno_req, next) = match u64::deserialize(buffer, mid) {
            Some(x) => x,
            None => return None,
        };
        mid = next;

        let (val, end) = match deserialize_cappmessage(buffer, mid) {
            Some(x) => x,
            None => return None,
        };

        Some((CMessage::CMessageRequest {
            seqno_req,
            val,
        }, end))
    }

    #[verifier(external_body)]
    pub fn deserialize_cmessage2a(data: &Vec<u8>, start: usize) -> Option<(CMessage, usize)> {
        if start >= data.len() { return None; }
        if data[start] != 4 { return None; }

        let mut mid = start + 1;

        let (bal, m1) = match CBallot::deserialize(data, mid) {
            Some(x) => x,
            None => {println!("invalid ballot"); return None},
        };
        let (opn, m2) = u64::deserialize(data, m1)?;
        let (val, end) = match deserialize_crequestbatch(data, m2){
            Some(x) => x,
            None => {println!("invalid crequestbatch"); return None},
        };

        Some((CMessage::CMessage2a {
            bal_2a: bal,
            opn_2a: opn,
            val_2a: val,
        }, end))
    }

    #[verifier(external_body)]
    pub fn deserialize_cmessage2b(data: &Vec<u8>, start: usize) -> Option<(CMessage, usize)> {
        if start >= data.len() { return None; }
        if data[start] != 5 { return None; }

        let mut mid = start + 1;

        let (bal, m1) = match CBallot::deserialize(data, mid) {
            Some(x) => x,
            None => {println!("invalid ballot"); return None},
        };
        let (opn, m2) = u64::deserialize(data, m1)?;
        let (val, end) = match deserialize_crequestbatch(data, m2){
            Some(x) => x,
            None => {println!("invalid crequestbatch"); return None},
        };

        Some((CMessage::CMessage2b {
            bal_2b: bal,
            opn_2b: opn,
            val_2b: val,
        }, end))
    }



    #[verifier(external_body)]
    pub fn rsl_demarshall_data_method(buffer: &Vec<u8>) -> (out: CMessage)
    {
        // println!("trying to deserialize CMessage");
        // println!("buffer len: {}", buffer.len());
        if buffer[0] == 1 {
            // println!("first byte (tag): {}", buffer[0]);
            // println!("buffer len: {}", buffer.len());
            // println!("last byte (tag): {}", buffer[9]);
            let msg = deserialize_cmessagerequest(buffer, 0);
            match msg {
                None => {
                    print("invalid message");
                    return CMessage::CMessageInvalid{};
                },
                Some((cmessage, count)) => {
                    if count != buffer.len() {print("count and length mismatch"); return CMessage::CMessageInvalid{};}
                    else {
                        return cmessage;
                    }
                }
            }
        } else if buffer[0] == 4 {
            let msg = deserialize_cmessage2a(buffer, 0);
            match msg {
                None => {
                    print("invalid 2a message");
                    return CMessage::CMessageInvalid{};
                },
                Some((cmessage, count)) => {
                    if count != buffer.len() {print("count and length mismatch"); return CMessage::CMessageInvalid{};}
                    else {
                        return cmessage;
                    }
                }
            }
        } else if buffer[0] == 5 {
            let msg = deserialize_cmessage2b(buffer, 0);
            match msg {
                None => {
                    print("invalid 2b message");
                    return CMessage::CMessageInvalid{};
                },
                Some((cmessage, count)) => {
                    if count != buffer.len() {print("count and length mismatch"); return CMessage::CMessageInvalid{};}
                    else {
                        return cmessage;
                    }
                }
            }
        }
        

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
                (ReceiveResult::Packet{cpacket}, Ghost(net_event))
            }
        }
    }

    #[verifier(external_body)]
    pub fn send_packet(cpacket: &CPacket, netc: &mut NetClient) -> (rc:(bool, Ghost<Option<NetEvent>>))
    {
        // let ghost net_events = Seq::<NetEvent>::empty();
        let mut buf: Vec<u8> = Vec::new();
        cpacket.msg.serialize(&mut buf);

        let _ = buf.len();
        match netc.send(&cpacket.dst, &buf)
        {
            Ok(_) => {
                let ghost lpacket = LPacket::<AbstractEndPoint, Seq<u8>>{ dst: cpacket.dst@, src: netc.my_end_point(), msg: buf@ };
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
