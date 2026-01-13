#![allow(unused_imports)]
use std::net;

use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

use super::message_i::*;
use crate::common::framework::environment_s::{LIoOp, LPacket};
use crate::common::native::io_s::*;
use crate::implementation::common::marshalling::Marshalable;
use crate::protocol::lock::types::*;

verus! {
    pub enum ReceiveResult {
        Fail,
        Timeout,
        Packet{cpacket: CLockPacket},
    }

    pub open spec fn net_packet_is_abstractable(net: NetPacket) -> bool
    {
        true
    }

    pub open spec fn net_event_is_abstractable(evt: NetEvent) -> bool
     {
         match evt {
             LIoOp::<AbstractEndPoint, Seq<u8>>::Send{s} => net_packet_is_abstractable(s),
             LIoOp::<AbstractEndPoint, Seq<u8>>::Receive{r} => net_packet_is_abstractable(r),
             LIoOp::<AbstractEndPoint, Seq<u8>>::TimeoutReceive{} => true,
             LIoOp::<AbstractEndPoint, Seq<u8>>::ReadClock{t} => true,
         }
     }

    pub open spec fn net_event_log_is_abstractable(rawlog: Seq<NetEvent>) -> bool
    {
        forall |i: int| 0 <= i && i < rawlog.len() ==> #[trigger] net_event_is_abstractable(rawlog[i])
    }

    pub open spec fn raw_io_consistent_with_spec_io(rawlog: Seq<NetEvent>, ios: Seq<LockIo>) -> bool
    {
        &&& net_event_log_is_abstractable(rawlog)
        &&& abstractify_raw_log_to_ios(rawlog) == ios
    }


    pub open spec fn abstractify_net_event_to_lock_io(evt:NetEvent) -> LockIo
    {

        match evt {
            LIoOp::Send{ s } => LIoOp::Send{s: abstractify_net_packet_to_lock_packet(s)},
            LIoOp::Receive{r} => LIoOp::Receive{r: abstractify_net_packet_to_lock_packet(r)},
            LIoOp::TimeoutReceive => LIoOp::TimeoutReceive{},
            LIoOp::ReadClock{t} => LIoOp::ReadClock{t: t as int},
        }
    }

    pub open spec fn abstractify_raw_log_to_ios(rawlog: Seq<NetEvent>) -> Seq<LockIo>
    {
        rawlog.map_values(|evt: NetEvent| abstractify_net_event_to_lock_io(evt))
    }

    #[verifier(spinoff_prover)]
    pub proof fn lock_marshal_data_injective(a: &CMessage, b: &CMessage)
    requires
        a.is_marshalable(),
        b.is_marshalable(),
        a.ghost_serialize() == b.ghost_serialize(),
    ensures
        a@ == b@,
    {
        a.lemma_serialize_injective(b);
        assert(a@ == b@);
    }

    pub fn lock_demarshall_data_method(buffer: &Vec<u8>) -> (out: CMessage)
    ensures
        !(out is CInvalid) ==> {
            &&& out.is_marshalable()
            &&& out@ == lock_demarshal_data(buffer@)@
            &&& out.abstractable()
        },
    {
        match CMessage::deserialize(&buffer, 0) {
            None => {
                CMessage::CInvalid
            },
            Some((cmessage, count)) => {
                if count != buffer.len() { return CMessage::CInvalid; }
                proof {
                    assert( buffer@.subrange(0, count as int) =~= buffer@ );
                    lock_marshal_data_injective(&lock_demarshal_data(buffer@), &cmessage);
                }
                cmessage
            }
        }
    }

    pub fn receive(netc: &mut NetClient, local_addr: &EndPoint) -> (rc: (ReceiveResult, Ghost<NetEvent>))
        requires
            old(netc).ok(),
            old(netc).my_end_point() == local_addr@,
            old(netc).state() is Receiving,
            local_addr.abstractable(),
        ensures
        ({let (rr, net_event) = rc;
            &&& netc.my_end_point() == old(netc).my_end_point()
            &&& netc.ok() == !(rr is Fail)
            &&& !(rr is Fail) ==> netc.ok() && netc.history() == old(netc).history() + seq!( net_event@ )
            &&& rr is Timeout ==> net_event@ is TimeoutReceive
            &&& (rr is Packet ==> {
                &&& net_event@ is Receive
                &&& rr->cpacket.abstractable()
                &&&  !(rr->cpacket@.msg is Invalid) ==> {
                    &&& rr->cpacket@ == abstractify_net_packet_to_lock_packet(net_event@->r)
                    &&& rr->cpacket.msg@ == lock_demarshal_data(net_event@->r.msg)@
                }
                &&& rr->cpacket.dst@ == local_addr@
            })
        })
    {
        let timeout = 0;
        let netr = netc.receive(timeout);

        match netr {
            NetcReceiveResult::Error => {
                let dummy = NetEvent::TimeoutReceive{};
                (ReceiveResult::Fail, Ghost(dummy))
            },
            NetcReceiveResult::TimedOut{} => {
                (ReceiveResult::Timeout, Ghost(NetEvent::TimeoutReceive{}))
            },
            NetcReceiveResult::Received{sender, message} => {
                let cmessage = lock_demarshall_data_method(&message);
                assert( (cmessage is CTransfer || cmessage is CLocked) ==> cmessage@ == lock_demarshal_data(message@)@ );

                let src_ep = sender;
                let cpacket = CLockPacket{dst: local_addr.clone_up_to_view(), src: src_ep, msg: cmessage};
                let ghost net_event: NetEvent = LIoOp::Receive{
                                                        r: LPacket{dst: local_addr@, src: src_ep@, msg: message@}
                                                };
                assert( cpacket.dst@ == local_addr@ );
                assert( cpacket.src.abstractable() );
                assert( cpacket.abstractable() );

                proof {
                    let ghost gmessage = cmessage;
                    if !(gmessage is CInvalid) {
                        let lp = LPacket {
                            dst: local_addr@,
                            src: src_ep@,
                            msg: (lock_demarshal_data(message@))@
                        };
                        assert( lp == abstractify_net_packet_to_lock_packet(net_event->r));
                        let p = LockPacket{ dst: lp.dst, src: lp.src, msg: lp.msg };
                        assert( p == abstractify_net_packet_to_lock_packet(net_event->r));
                        assert( !(gmessage is CInvalid) );
                        assert( gmessage@ == (lock_demarshal_data(message@))@ );
                        assert( cpacket@.dst =~= p.dst );
                        assert( cpacket@.src =~= p.src );
                        assert( cpacket@.msg =~= p.msg );
                        assert( cpacket@ =~= p );
                        assert( cpacket@ == abstractify_net_packet_to_lock_packet(net_event->r));
                        assert( gmessage is CTransfer || gmessage is CLocked ==> cpacket.msg@ == lock_demarshal_data(net_event->r.msg)@);
                    }
                }
                (ReceiveResult::Packet{cpacket}, Ghost(net_event))
            }
        }
    }

    pub open spec fn send_log_entry_reflects_packet(event: NetEvent, cpacket: &CLockPacket) -> bool
    {
        &&& event is Send
        &&& cpacket.abstractable()
        &&& cpacket@ == abstractify_net_packet_to_lock_packet(event->s)
    }

    pub open spec fn send_log_entries_reflect_packets(net_event_log: Seq<NetEvent>, packet: Option<CLockPacket>) -> bool
    {
        match packet {
            Some(p) => net_event_log.len() == 1 && send_log_entry_reflects_packet(net_event_log[0], &p),
            None => net_event_log =~= Seq::<NetEvent>::empty()
        }
    }

    pub open spec fn net_packet_bound(data: Seq<u8>) -> bool
    {
        data.len() <= 0xffff_ffff_ffff_ffff
    }

    pub open spec fn is_marshalable_data(event: NetEvent) -> bool
    recommends event is Send
    {
        &&& net_packet_bound(event->s.msg)
        &&& lock_demarshal_data(event->s.msg).is_marshalable()
    }

    pub open spec fn only_sent_marshalable_data(rawlog:Seq<NetEvent>) -> bool
    {
        forall |i| 0 <= i < rawlog.len() && rawlog[i] is Send ==>
            #[trigger] is_marshalable_data(rawlog[i])
    }


    pub fn send(netc:&mut NetClient, opt_packet:Option<CLockPacket>, local_addr: &EndPoint) -> (rc: (bool, Ghost<Seq<NetEvent>>))
    requires
        old(netc).ok(),
        old(netc).my_end_point() == local_addr@,
        optional_clock_packet_is_valid(opt_packet),
        opt_packet is Some ==> {
            match opt_packet {
                Some(packet) => {
                    packet.src@ == local_addr@
                },
                _ => {true}
            }
        },
    ensures
        netc.my_end_point() == old(netc).my_end_point(),
        ({
            let (ok, Ghost(net_events)) = rc;
            {
                &&& netc.ok() <==> ok
                &&& ok ==> netc.history() == old(netc).history() + net_events
                &&& ok ==> only_sent_marshalable_data(net_events)
                &&& ok ==> send_log_entries_reflect_packets(net_events, opt_packet) // failing
            }
        })
    {
        let ghost net_events = Seq::<NetEvent>::empty();
        assert(netc.history() == old(netc).history() + net_events);

        match opt_packet {
            None => {
                (true, Ghost(net_events))
            },
            Some(packet) => {
                let cpacket = packet;
                let mut buf: Vec<u8> = Vec::new();
                // witness that buf@.len() < 2^64
                let _ = buf.len();
                // marshall the message
                cpacket.msg.serialize(&mut buf);
                match netc.send(&cpacket.dst, &buf) {
                    Ok(_) => {
                        let ghost lpacket = LPacket::<AbstractEndPoint, Seq<u8>>{ dst: cpacket.dst@, src: netc.my_end_point(), msg: buf@ };
                        let ghost net_event = LIoOp::Send{s:  lpacket};
                        proof {
                            net_events = net_events + seq![net_event];
                            assert_seqs_equal!( buf@ == cpacket.msg.ghost_serialize() );
                            assert(net_packet_bound(buf@));
                            let purported_cpacket = lock_demarshal_data(buf@);
                            lock_marshal_data_injective( &cpacket.msg, &purported_cpacket );
                        }
                        (true, Ghost(net_events))
                    },
                    Err(_) => {
                        (false, Ghost(net_events))
                    },
                }
            }
        }
    }
}
