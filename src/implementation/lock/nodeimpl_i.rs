#![allow(unused_imports)]
use std::net;

use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

use crate::common::collections::seq_is_unique_v::{endpoints_contain, seq_is_unique};
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::{abstractify_end_points, EndPoint};
use crate::common::native::io_s::{AbstractEndPoint, NetClient, NetEvent};
use crate::implementation::lock::message_i::*;
use crate::implementation::lock::netlock_i::*;
use crate::implementation::lock::node_i::*;
use crate::protocol::lock::types::*;
use crate::protocol::lock::{self, node::*};

use super::host_s::EventResults;
use super::netlock_i::only_sent_marshalable_data;

verus! {
    pub struct NodeImpl {
        pub node: Node,
        pub me: EndPoint,
    }

    proof fn empty_event_results() -> (event_results: EventResults)
    ensures
        event_results.well_typed_events(),
        event_results.ios =~= event_results.event_seq(),
        event_results.ios == Seq::<NetEvent>::empty(),
    {
        EventResults{
            recvs: Seq::<NetEvent>::empty(),
            clocks: Seq::<NetEvent>::empty(),
            sends: Seq::<NetEvent>::empty(),
            ios: Seq::<NetEvent>::empty(),
        }
    }

    impl NodeImpl {
        pub open spec fn valid(self) -> bool {
            &&& self.node.valid()
            &&& self.me@ == self.node@.config[self.node@.my_index as int]
        }

        pub open spec fn view(self) -> AbstractNode {
            self.node@
        }

        pub fn init(config: ConcreteConfig, my_index: usize, me: &EndPoint) -> (rc: Self)
            requires
                valid_config(config),
                valid_config_index(config, my_index),
                me@ == abstractify_end_points(config)[my_index as int],
            ensures
                rc.valid(),
                me@ == rc.me@,
                NodeInit(rc.node@, my_index as nat, rc.node@.config),
                rc.node@.config =~= abstractify_end_points(config),
                rc.node@.my_index == my_index as nat,
        {
            let node = Node::init(my_index, config);
            assert(node.my_index == my_index);
            let node_impl = NodeImpl{
                me: node.config[my_index].clone_up_to_view(),
                node: node,
            };
            node_impl
        }

        pub fn next_grant(&mut self, netc: &mut NetClient) -> (rc: (bool, Ghost<EventResults>, Ghost<Seq<LockIo>>))
            requires
            // These lines just correspond to self.valid(), but I'm not sure how to pass the
            // mutable netc reference to the valid spec function, so the netc dependent
            // conditions are here instead of self.valid()
                old(netc).my_end_point() == old(self).me@,
                old(netc).valid(),
                old(self).valid(),
            ensures
            ({
                let (ok, Ghost(res), Ghost(ios)) = rc;
                &&& ok ==> self.valid()
                &&& ok ==> netc.valid()
                &&& ok == netc.ok()
                &&& ok ==> netc.my_end_point() == self.me@
                &&& ok ==> NodeGrant(old(self).node@, self.node@, ios)
                &&& ok ==> abstractify_raw_log_to_ios(res.ios) == ios
                &&& ok ==> res.event_seq() == res.ios
                &&& ok ==> only_sent_marshalable_data(res.ios)
                &&& (ok || res.sends.len() > 0) ==> (*netc).history() == (*old(netc)).history() + res.event_seq()
                &&& res.well_typed_events()
            })
        {
            let (transfer_packet, Ghost(ios)) = self.node.grant();
            let ghost net_event_log = Seq::<NetEvent>::empty();
            let (ok, Ghost(send_events)) = send(netc, transfer_packet, &self.me);

            if !ok {
                let ghost event_results = empty_event_results();
                return (false, Ghost(event_results), Ghost(Seq::<LockIo>::empty()));
            }

            let ghost event_results = EventResults{
                recvs: seq![],
                clocks: seq![],
                sends: send_events,
                ios: send_events,
            };

            proof {
                assert(ok ==> abstractify_raw_log_to_ios(event_results.ios) =~= ios);
            }
            (ok, Ghost(event_results), Ghost(ios))
        }

        pub fn next_accept(&mut self, netc: &mut NetClient) -> (rc: (bool, Ghost<EventResults>, Ghost<Seq<LockIo>>))
            requires
                (*old(netc)).my_end_point() == old(self).me@,
                (*old(netc)).valid(),
                (*old(self)).valid(),
                (*old(netc)).state() is Receiving
            ensures
                ({
                    let (ok, Ghost(res), Ghost(ios)) = rc;

                    &&& ok == netc.ok()
                    &&& ok ==> self.valid()
                    &&& ok ==> netc.valid()
                    &&& ok ==> netc.my_end_point() == self.me@
                    &&& ok ==> only_sent_marshalable_data(res.ios)
                    &&& (ok || res.sends.len() > 0) ==> (*netc).history() == (*old(netc)).history() + res.event_seq()
                    &&& ok ==> NodeAccept(old(self).node@, self.node@, ios)
                    &&& ok ==> abstractify_raw_log_to_ios(res.ios) == ios
                    &&& ok ==> res.event_seq() == res.ios
                    &&& res.well_typed_events()
                })
        {
            let (rr, Ghost(receive_event)) = receive(netc, &self.me);
            let ghost net_event_log = seq![receive_event];
            match rr {
                ReceiveResult::Fail => {
                    (false, Ghost(EventResults{ recvs: seq![], clocks: seq![], sends: seq![], ios: seq![]}), Ghost(Seq::<LockIo>::empty()))
                },
                ReceiveResult::Timeout => {
                    let ghost recv = LockIo::TimeoutReceive{};
                    let ghost ios = seq![recv];
                    let ghost res = EventResults{ recvs: seq![], clocks: seq![ receive_event ], sends: seq![], ios: seq![receive_event] };
                    proof {
                        assert(res.event_seq() == res.ios);
                        assert((*netc).history() == (*old(netc)).history() + res.event_seq());
                        assert(abstractify_raw_log_to_ios(res.ios) =~= ios);
                    }
                    (true, Ghost(res), Ghost(ios))
                },
                ReceiveResult::Packet { cpacket } => {
                    match cpacket.msg {
                         CMessage::CInvalid => {
                            let ghost res = EventResults{ recvs: seq![ receive_event ], clocks: seq![], sends: seq![],
                                ios: seq![ receive_event ] };
                            let ghost ios = abstractify_raw_log_to_ios(res.ios);
                            proof {
                                assert(res.event_seq() == res.ios);
                                assert(cpacket.msg is CInvalid);
                                assert((*netc).history() == (*old(netc)).history() + res.event_seq());
                                assert(abstractify_raw_log_to_ios(res.ios) =~= ios);
                            }
                             (true, Ghost(res), Ghost(ios))
                         },
                         _ => {
                            let (opt_locked_packet, Ghost(ios)) = self.node.accept(cpacket);
                            match (opt_locked_packet) {
                                Some(locked_packet) => {
                                    let (ok, Ghost(send_event_log)) = send(netc, Some(locked_packet), &self.me);
                                    assert(ok ==> netc.ok());

                                    if !ok {
                                        let ghost event_results = empty_event_results();
                                        return (false, Ghost(event_results), Ghost(Seq::<LockIo>::empty()));
                                    }

                                    let ghost event_results = EventResults{
                                        recvs: seq![receive_event],
                                        clocks: seq![],
                                        sends: send_event_log,
                                        ios: seq![receive_event] + send_event_log,
                                    };

                                    proof {
                                        assert(ok ==> abstractify_raw_log_to_ios(event_results.ios) =~= ios);
                                        assert(event_results.ios =~= event_results.event_seq());
                                        assert(!(locked_packet.msg@ is Invalid));
                                        assert(ok ==> (*netc).history() == (*old(netc)).history() + event_results.ios);
                                        assert(event_results.well_typed_events());
                                    }
                                    (ok, Ghost(event_results), Ghost(ios))
                                },
                                None => {
                                    let ghost event_results = EventResults{
                                        recvs: seq![receive_event],
                                        clocks: seq![],
                                        sends: seq![],
                                        ios: seq![receive_event],
                                    };
                                    proof {
                                        assert(abstractify_raw_log_to_ios(event_results.ios) =~= ios);
                                        assert((*netc).history() == (*old(netc)).history() + event_results.event_seq());
                                    }
                                    (true, Ghost(event_results), Ghost(ios))
                                }
                            }
                        }
                    }
                },
            }
        }

        pub fn host_next_main(&mut self, netc: &mut NetClient) -> (rc: (bool, Ghost<EventResults>, Ghost<Seq<LockIo>>))
            requires
                (*old(netc)).my_end_point() == old(self).me@,
                (*old(netc)).valid(),
                (*old(self)).valid(),
                (*old(netc)).state() is Receiving
            ensures
                ({
                    let (ok, Ghost(res), Ghost(ios)) = rc;
                    &&& ok ==> self.valid()
                    &&& ok ==> netc.valid()
                    &&& ok == netc.ok()
                    &&& ok ==> netc.my_end_point() == self.me@
                    &&& ok ==> NodeNext(old(self)@, self@, ios)
                    &&& ok ==> abstractify_raw_log_to_ios(res.ios) =~= ios
                    &&& ok ==> only_sent_marshalable_data(res.ios)
                    &&& ok ==> res.event_seq() == res.ios
                    &&& (ok || res.sends.len() > 0) ==> (*netc).history() == (*old(netc)).history() + res.event_seq()
                    &&& res.well_typed_events()
                })
        {
            if self.node.held {
                self.next_grant(netc)
            } else {
                self.next_accept(netc)
            }
        }
    }
}
