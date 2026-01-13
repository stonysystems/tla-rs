#![allow(unused_imports)]
use super::host_i::HostState;
use super::netlock_i::only_sent_marshalable_data;
use super::node_i::{ConcreteConfig, Node};
use crate::common::collections::seq_is_unique_v::endpoints_contain;
use crate::common::framework::args_t::*;
use crate::common::native::io_s::*;
use crate::implementation::common::cmd_line_parser_i::*;
use crate::implementation::lock::netlock_i::abstractify_raw_log_to_ios;
use crate::protocol::lock::node::{AbstractConfig, AbstractNode, NodeInit, NodeNext};
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {
    type Ios = Seq<NetEvent>;

    pub struct EventResults {
        pub recvs: Seq<NetEvent>,
        pub clocks: Seq<NetEvent>,
        pub sends: Seq<NetEvent>,
        pub ios: Ios,
    }

    impl EventResults {
        pub open spec fn event_seq(self) -> Seq<NetEvent> {
            self.recvs + self.clocks + self.sends
        }

        pub open spec fn well_typed_events(self) -> bool {
            &&& forall |i| 0 <= i < self.recvs.len() ==> self.recvs[i] is Receive
            &&& forall |i| 0 <= i < self.clocks.len() ==> self.clocks[i] is ReadClock || self.clocks[i] is TimeoutReceive
            &&& forall |i| 0 <= i < self.sends.len() ==> self.sends[i] is Send
            &&& self.clocks.len() <= 1
        }

        pub open spec fn empty() -> Self {
            EventResults{
                recvs: seq!(),
                clocks: seq!(),
                sends: seq!(),
                ios: seq!(),
            }
        }
    }

    impl HostState {
        pub open spec fn host_init(host_state: Self, config: AbstractConfig, id: AbstractEndPoint) -> bool {
            &&& NodeInit(host_state@, host_state@.my_index, config)
            &&& host_state@.config =~= config
            &&& host_state@.config[host_state@.my_index as int] == id
            &&& config.contains(id)
        }

        pub open spec fn init_ensures(netc: &NetClient, args: Args, rc: Option<Self>) -> bool
        {
            match rc {
                None => true,
                Some(host_state) => {
                    &&& netc.ok()
                    &&& host_state.invariants(&netc.my_end_point())
                    &&& ({
                        let end_points = parse_args(abstractify_args(args));
                        let id = netc.my_end_point();

                        if end_points is None || end_points.unwrap().len() == 0 {
                            false
                        } else {
                            Self::host_init(host_state, end_points.unwrap(), id)
                        }
                    })
                }
            }
        }

        pub fn init_impl(netc: &NetClient, args: &Args) -> (rc: Option<Self>)
        requires
            netc.valid()
        ensures
            Self::init_ensures(netc, *args, rc),
        {
            Self::real_init_impl(netc, args)
        }

        pub open spec fn next_requires(self, netc: NetClient) -> bool
        {
            &&& self.invariants(&netc.my_end_point())
            &&& netc.state() is Receiving
        }

        pub open spec fn next_ensures(s: Self, old_netc: NetClient, s_: Self, new_netc: NetClient, rc: (bool, Ghost<EventResults>)) -> bool
        {
            let (ok, res) = rc; {
                &&& ok == new_netc.ok()
                &&& ok ==> s_.invariants(&new_netc.my_end_point())
                &&& ok ==> Self::next(s.view(), s_.view(), res@.ios)
                &&& ok ==> res@.event_seq() == res@.ios
                &&& (ok || res@.sends.len()>0) ==> new_netc.history() == old_netc.history() + res@.event_seq()
                &&& res@.well_typed_events()
            }
        }

        pub fn next_impl(&mut self, netc: &mut NetClient) -> (rc: (bool, Ghost<EventResults>))
            requires
                Self::next_requires(*old(self), *old(netc)),
            ensures
                Self::next_ensures(*old(self), *old(netc), *self, *netc, rc),
        {
            self.real_next_impl(netc)
        }

        pub open spec fn next(pre: AbstractNode, post: AbstractNode, ios: Ios) -> bool
        {
            &&& NodeNext(pre, post, abstractify_raw_log_to_ios(ios))
            &&& only_sent_marshalable_data(ios)
        }
    }
}
