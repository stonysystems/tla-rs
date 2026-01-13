use builtin::*;
use builtin_macros::*;
use crate::implementation::common::function::*;
use vstd::prelude::*;
use vstd::slice::*;
use crate::verus_extra::seq_lib_v::*;
use crate::common::native::io_s::*;
use crate::protocol::RSL::environment::*;
use crate::common::collections::seq_is_unique_v::seq_is_unique;
use crate::common::framework::args_t::*;
use crate::common::framework::environment_s::*;
use crate::common::logic::*;
use crate::common::native::io_s::*;
use crate::implementation::RSL::{
    replicaimpl_class::*, 
    cmessage::*, cbroadcast::*, 
    cconstants::*, cconfiguration::*,
    cparameters::*,
    replicaimpl_delivery::*, 
    netrsl_i::*, 
    ReplicaImpl::*,
    replicaimpl_read_clock::*,
    replicaimpl_process_packet_no_clock::*,
    replicaimpl_process_packet_x::*,
    replicaimpl_no_receive_clock::*,
    replicaimpl_no_receive_no_clock::*,
    replicaimpl_main::*,
    cmd_line_parser::*,
};
use super::host_i::HostState;

verus!{
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
        #[verifier(external_body)]
        pub fn init_impl(netc: &NetClient, args: &Args) -> (rc: Option<Self>)
        // requires
        //     netc.valid()
        // ensures
        //     Self::init_ensures(netc, *args, rc),
        {
            // println!("init_impl called");
            // println!("args.len = {}", args.len());
            // for (i, a) in args.iter().enumerate() {
            //     println!("arg[{}] = {:?}", i, a);
            // }
            Self::host_init_impl(netc, args)
        }

        pub fn next_impl(&mut self, netc: &mut NetClient) -> (rc: (bool, Ghost<EventResults>))
            // requires
            //     Self::next_requires(*old(self), *old(netc)),
            // ensures
            //     Self::next_ensures(*old(self), *old(netc), *self, *netc, rc),
        {
            self.host_next_impl(netc)
        }
    }
}