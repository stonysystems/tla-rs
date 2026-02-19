use crate::common::framework::args_t::*;
use crate::common::framework::environment_s::*;
use crate::common::logic::*;
use crate::common::native::io_s::*;
use crate::implementation::RSL::{
    cbroadcast::*, cconfiguration::*, cconstants::*, cmd_line_parser::*, cmessage::*,
    cparameters::*, host_s::*, netrsl_i::*, replicaimpl_class::*, replicaimpl_delivery::*,
    replicaimpl_main::*, replicaimpl_no_receive_clock::*, replicaimpl_no_receive_no_clock::*,
    replicaimpl_process_packet_no_clock::*, replicaimpl_process_packet_x::*,
    replicaimpl_read_clock::*, ReplicaImpl::*,
};
use crate::protocol::RSL::environment::*;
use crate::verus_extra::seq_lib_v::*;
use vstd::prelude::*;
use vstd::slice::*;

verus! {
    pub struct HostState{
        pub replica_impl:ReplicaImpl,
    }

    impl HostState{
        #[verifier(external_body)]
        pub fn host_init_impl(netc: &NetClient, args: &Args) -> (rc: Option<Self>)
        {
            let me = netc.get_my_end_point();
            let config = parse_cmd_line(&me, args);
            if matches!(config, None) {
                println!("parse endpoints fail");
                return None;
            }

            let (config, my_index) = config.unwrap();

            let params = StaticParams();
            let constants = CConstants{config:config, params:params};
            let replicaconstants = CReplicaConstants{my_index:my_index as u64, all:constants};

            let replica_impl = ReplicaImpl::Replica_Init(replicaconstants);
            let host_state = HostState{
                replica_impl:replica_impl,
            };
            Some(host_state)
        }

        #[verifier(external_body)]
        pub fn host_next_impl(&mut self, netc:&mut NetClient) -> (rc: (bool, Ghost<EventResults>))
        {
            let (ok, Ghost(event_results), Ghost(ios)) = Replica_Next_main(&mut self.replica_impl, netc);
            (ok, Ghost(event_results))
        }
    }
}
