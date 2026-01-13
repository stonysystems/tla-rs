#![allow(unused_imports)]

use super::cmd_line_parser_i::parse_cmd_line;
use super::host_s::*;
use super::node_i::{valid_config, Node};
use super::nodeimpl_i::NodeImpl;
use crate::common::collections::seq_is_unique_v::seq_is_unique;
use crate::common::framework::args_t::*;
use crate::common::framework::environment_s::*;
use crate::common::logic::*;
use crate::common::native::io_s::*;
use crate::protocol::lock::node::*;
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {
    pub struct HostState {
        pub node_impl: NodeImpl,
    }

    impl HostState {
        // In IronFleet, the host has a protocol field and the node_impl field.
        // The protocol object is in fact pointing to the node_impl's protocol field
        // This seems redundant, adds more lines to invariant etc.
        // Instead we can maintain a view to the AbstractNode, so host_state@ == host_state.node == host_state.node_impl.node@
        pub open spec fn view(self) -> AbstractNode {
            self.node_impl.node.view()
        }

        pub closed spec fn invariants(self, netc_endpoint: &AbstractEndPoint) -> bool {
            &&& self.node_impl.valid()
            &&& self.node_impl.me@ == netc_endpoint // need this because node_impl doesn't own netc like in IronFleet
            &&& self.node_impl.me@.abstractable()
        }

        // HostInitImpl
        pub fn real_init_impl(netc: &NetClient, args: &Args) -> (rc: Option<Self>)
            requires
                netc.valid(),
            ensures
                Self::init_ensures(netc, *args, rc)
        {
            let me = netc.get_my_end_point();
            let config = parse_cmd_line(&me, args);
            if matches!(config, None) {
                return None;
            }

            proof {
                assert(config.is_some());
                // assert(config.is_some() ==> parse_args(abstractify_args(*args)).is_some());
            }

            let (config, my_index) = config.unwrap();

            let node_impl = NodeImpl::init(config, my_index, &me);
            let host_state = HostState{
                node_impl,
            };

            // Uncomment these observes if needed
            // proof{
                // assert(netc.ok());
                // assert(host_state.invariants(&netc.my_end_point()));
                // assert(0 <= my_index < config.len());
                // assert(seq_is_unique(abstractify_end_points(config)));
                // assert(valid_config(config));
                // assert(NodeInit(host_state@, host_state@.my_index, abstractify_end_points(config)));
                // assert(host_state@.config[host_state@.my_index as int] == me@);
            // }

            Some(host_state)
        }

        pub fn real_next_impl(&mut self, netc: &mut NetClient) -> (rc: (bool, Ghost<EventResults>))
            requires
                Self::next_requires(*old(self), *old(netc))
            ensures
                Self::next_ensures(*old(self), *old(netc), *self, *netc, rc)
        {
            let (ok, Ghost(event_results), Ghost(ios)) = self.node_impl.host_next_main(netc);
            (ok, Ghost(event_results))
        }
    }
}
