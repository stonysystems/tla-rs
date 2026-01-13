#![allow(unused_imports)]
use std::collections::HashMap;

use crate::common::framework::args_t::{abstractify_args, Args};
use crate::common::framework::environment_s::*;
use crate::common::logic::*;
use crate::common::native::io_s::*;
use crate::implementation::common::cmd_line_parser_i::{parse_args, parse_end_points};
use crate::implementation::lock::cmd_line_parser_i::parse_cmd_line;
use crate::implementation::lock::host_i::HostState;
use crate::implementation::lock::host_s::EventResults;
use crate::implementation::lock::message_i::abstractify_net_packet_to_lock_packet;
use crate::implementation::lock::netlock_i::{
    abstractify_net_event_to_lock_io, abstractify_raw_log_to_ios,
};
use crate::implementation::lock::node_i::{valid_config, ConcreteConfig};
use crate::protocol::lock::distributed_system_procotol_i::{ls_init, ls_next, AbstractLSState};
use crate::protocol::lock::node::{AbstractConfig, AbstractNode};
use crate::protocol::lock::types::{LockEnvironment, LockIo, LockMessage, LockPacket};
use builtin::*;
use builtin_macros::*;
use vstd::hash_map::HashMapWithView;
use vstd::seq_lib::lemma_seq_properties;
use vstd::set_lib::lemma_set_properties;
use vstd::view::*;
use vstd::{modes::*, prelude::*, seq::*, set::*, *};

verus! {
    pub struct IronError {

    }

    pub fn lock_main(netc: NetClient, args: Args) -> Result<(), IronError>
        requires
            netc.valid(),
            netc.state() is Receiving,
            from_trusted_code(),
    {
        let mut netc = netc;    // Verus does not support `mut` arguments

        let opt_host_state: Option<HostState> = HostState::init_impl(&netc, &args);
        let mut host_state = match opt_host_state {
            None => { return Err(IronError{}) },
            Some(thing) => thing,
        };
        let mut ok: bool = true;

        let end_point = netc.get_my_end_point();

        assert(HostState::init_ensures(&netc, args, Some(host_state)));

        while (ok)
            invariant
            from_trusted_code(),   // this predicate's value cannot change, but has to be explicitly imported into the loop invariant
            ok ==> host_state.invariants(&netc.my_end_point()),
            ok == netc.ok(),
            ok ==> netc.state() is Receiving,
        {
            // no need for decreases * because exec functions don't termination-check

            let old_net_history: Ghost<History> = Ghost(netc.history());
            let old_state: Ghost<HostState> = Ghost(host_state);

            let (shadow_ok, event_results) = host_state.next_impl(&mut netc);
            ok = shadow_ok;

            if ok {
            assert(host_state.invariants(&netc.my_end_point()));

            // Correctly executed one action
            assert(HostState::next(old_state@@, host_state@, event_results@.ios));

            // Connect the low-level IO events to the spec-level IO events
            assert(event_results@.event_seq() == event_results@.ios);

            // The event_seq obligation enable us to apply reduction. But we shouldn't need to separate these
            // events out anymore (relative to ironfleet) now that we're enforcing this ordering in the
            // NetClient interface.
            assert(netc.history() == old_net_history@ + event_results@.event_seq());
            assert(event_results@.well_typed_events());

            // Reset to allow receiving for the next atomic step.
            netc.reset();
            }
        }
        Ok(())
    }
}
