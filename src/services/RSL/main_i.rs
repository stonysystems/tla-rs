#![allow(unused_imports)]
use std::collections::HashMap;

use crate::common::framework::args_t::{abstractify_args, Args};
use crate::common::framework::environment_s::*;
use crate::common::logic::*;
use crate::common::native::io_s::*;
use crate::implementation::common::cmd_line_parser_i::{parse_args, parse_end_points};
use crate::implementation::RSL::{host_i::*, host_s::*};
use builtin::*;
use builtin_macros::*;
use vstd::view::*;
use vstd::{modes::*, prelude::*, seq::*, set::*, *};

verus!{
    pub struct IronError {

    }


    pub fn paxos_main(netc:NetClient, args:Args) -> Result<(), IronError>
    {
        let mut netc = netc;

        let opt_host_state: Option<HostState> = HostState::init_impl(&netc, &args);
        let mut host_state = match opt_host_state {
            None => { return Err(IronError{}) },
            Some(thing) => thing,
        };
        let mut ok: bool = true;

        let end_point = netc.get_my_end_point();

        while(ok)
        {
            let (shadow_ok, event_results) = host_state.next_impl(&mut netc);
            ok = shadow_ok;
        }
        Ok(())
    }
}