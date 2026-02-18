//! Paxos protocol service entry point.

use crate::common::framework::args_t::*;
use crate::common::framework::generic_main::*;
use crate::common::native::io_s::*;
use crate::implementation::Paxos::host::PaxosHost;

pub fn paxos_main(netc: NetClient, args: Args) -> Result<(), ProtocolError> {
    protocol_main::<PaxosHost>(netc, args)
}
