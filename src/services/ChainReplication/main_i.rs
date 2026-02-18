//! ChainReplication protocol service entry point.

use crate::common::framework::args_t::*;
use crate::common::framework::generic_main::*;
use crate::common::native::io_s::*;
use crate::implementation::ChainReplication::host::ChainHost;

pub fn chain_replication_main(netc: NetClient, args: Args) -> Result<(), ProtocolError> {
    protocol_main::<ChainHost>(netc, args)
}
