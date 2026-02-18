//! LeaderElection protocol service entry point.

use crate::common::framework::args_t::*;
use crate::common::framework::generic_main::*;
use crate::common::native::io_s::*;
use crate::implementation::LeaderElection::host::LeaderElectionHost;

pub fn leader_election_main(netc: NetClient, args: Args) -> Result<(), ProtocolError> {
    protocol_main::<LeaderElectionHost>(netc, args)
}
