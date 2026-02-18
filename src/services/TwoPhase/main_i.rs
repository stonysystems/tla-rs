//! TwoPhase protocol service entry point.

use crate::common::framework::args_t::*;
use crate::common::framework::generic_main::*;
use crate::common::native::io_s::*;
use crate::implementation::TwoPhase::host::TwoPhaseHost;

/// Entry point for the Two-Phase Commit protocol service.
pub fn twophase_main(netc: NetClient, args: Args) -> Result<(), ProtocolError> {
    protocol_main::<TwoPhaseHost>(netc, args)
}
