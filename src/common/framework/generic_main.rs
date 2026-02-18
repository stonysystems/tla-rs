//! Generic main entry point for all protocol services.
//!
//! Provides the top-level init -> loop -> shutdown pattern shared by all protocols.

#![allow(unused_imports)]
use crate::common::framework::args_t::*;
use crate::common::framework::generic_host::*;
use crate::common::framework::protocol_trait::*;
use crate::common::native::io_s::*;
use vstd::prelude::*;

/// Error type for protocol main function.
pub struct ProtocolError {
    pub message: String,
}

/// Generic main loop for any protocol.
///
/// This function:
/// 1. Initializes the host state from command-line arguments
/// 2. Runs the receive -> dispatch -> send loop until a fatal error
/// 3. Returns Ok(()) on graceful shutdown, Err on initialization failure
///
/// Each protocol calls this with its concrete ProtocolHost type:
/// ```ignore
/// pub fn twophase_main(netc: NetClient, args: Args) -> Result<(), ProtocolError> {
///     protocol_main::<TwoPhaseHost>(netc, args)
/// }
/// ```
pub fn protocol_main<H: ProtocolHost>(
    netc: NetClient,
    args: Args,
) -> Result<(), ProtocolError>
{
    let mut netc = netc;

    let host_state = GenericHostState::<H>::init(&netc, &args);
    let mut host_state = match host_state {
        None => {
            return Err(ProtocolError {
                message: String::from("Failed to initialize protocol host state"),
            });
        },
        Some(hs) => hs,
    };

    let mut ok = true;
    while ok {
        ok = host_state.next(&mut netc);
    }

    Ok(())
}
