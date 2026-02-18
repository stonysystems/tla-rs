//! Generic host state and main event loop for all protocols.
//!
//! Provides the common receive -> dispatch -> send loop that all protocols share.
//! Each protocol plugs in via the ProtocolHost trait.

#![allow(unused_imports)]
use crate::common::framework::generic_net::*;
use crate::common::framework::protocol_trait::*;
use crate::common::native::io_s::*;
use vstd::prelude::*;

/// Generic host wrapping protocol-specific state and configuration.
pub struct GenericHostState<H: ProtocolHost> {
    pub protocol: H,
    pub config: H::Cfg,
    pub local_addr: EndPoint,
}

impl<H: ProtocolHost> GenericHostState<H> {
    /// Initialize the host: parse config, create protocol state.
    pub fn init(netc: &NetClient, args: &crate::common::framework::args_t::Args) -> Option<Self> {
        let me = netc.get_my_end_point();
        let config = H::Cfg::parse_config(&me, args)?;
        let protocol = H::init(&config)?;
        Some(GenericHostState {
            protocol,
            config,
            local_addr: me,
        })
    }

    /// Execute one step of the protocol event loop.
    ///
    /// 1. Receive a packet (or timeout)
    /// 2. Dispatch to the protocol's next() handler
    /// 3. Send any outbound packets
    ///
    /// Returns false if a fatal error occurred and the loop should stop.
    pub fn next(&mut self, netc: &mut NetClient) -> bool {
        // Step 1: Receive
        let recv_result: GenericReceiveResult<H::Msg> =
            receive_packet::<H::Msg>(netc, &self.local_addr);

        let packet = match recv_result {
            GenericReceiveResult::Packet { packet } => Some(packet),
            GenericReceiveResult::Timeout => None,
            GenericReceiveResult::Fail => {
                // Receive error - not fatal, try again next iteration
                return true;
            }
        };

        // Step 2: Dispatch to protocol handler
        let step_result = self.protocol.next(&self.config, packet);

        if !step_result.ok {
            return false;
        }

        // Step 3: Send outbound packets
        let _send_ok = deliver_outbound(&step_result.outbound, netc);

        true
    }
}
