//! Generic protocol traits for building runnable verified distributed protocols.
//!
//! All non-RSL protocols implement these traits to plug into the generic
//! host/main loop infrastructure. The types and traits here are declared
//! outside verus! since they are runtime infrastructure, not verified code.

#![allow(unused_imports)]
use crate::common::framework::args_t::*;
use crate::common::native::io_s::*;
use vstd::prelude::*;

/// A protocol packet: destination, source, and a protocol-specific message.
pub struct GenericPacket<M> {
    pub dst: EndPoint,
    pub src: EndPoint,
    pub msg: M,
}

/// Result of attempting to receive a packet from the network.
pub enum GenericReceiveResult<M> {
    /// Successfully received and deserialized a protocol message.
    Packet { packet: GenericPacket<M> },
    /// Network timeout (no packet available).
    Timeout,
    /// Network or deserialization error.
    Fail,
}

/// Outbound packets produced by a protocol action.
pub enum GenericOutbound<M> {
    /// Send a single packet to one destination.
    Send { dst: EndPoint, msg: M },
    /// Broadcast the same message to all destinations.
    Broadcast { dsts: Vec<EndPoint>, msg: M },
    /// Send a sequence of packets to potentially different destinations.
    Sequence { packets: Vec<GenericPacket<M>> },
    /// No outbound packets (internal state transition only).
    None,
}

/// Trait that each protocol's message type must implement.
///
/// Provides serialization/deserialization for network transport.
/// Each protocol defines its own CMessage enum and implements this.
pub trait ProtocolMessage: Sized {
    /// Serialize this message into bytes.
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>);

    /// Deserialize a message from bytes. Returns None on failure.
    fn deserialize_from_bytes(data: &Vec<u8>) -> Option<Self>;
}

/// Trait that each protocol's configuration must implement.
///
/// Provides initialization from command-line arguments.
pub trait ProtocolConfig: Sized {
    /// Parse configuration from command-line arguments.
    fn parse_config(me: &EndPoint, args: &Args) -> Option<Self>;

    /// Get all peer endpoints for this protocol.
    fn get_peers(&self) -> &Vec<EndPoint>;
}

/// The result of a single protocol step.
pub struct StepResult<M> {
    /// Whether the step succeeded (false = fatal error, stop the loop).
    pub ok: bool,
    /// Outbound packets to send after this step.
    pub outbound: GenericOutbound<M>,
}

/// Trait that each protocol's host state must implement.
///
/// This is the main interface between the generic framework and each protocol.
/// The `init` and `next` methods wrap the transpiler-generated `CInit` and
/// action functions (CHeadReceiveWrite, CReceivePrepare, etc.).
pub trait ProtocolHost: Sized {
    /// The protocol-specific message type.
    type Msg: ProtocolMessage;
    /// The protocol-specific configuration type.
    type Cfg: ProtocolConfig;

    /// Initialize protocol state from configuration.
    fn init(config: &Self::Cfg) -> Option<Self>;

    /// Execute one protocol step.
    ///
    /// The implementation should:
    /// 1. Check if `packet` matches any enabled action guard
    /// 2. If so, call the corresponding transpiler-generated C* function
    /// 3. Determine what outbound messages to send based on state changes
    /// 4. Return the step result
    ///
    /// If `packet` is None, this is a timeout — the implementation may
    /// run timer-driven actions or do nothing.
    fn next(&mut self, config: &Self::Cfg, packet: Option<GenericPacket<Self::Msg>>) -> StepResult<Self::Msg>;
}
