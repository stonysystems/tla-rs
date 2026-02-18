//! Generic network send/receive for protocol messages.
//!
//! Wraps the low-level NetClient byte-oriented interface with protocol-specific
//! message serialization/deserialization. All functions here are runtime glue,
//! declared outside verus! macro.

#![allow(unused_imports)]
use crate::common::framework::protocol_trait::*;
use crate::common::native::io_s::*;
use vstd::prelude::*;

/// Receive a packet from the network and deserialize it into a protocol message.
///
/// Returns GenericReceiveResult::Packet on success, Timeout on timeout,
/// or Fail on error (including deserialization failure).
pub fn receive_packet<M: ProtocolMessage>(
    netc: &mut NetClient,
    local_addr: &EndPoint,
) -> GenericReceiveResult<M>
{
    let timeout = 0i32;
    let netr = netc.receive(timeout);

    match netr {
        NetcReceiveResult::Error => {
            GenericReceiveResult::Fail
        },
        NetcReceiveResult::TimedOut {} => {
            GenericReceiveResult::Timeout
        },
        NetcReceiveResult::Received { sender, message } => {
            match M::deserialize_from_bytes(&message) {
                None => {
                    GenericReceiveResult::Fail
                },
                Some(msg) => {
                    let packet = GenericPacket {
                        dst: local_addr.clone_up_to_view(),
                        src: sender,
                        msg,
                    };
                    GenericReceiveResult::Packet { packet }
                }
            }
        }
    }
}

/// Serialize and send a single packet over the network.
///
/// Returns true on success, false on send failure.
pub fn send_packet<M: ProtocolMessage>(
    dst: &EndPoint,
    msg: &M,
    netc: &mut NetClient,
) -> bool
{
    let mut buf: Vec<u8> = Vec::new();
    msg.serialize_to_bytes(&mut buf);

    match netc.send(dst, &buf) {
        Ok(_) => true,
        Err(_) => false,
    }
}

/// Send an outbound result (single, broadcast, sequence, or none).
///
/// Returns true if all sends succeeded, false if any failed.
pub fn deliver_outbound<M: ProtocolMessage>(
    outbound: &GenericOutbound<M>,
    netc: &mut NetClient,
) -> bool
{
    match outbound {
        GenericOutbound::None => true,
        GenericOutbound::Send { dst, msg } => {
            send_packet(dst, msg, netc)
        },
        GenericOutbound::Broadcast { dsts, msg } => {
            for dst in dsts.iter() {
                if !send_packet(dst, msg, netc) {
                    return false;
                }
            }
            true
        },
        GenericOutbound::Sequence { packets } => {
            for packet in packets.iter() {
                if !send_packet(&packet.dst, &packet.msg, netc) {
                    return false;
                }
            }
            true
        },
    }
}
