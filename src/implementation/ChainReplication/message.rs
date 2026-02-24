//! ChainReplication protocol network messages.
//!
//! Maps the spec's shared-state boolean message model to explicit network
//! messages for distributed deployment. Serialization uses simple u64 tags.

use crate::common::framework::protocol_trait::ProtocolMessage;

/// Network messages for the Chain Replication protocol.
///
/// Message flow:
///   Client -> Head: ClientWrite { value } (write request)
///   Client -> Tail: ClientRead (read request)
///   Predecessor -> Successor: Forward { value } (replicate update down chain)
///   Successor -> Predecessor: Ack { value } (acknowledge committed value up chain)
pub enum ChainMessage {
    /// Predecessor forwards an update to its successor.
    Forward { value: u64 },
    /// Successor acknowledges a committed value to its predecessor.
    Ack { value: u64 },
    /// Client sends a write request to the head.
    ClientWrite { value: u64 },
    /// Client sends a read request to the tail.
    ClientRead,
}

// Message tags for serialization
const TAG_FORWARD: u64 = 1;
const TAG_ACK: u64 = 2;
const TAG_CLIENT_WRITE: u64 = 3;
const TAG_CLIENT_READ: u64 = 4;

impl ProtocolMessage for ChainMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            ChainMessage::Forward { value } => {
                buf.extend_from_slice(&TAG_FORWARD.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            }
            ChainMessage::Ack { value } => {
                buf.extend_from_slice(&TAG_ACK.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            }
            ChainMessage::ClientWrite { value } => {
                buf.extend_from_slice(&TAG_CLIENT_WRITE.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            }
            ChainMessage::ClientRead => {
                buf.extend_from_slice(&TAG_CLIENT_READ.to_le_bytes());
            }
        }
    }

    fn deserialize_from_bytes(data: &Vec<u8>) -> Option<Self> {
        if data.len() < 8 {
            return None;
        }
        let tag = u64::from_le_bytes([
            data[0], data[1], data[2], data[3], data[4], data[5], data[6], data[7],
        ]);
        match tag {
            TAG_FORWARD => {
                if data.len() < 16 {
                    return None;
                }
                let value = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                Some(ChainMessage::Forward { value })
            }
            TAG_ACK => {
                if data.len() < 16 {
                    return None;
                }
                let value = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                Some(ChainMessage::Ack { value })
            }
            TAG_CLIENT_WRITE => {
                if data.len() < 16 {
                    return None;
                }
                let value = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                Some(ChainMessage::ClientWrite { value })
            }
            TAG_CLIENT_READ => Some(ChainMessage::ClientRead),
            _ => None,
        }
    }
}
