//! Chain Replication protocol network messages.

use crate::common::framework::protocol_trait::ProtocolMessage;

#[derive(Clone)]
pub enum ChainMessage {
    /// Forward a write to the next node in the chain.
    Forward {
        value: u64,
    },
    /// Acknowledge a committed write back up the chain.
    Ack {
        value: u64,
    },
    /// Client sends a write request to the head.
    ClientWrite {
        value: u64,
    },
    /// Client sends a read request to the tail.
    ClientRead,
}

// Message tags for serialization
const TAG_FORWARD: u64 = 1;
const TAG_ACK: u64 = 2;
const TAG_CLIENT_WRITE: u64 = 3;
const TAG_CLIENT_READ: u64 = 4;

/// Read a u64 from a byte slice at the given byte offset.
fn read_u64(data: &Vec<u8>, offset: usize) -> u64 {
    u64::from_le_bytes([
        data[offset + 0],
        data[offset + 1],
        data[offset + 2],
        data[offset + 3],
        data[offset + 4],
        data[offset + 5],
        data[offset + 6],
        data[offset + 7],
    ])
}

impl ProtocolMessage for ChainMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            ChainMessage::Forward { value } => {
                buf.extend_from_slice(&TAG_FORWARD.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            },
            ChainMessage::Ack { value } => {
                buf.extend_from_slice(&TAG_ACK.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            },
            ChainMessage::ClientWrite { value } => {
                buf.extend_from_slice(&TAG_CLIENT_WRITE.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            },
            ChainMessage::ClientRead => {
                buf.extend_from_slice(&TAG_CLIENT_READ.to_le_bytes());
            },
        }
    }

    fn deserialize_from_bytes(data: &Vec<u8>) -> Option<Self> {
        if data.len() < 8 {
            return None;
        }
        let tag = read_u64(data, 0);
        match tag {
            TAG_FORWARD => {
                if data.len() < 16 {
                    return None;
                }
                let value = read_u64(data, 8);
                Some(ChainMessage::Forward { value })
            },
            TAG_ACK => {
                if data.len() < 16 {
                    return None;
                }
                let value = read_u64(data, 8);
                Some(ChainMessage::Ack { value })
            },
            TAG_CLIENT_WRITE => {
                if data.len() < 16 {
                    return None;
                }
                let value = read_u64(data, 8);
                Some(ChainMessage::ClientWrite { value })
            },
            TAG_CLIENT_READ => {
                Some(ChainMessage::ClientRead)
            },
            _ => None,
        }
    }
}
