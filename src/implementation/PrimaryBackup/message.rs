//! Primary-Backup protocol network messages.

use crate::common::framework::protocol_trait::ProtocolMessage;

#[derive(Clone)]
pub enum PrimaryBackupMessage {
    /// Primary sends replicate to backup.
    Replicate {
        value: u64,
    },
    /// Backup acknowledges replication.
    Ack,
    /// Client sends write request.
    ClientRequest {
        value: u64,
    },
    /// Primary replies to client after commit.
    ClientReply {
        value: u64,
    },
}

// Message tags for serialization
const TAG_REPLICATE: u64 = 1;
const TAG_ACK: u64 = 2;
const TAG_CLIENT_REQUEST: u64 = 3;
const TAG_CLIENT_REPLY: u64 = 4;

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

impl ProtocolMessage for PrimaryBackupMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            PrimaryBackupMessage::Replicate { value } => {
                buf.extend_from_slice(&TAG_REPLICATE.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            },
            PrimaryBackupMessage::Ack => {
                buf.extend_from_slice(&TAG_ACK.to_le_bytes());
            },
            PrimaryBackupMessage::ClientRequest { value } => {
                buf.extend_from_slice(&TAG_CLIENT_REQUEST.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            },
            PrimaryBackupMessage::ClientReply { value } => {
                buf.extend_from_slice(&TAG_CLIENT_REPLY.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            },
        }
    }

    fn deserialize_from_bytes(data: &Vec<u8>) -> Option<Self> {
        if data.len() < 8 {
            return None;
        }
        let tag = read_u64(data, 0);
        match tag {
            TAG_REPLICATE => {
                if data.len() < 16 {
                    return None;
                }
                let value = read_u64(data, 8);
                Some(PrimaryBackupMessage::Replicate { value })
            },
            TAG_ACK => {
                Some(PrimaryBackupMessage::Ack)
            },
            TAG_CLIENT_REQUEST => {
                if data.len() < 16 {
                    return None;
                }
                let value = read_u64(data, 8);
                Some(PrimaryBackupMessage::ClientRequest { value })
            },
            TAG_CLIENT_REPLY => {
                if data.len() < 16 {
                    return None;
                }
                let value = read_u64(data, 8);
                Some(PrimaryBackupMessage::ClientReply { value })
            },
            _ => None,
        }
    }
}
