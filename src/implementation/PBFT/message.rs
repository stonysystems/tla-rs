//! PBFT consensus protocol network messages.

use crate::common::framework::protocol_trait::ProtocolMessage;

#[derive(Clone)]
pub enum PBFTMessage {
    /// Primary broadcasts a pre-prepare for a client request.
    PrePrepare {
        view: u64,
        seq: u64,
        digest: u64,
    },
    /// Replica sends a prepare message to all peers.
    Prepare {
        view: u64,
        seq: u64,
        digest: u64,
        sender: u64,
    },
    /// Replica sends a commit message to all peers.
    Commit {
        view: u64,
        seq: u64,
        sender: u64,
    },
    /// Client sends a request to the primary.
    ClientRequest {
        digest: u64,
    },
}

// Message tags for serialization
const TAG_PRE_PREPARE: u64 = 1;
const TAG_PREPARE: u64 = 2;
const TAG_COMMIT: u64 = 3;
const TAG_CLIENT_REQUEST: u64 = 4;

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

impl ProtocolMessage for PBFTMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            PBFTMessage::PrePrepare { view, seq, digest } => {
                buf.extend_from_slice(&TAG_PRE_PREPARE.to_le_bytes());
                buf.extend_from_slice(&view.to_le_bytes());
                buf.extend_from_slice(&seq.to_le_bytes());
                buf.extend_from_slice(&digest.to_le_bytes());
            },
            PBFTMessage::Prepare { view, seq, digest, sender } => {
                buf.extend_from_slice(&TAG_PREPARE.to_le_bytes());
                buf.extend_from_slice(&view.to_le_bytes());
                buf.extend_from_slice(&seq.to_le_bytes());
                buf.extend_from_slice(&digest.to_le_bytes());
                buf.extend_from_slice(&sender.to_le_bytes());
            },
            PBFTMessage::Commit { view, seq, sender } => {
                buf.extend_from_slice(&TAG_COMMIT.to_le_bytes());
                buf.extend_from_slice(&view.to_le_bytes());
                buf.extend_from_slice(&seq.to_le_bytes());
                buf.extend_from_slice(&sender.to_le_bytes());
            },
            PBFTMessage::ClientRequest { digest } => {
                buf.extend_from_slice(&TAG_CLIENT_REQUEST.to_le_bytes());
                buf.extend_from_slice(&digest.to_le_bytes());
            },
        }
    }

    fn deserialize_from_bytes(data: &Vec<u8>) -> Option<Self> {
        if data.len() < 8 {
            return None;
        }
        let tag = read_u64(data, 0);
        match tag {
            TAG_PRE_PREPARE => {
                if data.len() < 32 {
                    return None;
                }
                let view = read_u64(data, 8);
                let seq = read_u64(data, 16);
                let digest = read_u64(data, 24);
                Some(PBFTMessage::PrePrepare { view, seq, digest })
            },
            TAG_PREPARE => {
                if data.len() < 40 {
                    return None;
                }
                let view = read_u64(data, 8);
                let seq = read_u64(data, 16);
                let digest = read_u64(data, 24);
                let sender = read_u64(data, 32);
                Some(PBFTMessage::Prepare { view, seq, digest, sender })
            },
            TAG_COMMIT => {
                if data.len() < 32 {
                    return None;
                }
                let view = read_u64(data, 8);
                let seq = read_u64(data, 16);
                let sender = read_u64(data, 24);
                Some(PBFTMessage::Commit { view, seq, sender })
            },
            TAG_CLIENT_REQUEST => {
                if data.len() < 16 {
                    return None;
                }
                let digest = read_u64(data, 8);
                Some(PBFTMessage::ClientRequest { digest })
            },
            _ => None,
        }
    }
}
