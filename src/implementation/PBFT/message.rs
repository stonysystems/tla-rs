//! PBFT protocol network messages.
//!
//! Maps the spec's PBFT actions to explicit network messages for distributed
//! deployment. Serialization uses simple u64 tag-based encoding.
//!
//! Message flow:
//!   Client -> Primary:    ClientRequest { digest }                  (request)
//!   Primary -> All:       PrePrepare { view, seq, digest }          (pre-prepare)
//!   Replica -> All:       Prepare { view, seq, digest, sender }     (prepare)
//!   Replica -> All:       Commit { view, seq, sender }              (commit)

use crate::common::framework::protocol_trait::ProtocolMessage;

/// Network messages for the PBFT consensus protocol.
pub enum PBFTMessage {
    /// Primary broadcasts a pre-prepare for a client request.
    PrePrepare { view: u64, seq: u64, digest: u64 },
    /// Replica sends a prepare message to all peers.
    Prepare {
        view: u64,
        seq: u64,
        digest: u64,
        sender: u64,
    },
    /// Replica sends a commit message to all peers.
    Commit { view: u64, seq: u64, sender: u64 },
    /// Client sends a request to the primary.
    ClientRequest { digest: u64 },
}

// Message tags for serialization
const TAG_PRE_PREPARE: u64 = 1;
const TAG_PREPARE: u64 = 2;
const TAG_COMMIT: u64 = 3;
const TAG_CLIENT_REQUEST: u64 = 4;

impl ProtocolMessage for PBFTMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            PBFTMessage::PrePrepare { view, seq, digest } => {
                buf.extend_from_slice(&TAG_PRE_PREPARE.to_le_bytes());
                buf.extend_from_slice(&view.to_le_bytes());
                buf.extend_from_slice(&seq.to_le_bytes());
                buf.extend_from_slice(&digest.to_le_bytes());
            }
            PBFTMessage::Prepare {
                view,
                seq,
                digest,
                sender,
            } => {
                buf.extend_from_slice(&TAG_PREPARE.to_le_bytes());
                buf.extend_from_slice(&view.to_le_bytes());
                buf.extend_from_slice(&seq.to_le_bytes());
                buf.extend_from_slice(&digest.to_le_bytes());
                buf.extend_from_slice(&sender.to_le_bytes());
            }
            PBFTMessage::Commit { view, seq, sender } => {
                buf.extend_from_slice(&TAG_COMMIT.to_le_bytes());
                buf.extend_from_slice(&view.to_le_bytes());
                buf.extend_from_slice(&seq.to_le_bytes());
                buf.extend_from_slice(&sender.to_le_bytes());
            }
            PBFTMessage::ClientRequest { digest } => {
                buf.extend_from_slice(&TAG_CLIENT_REQUEST.to_le_bytes());
                buf.extend_from_slice(&digest.to_le_bytes());
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
            TAG_PRE_PREPARE => {
                if data.len() < 32 {
                    return None;
                }
                let view = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                let seq = u64::from_le_bytes([
                    data[16], data[17], data[18], data[19], data[20], data[21], data[22], data[23],
                ]);
                let digest = u64::from_le_bytes([
                    data[24], data[25], data[26], data[27], data[28], data[29], data[30], data[31],
                ]);
                Some(PBFTMessage::PrePrepare { view, seq, digest })
            }
            TAG_PREPARE => {
                if data.len() < 40 {
                    return None;
                }
                let view = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                let seq = u64::from_le_bytes([
                    data[16], data[17], data[18], data[19], data[20], data[21], data[22], data[23],
                ]);
                let digest = u64::from_le_bytes([
                    data[24], data[25], data[26], data[27], data[28], data[29], data[30], data[31],
                ]);
                let sender = u64::from_le_bytes([
                    data[32], data[33], data[34], data[35], data[36], data[37], data[38], data[39],
                ]);
                Some(PBFTMessage::Prepare {
                    view,
                    seq,
                    digest,
                    sender,
                })
            }
            TAG_COMMIT => {
                if data.len() < 32 {
                    return None;
                }
                let view = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                let seq = u64::from_le_bytes([
                    data[16], data[17], data[18], data[19], data[20], data[21], data[22], data[23],
                ]);
                let sender = u64::from_le_bytes([
                    data[24], data[25], data[26], data[27], data[28], data[29], data[30], data[31],
                ]);
                Some(PBFTMessage::Commit { view, seq, sender })
            }
            TAG_CLIENT_REQUEST => {
                if data.len() < 16 {
                    return None;
                }
                let digest = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                Some(PBFTMessage::ClientRequest { digest })
            }
            _ => None,
        }
    }
}
