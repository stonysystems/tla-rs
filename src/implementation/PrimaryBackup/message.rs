//! PrimaryBackup protocol network messages.
//!
//! Maps the spec's shared-state boolean message model to explicit network
//! messages for distributed deployment. Serialization uses simple u64 tags.

use crate::common::framework::protocol_trait::ProtocolMessage;

/// Network messages for the Primary-Backup replication protocol.
///
/// Message flow:
///   Client -> Primary: ClientRequest { value } (write request)
///   Primary -> Backup: Replicate { value } (replicate pending write)
///   Backup -> Primary: Ack (acknowledge replication)
pub enum PrimaryBackupMessage {
    /// Primary sends a replicate request to the backup.
    Replicate { value: u64 },
    /// Backup acknowledges successful replication.
    Ack,
    /// External client sends a write request to the primary.
    ClientRequest { value: u64 },
}

// Message tags for serialization
const TAG_REPLICATE: u64 = 1;
const TAG_ACK: u64 = 2;
const TAG_CLIENT_REQUEST: u64 = 3;

impl ProtocolMessage for PrimaryBackupMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            PrimaryBackupMessage::Replicate { value } => {
                buf.extend_from_slice(&TAG_REPLICATE.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            }
            PrimaryBackupMessage::Ack => {
                buf.extend_from_slice(&TAG_ACK.to_le_bytes());
            }
            PrimaryBackupMessage::ClientRequest { value } => {
                buf.extend_from_slice(&TAG_CLIENT_REQUEST.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
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
            TAG_REPLICATE => {
                if data.len() < 16 {
                    return None;
                }
                let value = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                Some(PrimaryBackupMessage::Replicate { value })
            }
            TAG_ACK => Some(PrimaryBackupMessage::Ack),
            TAG_CLIENT_REQUEST => {
                if data.len() < 16 {
                    return None;
                }
                let value = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                Some(PrimaryBackupMessage::ClientRequest { value })
            }
            _ => None,
        }
    }
}
