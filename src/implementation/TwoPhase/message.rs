//! TwoPhase protocol network messages.
//!
//! Maps the spec's shared-state boolean message model to explicit network
//! messages for distributed deployment. Serialization uses simple u64 tags.

use crate::common::framework::protocol_trait::ProtocolMessage;

/// Network messages for the Two-Phase Commit protocol.
///
/// Message flow:
///   TM -> RMs: Prepare (broadcast)
///   RM -> TM: PreparedVote { rm_id } (unicast)
///   TM -> RMs: Commit (broadcast, when all RMs prepared)
///   TM -> RMs: Abort (broadcast, when TM decides to abort)
pub enum TwoPhaseMessage {
    /// TM broadcasts Prepare to all RMs.
    Prepare,
    /// RM votes Prepared (sends to TM).
    PreparedVote { rm_id: u64 },
    /// TM broadcasts Commit to all RMs.
    Commit,
    /// TM broadcasts Abort to all RMs.
    Abort,
}

// Message tags for serialization
const TAG_PREPARE: u64 = 1;
const TAG_PREPARED_VOTE: u64 = 2;
const TAG_COMMIT: u64 = 3;
const TAG_ABORT: u64 = 4;

impl ProtocolMessage for TwoPhaseMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            TwoPhaseMessage::Prepare => {
                buf.extend_from_slice(&TAG_PREPARE.to_le_bytes());
            },
            TwoPhaseMessage::PreparedVote { rm_id } => {
                buf.extend_from_slice(&TAG_PREPARED_VOTE.to_le_bytes());
                buf.extend_from_slice(&rm_id.to_le_bytes());
            },
            TwoPhaseMessage::Commit => {
                buf.extend_from_slice(&TAG_COMMIT.to_le_bytes());
            },
            TwoPhaseMessage::Abort => {
                buf.extend_from_slice(&TAG_ABORT.to_le_bytes());
            },
        }
    }

    fn deserialize_from_bytes(data: &Vec<u8>) -> Option<Self> {
        if data.len() < 8 {
            return None;
        }
        let tag = u64::from_le_bytes([
            data[0], data[1], data[2], data[3],
            data[4], data[5], data[6], data[7],
        ]);
        match tag {
            TAG_PREPARE => Some(TwoPhaseMessage::Prepare),
            TAG_PREPARED_VOTE => {
                if data.len() < 16 {
                    return None;
                }
                let rm_id = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11],
                    data[12], data[13], data[14], data[15],
                ]);
                Some(TwoPhaseMessage::PreparedVote { rm_id })
            },
            TAG_COMMIT => Some(TwoPhaseMessage::Commit),
            TAG_ABORT => Some(TwoPhaseMessage::Abort),
            _ => None,
        }
    }
}
