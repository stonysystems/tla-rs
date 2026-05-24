//! Two-Phase Commit protocol network messages.

use crate::common::framework::protocol_trait::ProtocolMessage;

#[derive(Clone)]
pub enum TwoPhaseMessage {
    /// TM sends prepare to all RMs.
    Prepare,
    /// RM votes that it is prepared.
    PreparedVote {
        rm_id: u64,
    },
    /// TM broadcasts commit decision.
    Commit,
    /// TM broadcasts abort decision.
    Abort,
}

// Message tags for serialization
const TAG_PREPARE: u64 = 1;
const TAG_PREPARED_VOTE: u64 = 2;
const TAG_COMMIT: u64 = 3;
const TAG_ABORT: u64 = 4;

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
        let tag = read_u64(data, 0);
        match tag {
            TAG_PREPARE => {
                Some(TwoPhaseMessage::Prepare)
            },
            TAG_PREPARED_VOTE => {
                if data.len() < 16 {
                    return None;
                }
                let rm_id = read_u64(data, 8);
                Some(TwoPhaseMessage::PreparedVote { rm_id })
            },
            TAG_COMMIT => {
                Some(TwoPhaseMessage::Commit)
            },
            TAG_ABORT => {
                Some(TwoPhaseMessage::Abort)
            },
            _ => None,
        }
    }
}
