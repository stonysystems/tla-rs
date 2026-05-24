//! Bully Leader Election protocol network messages.

use crate::common::framework::protocol_trait::ProtocolMessage;

#[derive(Clone)]
pub enum LeaderElectionMessage {
    /// Node announces candidacy to higher-ID nodes.
    Election {
        sender: u64,
    },
    /// Higher-ID node responds, suppressing the election.
    Answer {
        responder: u64,
    },
    /// Elected leader announces itself.
    Coordinator {
        leader: u64,
    },
}

// Message tags for serialization
const TAG_ELECTION: u64 = 1;
const TAG_ANSWER: u64 = 2;
const TAG_COORDINATOR: u64 = 3;

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

impl ProtocolMessage for LeaderElectionMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            LeaderElectionMessage::Election { sender } => {
                buf.extend_from_slice(&TAG_ELECTION.to_le_bytes());
                buf.extend_from_slice(&sender.to_le_bytes());
            },
            LeaderElectionMessage::Answer { responder } => {
                buf.extend_from_slice(&TAG_ANSWER.to_le_bytes());
                buf.extend_from_slice(&responder.to_le_bytes());
            },
            LeaderElectionMessage::Coordinator { leader } => {
                buf.extend_from_slice(&TAG_COORDINATOR.to_le_bytes());
                buf.extend_from_slice(&leader.to_le_bytes());
            },
        }
    }

    fn deserialize_from_bytes(data: &Vec<u8>) -> Option<Self> {
        if data.len() < 8 {
            return None;
        }
        let tag = read_u64(data, 0);
        match tag {
            TAG_ELECTION => {
                if data.len() < 16 {
                    return None;
                }
                let sender = read_u64(data, 8);
                Some(LeaderElectionMessage::Election { sender })
            },
            TAG_ANSWER => {
                if data.len() < 16 {
                    return None;
                }
                let responder = read_u64(data, 8);
                Some(LeaderElectionMessage::Answer { responder })
            },
            TAG_COORDINATOR => {
                if data.len() < 16 {
                    return None;
                }
                let leader = read_u64(data, 8);
                Some(LeaderElectionMessage::Coordinator { leader })
            },
            _ => None,
        }
    }
}
