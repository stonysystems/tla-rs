//! LeaderElection protocol network messages.
//!
//! Maps the spec's shared-state boolean message flags to explicit network
//! messages for distributed deployment. The spec uses boolean flags
//! (msgs_election, msgs_answer, msgs_coordinator) with associated sender/
//! responder/leader fields; this enum encodes each flag+payload pair as a
//! distinct message variant.
//!
//! Serialization uses simple u64 tag-based encoding.

use crate::common::framework::protocol_trait::ProtocolMessage;

/// Network messages for the Bully Leader Election protocol.
///
/// Message flow:
///   Node -> higher-ID nodes: Election { sender } (initiating election)
///   Higher-ID node -> sender: Answer { responder } (suppresses sender's election)
///   Winner -> all nodes: Coordinator { leader } (announces new leader)
pub enum LeaderElectionMessage {
    /// A node initiates an election (Bully algorithm step 1).
    /// Corresponds to spec: msgs_election=true, msgs_election_sender=sender.
    Election { sender: u64 },
    /// A higher-ID node responds to suppress a lower node's election.
    /// Corresponds to spec: msgs_answer=true, msgs_answer_responder=responder.
    Answer { responder: u64 },
    /// The election winner announces itself as the new leader.
    /// Corresponds to spec: msgs_coordinator=true, msgs_coordinator_leader=leader.
    Coordinator { leader: u64 },
}

// Message tags for serialization
const TAG_ELECTION: u64 = 1;
const TAG_ANSWER: u64 = 2;
const TAG_COORDINATOR: u64 = 3;

impl ProtocolMessage for LeaderElectionMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            LeaderElectionMessage::Election { sender } => {
                buf.extend_from_slice(&TAG_ELECTION.to_le_bytes());
                buf.extend_from_slice(&sender.to_le_bytes());
            }
            LeaderElectionMessage::Answer { responder } => {
                buf.extend_from_slice(&TAG_ANSWER.to_le_bytes());
                buf.extend_from_slice(&responder.to_le_bytes());
            }
            LeaderElectionMessage::Coordinator { leader } => {
                buf.extend_from_slice(&TAG_COORDINATOR.to_le_bytes());
                buf.extend_from_slice(&leader.to_le_bytes());
            }
        }
    }

    fn deserialize_from_bytes(data: &Vec<u8>) -> Option<Self> {
        if data.len() < 16 {
            return None;
        }
        let tag = u64::from_le_bytes([
            data[0], data[1], data[2], data[3], data[4], data[5], data[6], data[7],
        ]);
        let payload = u64::from_le_bytes([
            data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
        ]);
        match tag {
            TAG_ELECTION => Some(LeaderElectionMessage::Election { sender: payload }),
            TAG_ANSWER => Some(LeaderElectionMessage::Answer { responder: payload }),
            TAG_COORDINATOR => Some(LeaderElectionMessage::Coordinator { leader: payload }),
            _ => None,
        }
    }
}
