//! Paxos protocol network messages.
//!
//! Maps the spec's single-decree Paxos actions to explicit network messages
//! for distributed deployment. Serialization uses simple u64 tag-based encoding.
//!
//! Message flow:
//!   Proposer -> Acceptors: Prepare { ballot }                             (Phase 1a)
//!   Acceptor -> Proposer:  Promise { ballot, accepted_bal, accepted_val } (Phase 1b)
//!   Proposer -> Acceptors: Accept { ballot, value }                       (Phase 2a)
//!   Acceptor -> Proposer:  Accepted { ballot, value }                     (Phase 2b)

use crate::common::framework::protocol_trait::ProtocolMessage;

/// Network messages for the Single-Decree Paxos protocol.
pub enum PaxosMessage {
    /// Phase 1a: Proposer sends Prepare with a ballot number.
    Prepare { ballot: u64 },
    /// Phase 1b: Acceptor promises not to accept lower ballots.
    /// Includes the highest ballot/value it has already accepted (0 if none).
    Promise {
        ballot: u64,
        accepted_bal: u64,
        accepted_val: u64,
    },
    /// Phase 2a: Proposer sends Accept with ballot and chosen value.
    Accept { ballot: u64, value: u64 },
    /// Phase 2b: Acceptor confirms it has accepted the ballot/value.
    Accepted { ballot: u64, value: u64 },
}

// Message tags for serialization
const TAG_PREPARE: u64 = 1;
const TAG_PROMISE: u64 = 2;
const TAG_ACCEPT: u64 = 3;
const TAG_ACCEPTED: u64 = 4;

impl ProtocolMessage for PaxosMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            PaxosMessage::Prepare { ballot } => {
                buf.extend_from_slice(&TAG_PREPARE.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
            }
            PaxosMessage::Promise {
                ballot,
                accepted_bal,
                accepted_val,
            } => {
                buf.extend_from_slice(&TAG_PROMISE.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
                buf.extend_from_slice(&accepted_bal.to_le_bytes());
                buf.extend_from_slice(&accepted_val.to_le_bytes());
            }
            PaxosMessage::Accept { ballot, value } => {
                buf.extend_from_slice(&TAG_ACCEPT.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            }
            PaxosMessage::Accepted { ballot, value } => {
                buf.extend_from_slice(&TAG_ACCEPTED.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
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
            TAG_PREPARE => {
                if data.len() < 16 {
                    return None;
                }
                let ballot = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                Some(PaxosMessage::Prepare { ballot })
            }
            TAG_PROMISE => {
                if data.len() < 32 {
                    return None;
                }
                let ballot = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                let accepted_bal = u64::from_le_bytes([
                    data[16], data[17], data[18], data[19], data[20], data[21], data[22], data[23],
                ]);
                let accepted_val = u64::from_le_bytes([
                    data[24], data[25], data[26], data[27], data[28], data[29], data[30], data[31],
                ]);
                Some(PaxosMessage::Promise {
                    ballot,
                    accepted_bal,
                    accepted_val,
                })
            }
            TAG_ACCEPT => {
                if data.len() < 24 {
                    return None;
                }
                let ballot = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                let value = u64::from_le_bytes([
                    data[16], data[17], data[18], data[19], data[20], data[21], data[22], data[23],
                ]);
                Some(PaxosMessage::Accept { ballot, value })
            }
            TAG_ACCEPTED => {
                if data.len() < 24 {
                    return None;
                }
                let ballot = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                let value = u64::from_le_bytes([
                    data[16], data[17], data[18], data[19], data[20], data[21], data[22], data[23],
                ]);
                Some(PaxosMessage::Accepted { ballot, value })
            }
            _ => None,
        }
    }
}
