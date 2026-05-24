//! Single-Decree Paxos protocol network messages.

use crate::common::framework::protocol_trait::ProtocolMessage;

#[derive(Clone)]
pub enum PaxosMessage {
    /// Phase 1a: Proposer sends Prepare with a ballot number.
    Prepare {
        ballot: u64,
    },
    /// Phase 1b: Acceptor promises not to accept lower ballots.
    Promise {
        ballot: u64,
        accepted_bal: u64,
        accepted_val: u64,
    },
    /// Phase 2a: Proposer sends Accept with ballot and chosen value.
    Accept {
        ballot: u64,
        value: u64,
    },
    /// Phase 2b: Acceptor confirms it has accepted the ballot/value.
    Accepted {
        ballot: u64,
        value: u64,
    },
}

// Message tags for serialization
const TAG_PREPARE: u64 = 1;
const TAG_PROMISE: u64 = 2;
const TAG_ACCEPT: u64 = 3;
const TAG_ACCEPTED: u64 = 4;

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

impl ProtocolMessage for PaxosMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            PaxosMessage::Prepare { ballot } => {
                buf.extend_from_slice(&TAG_PREPARE.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
            },
            PaxosMessage::Promise { ballot, accepted_bal, accepted_val } => {
                buf.extend_from_slice(&TAG_PROMISE.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
                buf.extend_from_slice(&accepted_bal.to_le_bytes());
                buf.extend_from_slice(&accepted_val.to_le_bytes());
            },
            PaxosMessage::Accept { ballot, value } => {
                buf.extend_from_slice(&TAG_ACCEPT.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            },
            PaxosMessage::Accepted { ballot, value } => {
                buf.extend_from_slice(&TAG_ACCEPTED.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
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
            TAG_PREPARE => {
                if data.len() < 16 {
                    return None;
                }
                let ballot = read_u64(data, 8);
                Some(PaxosMessage::Prepare { ballot })
            },
            TAG_PROMISE => {
                if data.len() < 32 {
                    return None;
                }
                let ballot = read_u64(data, 8);
                let accepted_bal = read_u64(data, 16);
                let accepted_val = read_u64(data, 24);
                Some(PaxosMessage::Promise { ballot, accepted_bal, accepted_val })
            },
            TAG_ACCEPT => {
                if data.len() < 24 {
                    return None;
                }
                let ballot = read_u64(data, 8);
                let value = read_u64(data, 16);
                Some(PaxosMessage::Accept { ballot, value })
            },
            TAG_ACCEPTED => {
                if data.len() < 24 {
                    return None;
                }
                let ballot = read_u64(data, 8);
                let value = read_u64(data, 16);
                Some(PaxosMessage::Accepted { ballot, value })
            },
            _ => None,
        }
    }
}
