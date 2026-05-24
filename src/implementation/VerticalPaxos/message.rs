//! Vertical Paxos protocol network messages.

use crate::common::framework::protocol_trait::ProtocolMessage;

#[derive(Clone)]
pub enum VerticalPaxosMessage {
    /// Phase 1a: Proposer sends Prepare.
    Prepare {
        ballot: u64,
    },
    /// Phase 1b: Acceptor promises with accepted ballot/value.
    Promise {
        ballot: u64,
        v_bal: u64,
        val: u64,
        sender: u64,
    },
    /// Phase 2a: Proposer sends Accept.
    Accept {
        ballot: u64,
        value: u64,
    },
    /// Phase 2b: Acceptor confirms acceptance.
    AcceptOk {
        sender: u64,
    },
    /// Commit notification.
    Commit {
        value: u64,
    },
    /// Reconfiguration sync message.
    Sync {
        config: u64,
        value: u64,
    },
}

// Message tags for serialization
const TAG_PREPARE: u64 = 1;
const TAG_PROMISE: u64 = 2;
const TAG_ACCEPT: u64 = 3;
const TAG_ACCEPT_OK: u64 = 4;
const TAG_COMMIT: u64 = 5;
const TAG_SYNC: u64 = 6;

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

impl ProtocolMessage for VerticalPaxosMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            VerticalPaxosMessage::Prepare { ballot } => {
                buf.extend_from_slice(&TAG_PREPARE.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
            },
            VerticalPaxosMessage::Promise { ballot, v_bal, val, sender } => {
                buf.extend_from_slice(&TAG_PROMISE.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
                buf.extend_from_slice(&v_bal.to_le_bytes());
                buf.extend_from_slice(&val.to_le_bytes());
                buf.extend_from_slice(&sender.to_le_bytes());
            },
            VerticalPaxosMessage::Accept { ballot, value } => {
                buf.extend_from_slice(&TAG_ACCEPT.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            },
            VerticalPaxosMessage::AcceptOk { sender } => {
                buf.extend_from_slice(&TAG_ACCEPT_OK.to_le_bytes());
                buf.extend_from_slice(&sender.to_le_bytes());
            },
            VerticalPaxosMessage::Commit { value } => {
                buf.extend_from_slice(&TAG_COMMIT.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            },
            VerticalPaxosMessage::Sync { config, value } => {
                buf.extend_from_slice(&TAG_SYNC.to_le_bytes());
                buf.extend_from_slice(&config.to_le_bytes());
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
                Some(VerticalPaxosMessage::Prepare { ballot })
            },
            TAG_PROMISE => {
                if data.len() < 40 {
                    return None;
                }
                let ballot = read_u64(data, 8);
                let v_bal = read_u64(data, 16);
                let val = read_u64(data, 24);
                let sender = read_u64(data, 32);
                Some(VerticalPaxosMessage::Promise { ballot, v_bal, val, sender })
            },
            TAG_ACCEPT => {
                if data.len() < 24 {
                    return None;
                }
                let ballot = read_u64(data, 8);
                let value = read_u64(data, 16);
                Some(VerticalPaxosMessage::Accept { ballot, value })
            },
            TAG_ACCEPT_OK => {
                if data.len() < 16 {
                    return None;
                }
                let sender = read_u64(data, 8);
                Some(VerticalPaxosMessage::AcceptOk { sender })
            },
            TAG_COMMIT => {
                if data.len() < 16 {
                    return None;
                }
                let value = read_u64(data, 8);
                Some(VerticalPaxosMessage::Commit { value })
            },
            TAG_SYNC => {
                if data.len() < 24 {
                    return None;
                }
                let config = read_u64(data, 8);
                let value = read_u64(data, 16);
                Some(VerticalPaxosMessage::Sync { config, value })
            },
            _ => None,
        }
    }
}
