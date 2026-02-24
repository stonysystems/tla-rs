//! Vertical Paxos protocol network messages.
//!
//! Maps the spec's reconfigurable Paxos actions to explicit network messages
//! for distributed deployment. Serialization uses simple u64 tag-based encoding.
//!
//! Message flow:
//!   Proposer -> Acceptors: Prepare { ballot }                                 (Phase 1a)
//!   Acceptor -> Proposer:  Promise { ballot, v_bal, val, sender }             (Phase 1b)
//!   Proposer -> Acceptors: Accept { ballot, value }                           (Phase 2a)
//!   Acceptor -> Proposer:  AcceptOk { sender }                                (Phase 2b ack)
//!   Leader  -> All:        Commit { value }                                   (commit/learn)
//!   Old config -> New:     Sync { config, value }                             (reconfiguration sync)

use crate::common::framework::protocol_trait::ProtocolMessage;

/// Network messages for the Vertical Paxos protocol.
pub enum VerticalPaxosMessage {
    /// Phase 1a: Proposer sends Prepare with a ballot number.
    Prepare { ballot: u64 },
    /// Phase 1b: Acceptor promises not to accept lower ballots.
    /// Includes the highest ballot/value it has already accepted and the sender's node id.
    Promise {
        ballot: u64,
        v_bal: u64,
        val: u64,
        sender: u64,
    },
    /// Phase 2a: Proposer sends Accept with ballot and chosen value.
    Accept { ballot: u64, value: u64 },
    /// Phase 2b: Acceptor confirms it has accepted the proposal.
    AcceptOk { sender: u64 },
    /// Commit notification: a value has been decided.
    Commit { value: u64 },
    /// Reconfiguration sync: transfer state to a new configuration.
    Sync { config: u64, value: u64 },
}

// Message tags for serialization
const TAG_PREPARE: u64 = 1;
const TAG_PROMISE: u64 = 2;
const TAG_ACCEPT: u64 = 3;
const TAG_ACCEPT_OK: u64 = 4;
const TAG_COMMIT: u64 = 5;
const TAG_SYNC: u64 = 6;

impl ProtocolMessage for VerticalPaxosMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            VerticalPaxosMessage::Prepare { ballot } => {
                buf.extend_from_slice(&TAG_PREPARE.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
            }
            VerticalPaxosMessage::Promise {
                ballot,
                v_bal,
                val,
                sender,
            } => {
                buf.extend_from_slice(&TAG_PROMISE.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
                buf.extend_from_slice(&v_bal.to_le_bytes());
                buf.extend_from_slice(&val.to_le_bytes());
                buf.extend_from_slice(&sender.to_le_bytes());
            }
            VerticalPaxosMessage::Accept { ballot, value } => {
                buf.extend_from_slice(&TAG_ACCEPT.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            }
            VerticalPaxosMessage::AcceptOk { sender } => {
                buf.extend_from_slice(&TAG_ACCEPT_OK.to_le_bytes());
                buf.extend_from_slice(&sender.to_le_bytes());
            }
            VerticalPaxosMessage::Commit { value } => {
                buf.extend_from_slice(&TAG_COMMIT.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            }
            VerticalPaxosMessage::Sync { config, value } => {
                buf.extend_from_slice(&TAG_SYNC.to_le_bytes());
                buf.extend_from_slice(&config.to_le_bytes());
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
                Some(VerticalPaxosMessage::Prepare { ballot })
            }
            TAG_PROMISE => {
                if data.len() < 40 {
                    return None;
                }
                let ballot = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                let v_bal = u64::from_le_bytes([
                    data[16], data[17], data[18], data[19], data[20], data[21], data[22], data[23],
                ]);
                let val = u64::from_le_bytes([
                    data[24], data[25], data[26], data[27], data[28], data[29], data[30], data[31],
                ]);
                let sender = u64::from_le_bytes([
                    data[32], data[33], data[34], data[35], data[36], data[37], data[38], data[39],
                ]);
                Some(VerticalPaxosMessage::Promise {
                    ballot,
                    v_bal,
                    val,
                    sender,
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
                Some(VerticalPaxosMessage::Accept { ballot, value })
            }
            TAG_ACCEPT_OK => {
                if data.len() < 16 {
                    return None;
                }
                let sender = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                Some(VerticalPaxosMessage::AcceptOk { sender })
            }
            TAG_COMMIT => {
                if data.len() < 16 {
                    return None;
                }
                let value = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                Some(VerticalPaxosMessage::Commit { value })
            }
            TAG_SYNC => {
                if data.len() < 24 {
                    return None;
                }
                let config = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
                ]);
                let value = u64::from_le_bytes([
                    data[16], data[17], data[18], data[19], data[20], data[21], data[22], data[23],
                ]);
                Some(VerticalPaxosMessage::Sync { config, value })
            }
            _ => None,
        }
    }
}
