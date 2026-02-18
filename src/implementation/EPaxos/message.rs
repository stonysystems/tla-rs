//! EPaxos protocol network messages.
//!
//! Maps the Egalitarian Paxos protocol actions to explicit network messages
//! for distributed deployment. Serialization uses simple u64 tag-based encoding.
//!
//! Message flow:
//!   Leader -> Replicas:  PreAccept { ballot, cmd, seq }        (fast path)
//!   Replica -> Leader:   PreAcceptOk { sender, seq, conflict } (fast-path response)
//!   Leader -> Replicas:  Accept { ballot, cmd, seq }           (slow path)
//!   Replica -> Leader:   AcceptOk { sender }                   (slow-path ack)
//!   Leader -> Replicas:  CommitMsg { cmd, seq }                (commit notification)

use crate::common::framework::protocol_trait::ProtocolMessage;

/// Network messages for the Egalitarian Paxos protocol.
pub enum EPaxosMessage {
    /// Fast-path: leader sends PreAccept with ballot, command, and sequence number.
    PreAccept { ballot: u64, cmd: u64, seq: u64 },
    /// Fast-path response: replica reports its local sequence and conflict status.
    PreAcceptOk { sender: u64, seq: u64, conflict: bool },
    /// Slow-path: leader sends Accept after conflict detected.
    Accept { ballot: u64, cmd: u64, seq: u64 },
    /// Slow-path acknowledgment from replica.
    AcceptOk { sender: u64 },
    /// Commit notification broadcast to all replicas.
    CommitMsg { cmd: u64, seq: u64 },
}

// Message tags for serialization
const TAG_PREACCEPT: u64 = 1;
const TAG_PREACCEPT_OK: u64 = 2;
const TAG_ACCEPT: u64 = 3;
const TAG_ACCEPT_OK: u64 = 4;
const TAG_COMMIT: u64 = 5;

impl ProtocolMessage for EPaxosMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            EPaxosMessage::PreAccept { ballot, cmd, seq } => {
                buf.extend_from_slice(&TAG_PREACCEPT.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
                buf.extend_from_slice(&cmd.to_le_bytes());
                buf.extend_from_slice(&seq.to_le_bytes());
            },
            EPaxosMessage::PreAcceptOk { sender, seq, conflict } => {
                buf.extend_from_slice(&TAG_PREACCEPT_OK.to_le_bytes());
                buf.extend_from_slice(&sender.to_le_bytes());
                buf.extend_from_slice(&seq.to_le_bytes());
                let conflict_val: u64 = if *conflict { 1 } else { 0 };
                buf.extend_from_slice(&conflict_val.to_le_bytes());
            },
            EPaxosMessage::Accept { ballot, cmd, seq } => {
                buf.extend_from_slice(&TAG_ACCEPT.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
                buf.extend_from_slice(&cmd.to_le_bytes());
                buf.extend_from_slice(&seq.to_le_bytes());
            },
            EPaxosMessage::AcceptOk { sender } => {
                buf.extend_from_slice(&TAG_ACCEPT_OK.to_le_bytes());
                buf.extend_from_slice(&sender.to_le_bytes());
            },
            EPaxosMessage::CommitMsg { cmd, seq } => {
                buf.extend_from_slice(&TAG_COMMIT.to_le_bytes());
                buf.extend_from_slice(&cmd.to_le_bytes());
                buf.extend_from_slice(&seq.to_le_bytes());
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
            TAG_PREACCEPT => {
                if data.len() < 32 {
                    return None;
                }
                let ballot = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11],
                    data[12], data[13], data[14], data[15],
                ]);
                let cmd = u64::from_le_bytes([
                    data[16], data[17], data[18], data[19],
                    data[20], data[21], data[22], data[23],
                ]);
                let seq = u64::from_le_bytes([
                    data[24], data[25], data[26], data[27],
                    data[28], data[29], data[30], data[31],
                ]);
                Some(EPaxosMessage::PreAccept { ballot, cmd, seq })
            },
            TAG_PREACCEPT_OK => {
                if data.len() < 32 {
                    return None;
                }
                let sender = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11],
                    data[12], data[13], data[14], data[15],
                ]);
                let seq = u64::from_le_bytes([
                    data[16], data[17], data[18], data[19],
                    data[20], data[21], data[22], data[23],
                ]);
                let conflict_val = u64::from_le_bytes([
                    data[24], data[25], data[26], data[27],
                    data[28], data[29], data[30], data[31],
                ]);
                let conflict = conflict_val != 0;
                Some(EPaxosMessage::PreAcceptOk { sender, seq, conflict })
            },
            TAG_ACCEPT => {
                if data.len() < 32 {
                    return None;
                }
                let ballot = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11],
                    data[12], data[13], data[14], data[15],
                ]);
                let cmd = u64::from_le_bytes([
                    data[16], data[17], data[18], data[19],
                    data[20], data[21], data[22], data[23],
                ]);
                let seq = u64::from_le_bytes([
                    data[24], data[25], data[26], data[27],
                    data[28], data[29], data[30], data[31],
                ]);
                Some(EPaxosMessage::Accept { ballot, cmd, seq })
            },
            TAG_ACCEPT_OK => {
                if data.len() < 16 {
                    return None;
                }
                let sender = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11],
                    data[12], data[13], data[14], data[15],
                ]);
                Some(EPaxosMessage::AcceptOk { sender })
            },
            TAG_COMMIT => {
                if data.len() < 24 {
                    return None;
                }
                let cmd = u64::from_le_bytes([
                    data[8], data[9], data[10], data[11],
                    data[12], data[13], data[14], data[15],
                ]);
                let seq = u64::from_le_bytes([
                    data[16], data[17], data[18], data[19],
                    data[20], data[21], data[22], data[23],
                ]);
                Some(EPaxosMessage::CommitMsg { cmd, seq })
            },
            _ => None,
        }
    }
}
