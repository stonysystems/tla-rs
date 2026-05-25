//! Egalitarian Paxos protocol network messages.

use crate::common::framework::protocol_trait::ProtocolMessage;

#[derive(Clone)]
pub enum EPaxosMessage {
    /// Fast-path: leader sends PreAccept with ballot, command, and sequence number.
    PreAccept {
        ballot: u64,
        cmd: u64,
        seq: u64,
    },
    /// Fast-path response: replica reports its local sequence and conflict status.
    PreAcceptOk {
        sender: u64,
        seq: u64,
        conflict: bool,
    },
    /// Slow-path: leader sends Accept after conflict detected.
    Accept {
        ballot: u64,
        cmd: u64,
        seq: u64,
    },
    /// Slow-path acknowledgment from replica.
    AcceptOk {
        sender: u64,
    },
    /// Commit notification broadcast to all replicas.
    CommitMsg {
        cmd: u64,
        seq: u64,
    },
    /// Client sends a command request to a replica.
    ClientRequest {
        cmd: u64,
    },
    /// Leader replies to client after executing a committed command.
    ClientReply {
        cmd: u64,
    },
}

// Message tags for serialization
const TAG_PRE_ACCEPT: u64 = 1;
const TAG_PRE_ACCEPT_OK: u64 = 2;
const TAG_ACCEPT: u64 = 3;
const TAG_ACCEPT_OK: u64 = 4;
const TAG_COMMIT_MSG: u64 = 5;
const TAG_CLIENT_REQUEST: u64 = 6;
const TAG_CLIENT_REPLY: u64 = 7;

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

impl ProtocolMessage for EPaxosMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            EPaxosMessage::PreAccept { ballot, cmd, seq } => {
                buf.extend_from_slice(&TAG_PRE_ACCEPT.to_le_bytes());
                buf.extend_from_slice(&ballot.to_le_bytes());
                buf.extend_from_slice(&cmd.to_le_bytes());
                buf.extend_from_slice(&seq.to_le_bytes());
            },
            EPaxosMessage::PreAcceptOk { sender, seq, conflict } => {
                buf.extend_from_slice(&TAG_PRE_ACCEPT_OK.to_le_bytes());
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
                buf.extend_from_slice(&TAG_COMMIT_MSG.to_le_bytes());
                buf.extend_from_slice(&cmd.to_le_bytes());
                buf.extend_from_slice(&seq.to_le_bytes());
            },
            EPaxosMessage::ClientRequest { cmd } => {
                buf.extend_from_slice(&TAG_CLIENT_REQUEST.to_le_bytes());
                buf.extend_from_slice(&cmd.to_le_bytes());
            },
            EPaxosMessage::ClientReply { cmd } => {
                buf.extend_from_slice(&TAG_CLIENT_REPLY.to_le_bytes());
                buf.extend_from_slice(&cmd.to_le_bytes());
            },
        }
    }

    fn deserialize_from_bytes(data: &Vec<u8>) -> Option<Self> {
        if data.len() < 8 {
            return None;
        }
        let tag = read_u64(data, 0);
        match tag {
            TAG_PRE_ACCEPT => {
                if data.len() < 32 {
                    return None;
                }
                let ballot = read_u64(data, 8);
                let cmd = read_u64(data, 16);
                let seq = read_u64(data, 24);
                Some(EPaxosMessage::PreAccept { ballot, cmd, seq })
            },
            TAG_PRE_ACCEPT_OK => {
                if data.len() < 32 {
                    return None;
                }
                let sender = read_u64(data, 8);
                let seq = read_u64(data, 16);
                let conflict = read_u64(data, 24) != 0;
                Some(EPaxosMessage::PreAcceptOk { sender, seq, conflict })
            },
            TAG_ACCEPT => {
                if data.len() < 32 {
                    return None;
                }
                let ballot = read_u64(data, 8);
                let cmd = read_u64(data, 16);
                let seq = read_u64(data, 24);
                Some(EPaxosMessage::Accept { ballot, cmd, seq })
            },
            TAG_ACCEPT_OK => {
                if data.len() < 16 {
                    return None;
                }
                let sender = read_u64(data, 8);
                Some(EPaxosMessage::AcceptOk { sender })
            },
            TAG_COMMIT_MSG => {
                if data.len() < 24 {
                    return None;
                }
                let cmd = read_u64(data, 8);
                let seq = read_u64(data, 16);
                Some(EPaxosMessage::CommitMsg { cmd, seq })
            },
            TAG_CLIENT_REQUEST => {
                if data.len() < 16 {
                    return None;
                }
                let cmd = read_u64(data, 8);
                Some(EPaxosMessage::ClientRequest { cmd })
            },
            TAG_CLIENT_REPLY => {
                if data.len() < 16 {
                    return None;
                }
                let cmd = read_u64(data, 8);
                Some(EPaxosMessage::ClientReply { cmd })
            },
            _ => None,
        }
    }
}
