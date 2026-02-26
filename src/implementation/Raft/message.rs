//! Raft Consensus protocol network messages.

use crate::common::framework::protocol_trait::ProtocolMessage;

pub enum RaftMessage {
    /// Candidate requests votes from peers during an election.
    RequestVote {
        term: u64,
        candidate_id: u64,
        last_log_index: u64,
        last_log_term: u64,
    },
    /// Follower responds to a vote request.
    VoteResponse {
        term: u64,
        granted: bool,
        voter: u64,
    },
    /// Leader sends log entries (or heartbeats) to followers.
    AppendEntries {
        term: u64,
        leader_id: u64,
        prev_log_index: u64,
        prev_log_term: u64,
        value: u64,
        has_entry: bool,
        leader_commit: u64,
    },
    /// Follower responds to an append entries request.
    AppendResponse {
        term: u64,
        success: bool,
        match_index: u64,
        follower: u64,
    },
    /// External client submits a request to the cluster.
    ClientRequest {
        client_id: u64,
        seq_no: u64,
        value: u64,
    },
    /// Server responds to a client request.
    ClientResponse {
        client_id: u64,
        seq_no: u64,
        success: bool,
    },
}

// Message tags for serialization
const TAG_REQUEST_VOTE: u64 = 1;
const TAG_VOTE_RESPONSE: u64 = 2;
const TAG_APPEND_ENTRIES: u64 = 3;
const TAG_APPEND_RESPONSE: u64 = 4;
const TAG_CLIENT_REQUEST: u64 = 5;
const TAG_CLIENT_RESPONSE: u64 = 6;

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

impl ProtocolMessage for RaftMessage {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            RaftMessage::RequestVote {
                term,
                candidate_id,
                last_log_index,
                last_log_term,
            } => {
                buf.extend_from_slice(&TAG_REQUEST_VOTE.to_le_bytes());
                buf.extend_from_slice(&term.to_le_bytes());
                buf.extend_from_slice(&candidate_id.to_le_bytes());
                buf.extend_from_slice(&last_log_index.to_le_bytes());
                buf.extend_from_slice(&last_log_term.to_le_bytes());
            }
            RaftMessage::VoteResponse {
                term,
                granted,
                voter,
            } => {
                buf.extend_from_slice(&TAG_VOTE_RESPONSE.to_le_bytes());
                buf.extend_from_slice(&term.to_le_bytes());
                let granted_val: u64 = if *granted { 1 } else { 0 };
                buf.extend_from_slice(&granted_val.to_le_bytes());
                buf.extend_from_slice(&voter.to_le_bytes());
            }
            RaftMessage::AppendEntries {
                term,
                leader_id,
                prev_log_index,
                prev_log_term,
                value,
                has_entry,
                leader_commit,
            } => {
                buf.extend_from_slice(&TAG_APPEND_ENTRIES.to_le_bytes());
                buf.extend_from_slice(&term.to_le_bytes());
                buf.extend_from_slice(&leader_id.to_le_bytes());
                buf.extend_from_slice(&prev_log_index.to_le_bytes());
                buf.extend_from_slice(&prev_log_term.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
                let has_entry_val: u64 = if *has_entry { 1 } else { 0 };
                buf.extend_from_slice(&has_entry_val.to_le_bytes());
                buf.extend_from_slice(&leader_commit.to_le_bytes());
            }
            RaftMessage::AppendResponse {
                term,
                success,
                match_index,
                follower,
            } => {
                buf.extend_from_slice(&TAG_APPEND_RESPONSE.to_le_bytes());
                buf.extend_from_slice(&term.to_le_bytes());
                let success_val: u64 = if *success { 1 } else { 0 };
                buf.extend_from_slice(&success_val.to_le_bytes());
                buf.extend_from_slice(&match_index.to_le_bytes());
                buf.extend_from_slice(&follower.to_le_bytes());
            }
            RaftMessage::ClientRequest {
                client_id,
                seq_no,
                value,
            } => {
                buf.extend_from_slice(&TAG_CLIENT_REQUEST.to_le_bytes());
                buf.extend_from_slice(&client_id.to_le_bytes());
                buf.extend_from_slice(&seq_no.to_le_bytes());
                buf.extend_from_slice(&value.to_le_bytes());
            }
            RaftMessage::ClientResponse {
                client_id,
                seq_no,
                success,
            } => {
                buf.extend_from_slice(&TAG_CLIENT_RESPONSE.to_le_bytes());
                buf.extend_from_slice(&client_id.to_le_bytes());
                buf.extend_from_slice(&seq_no.to_le_bytes());
                let success_val: u64 = if *success { 1 } else { 0 };
                buf.extend_from_slice(&success_val.to_le_bytes());
            }
        }
    }

    fn deserialize_from_bytes(data: &Vec<u8>) -> Option<Self> {
        if data.len() < 8 {
            return None;
        }
        let tag = read_u64(data, 0);
        match tag {
            TAG_REQUEST_VOTE => {
                if data.len() < 40 {
                    return None;
                }
                let term = read_u64(data, 8);
                let candidate_id = read_u64(data, 16);
                let last_log_index = read_u64(data, 24);
                let last_log_term = read_u64(data, 32);
                Some(RaftMessage::RequestVote {
                    term,
                    candidate_id,
                    last_log_index,
                    last_log_term,
                })
            }
            TAG_VOTE_RESPONSE => {
                if data.len() < 32 {
                    return None;
                }
                let term = read_u64(data, 8);
                let granted = read_u64(data, 16) != 0;
                let voter = read_u64(data, 24);
                Some(RaftMessage::VoteResponse {
                    term,
                    granted,
                    voter,
                })
            }
            TAG_APPEND_ENTRIES => {
                if data.len() < 64 {
                    return None;
                }
                let term = read_u64(data, 8);
                let leader_id = read_u64(data, 16);
                let prev_log_index = read_u64(data, 24);
                let prev_log_term = read_u64(data, 32);
                let value = read_u64(data, 40);
                let has_entry = read_u64(data, 48) != 0;
                let leader_commit = read_u64(data, 56);
                Some(RaftMessage::AppendEntries {
                    term,
                    leader_id,
                    prev_log_index,
                    prev_log_term,
                    value,
                    has_entry,
                    leader_commit,
                })
            }
            TAG_APPEND_RESPONSE => {
                if data.len() < 40 {
                    return None;
                }
                let term = read_u64(data, 8);
                let success = read_u64(data, 16) != 0;
                let match_index = read_u64(data, 24);
                let follower = read_u64(data, 32);
                Some(RaftMessage::AppendResponse {
                    term,
                    success,
                    match_index,
                    follower,
                })
            }
            TAG_CLIENT_REQUEST => {
                if data.len() < 32 {
                    return None;
                }
                let client_id = read_u64(data, 8);
                let seq_no = read_u64(data, 16);
                let value = read_u64(data, 24);
                Some(RaftMessage::ClientRequest {
                    client_id,
                    seq_no,
                    value,
                })
            }
            TAG_CLIENT_RESPONSE => {
                if data.len() < 32 {
                    return None;
                }
                let client_id = read_u64(data, 8);
                let seq_no = read_u64(data, 16);
                let success = read_u64(data, 24) != 0;
                Some(RaftMessage::ClientResponse {
                    client_id,
                    seq_no,
                    success,
                })
            }
            _ => None,
        }
    }
}
