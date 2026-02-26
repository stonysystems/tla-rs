//! Raft protocol host implementation.
//!
//! Bridges the generic framework traits with the transpiler-generated
//! verified exec functions from raft_gen. The host scheduler maps incoming
//! network messages to the appropriate C* function calls and drives
//! timer-based leader actions (heartbeats, commit advancement) in a
//! round-robin fashion.
//!
//! The spec models messages via a sent_packets output parameter.
//! This implementation translates that into explicit network messages:
//! - RequestVote messages are broadcast to all peers on election timeout
//! - VoteResponse messages are sent back to the candidate
//! - AppendEntries messages are sent from leader to individual followers
//! - AppendResponse messages are sent back to the leader
//!
//! Role-based dispatch:
//!   Follower: receive RequestVote -> CGrantVote, receive AppendEntries -> CFollowerAppendEntries+reply, timeout -> CTimeout
//!   Candidate: receive VoteResponse -> CReceiveVoteGranted then CBecomeLeader, timeout -> CTimeout
//!   Leader: receive AppendResponse -> CHandleAppendResponse/Reject, timer -> CSendAppendEntries+CAdvanceCommitIndex

use crate::common::framework::args_t::*;
use crate::common::framework::protocol_trait::*;
use crate::common::native::io_s::*;
use crate::generated::Raft::raft_gen;
use crate::generated::Raft::types_gen::*;
use crate::implementation::Raft::message::*;
use std::collections::{HashMap, HashSet};

/// Raft protocol configuration.
pub struct RaftConfig {
    /// All peer endpoints (ordered by node index).
    pub peers: Vec<EndPoint>,
    /// This node's index in the peers list.
    pub my_index: u64,
    /// The protocol constants (servers set, quorum_size, my_id).
    pub constants: CConstants,
}

impl ProtocolConfig for RaftConfig {
    fn parse_config(me: &EndPoint, args: &Args) -> Option<Self> {
        // Expected args format: [endpoint0, endpoint1, ..., endpointN]
        // Each endpoint is a peer. The one matching `me` determines my_index.
        // Quorum size is majority: (n / 2) + 1.
        if args.len() < 2 {
            eprintln!("Raft: need at least 2 args (self + peers)");
            return None;
        }

        let mut peers: Vec<EndPoint> = Vec::new();
        let mut my_index: Option<u64> = None;

        for i in 0..args.len() {
            let ep = EndPoint {
                id: args[i].clone(),
            };
            if ep.id == me.id {
                my_index = Some(i as u64);
            }
            peers.push(ep);
        }

        let my_index = match my_index {
            Some(idx) => idx,
            None => {
                eprintln!("Raft: own endpoint not found in args");
                return None;
            }
        };

        let num_nodes = peers.len() as u64;
        let quorum_size = (num_nodes / 2) + 1;

        // Build servers set: all node indices
        let mut servers = HashSet::new();
        for i in 0..num_nodes {
            servers.insert(i);
        }

        let constants = CConstants {
            servers,
            quorum_size,
            my_id: my_index,
        };

        Some(RaftConfig {
            peers,
            my_index,
            constants,
        })
    }

    fn get_peers(&self) -> &Vec<EndPoint> {
        &self.peers
    }
}

/// The Raft host wrapping protocol state.
pub struct RaftHost {
    /// The verified protocol state.
    pub state: CState,
    /// Round-robin action index for timer-driven actions.
    pub action_index: u64,
    /// Client request counter (used to generate unique values).
    pub client_request_counter: u64,
}

impl RaftHost {
    /// Collect all peer endpoints except self for broadcasting.
    fn other_peers(config: &RaftConfig) -> Vec<EndPoint> {
        let mut others = Vec::new();
        for i in 0..config.peers.len() {
            if i as u64 != config.my_index {
                others.push(config.peers[i].clone_up_to_view());
            }
        }
        others
    }

    /// Get the endpoint for a specific node index.
    fn peer_endpoint(config: &RaftConfig, node_id: u64) -> Option<EndPoint> {
        if (node_id as usize) < config.peers.len() {
            Some(config.peers[node_id as usize].clone_up_to_view())
        } else {
            None
        }
    }

    /// Resolve the sender's node index from their endpoint.
    fn resolve_sender_index(config: &RaftConfig, src: &EndPoint) -> Option<u64> {
        for i in 0..config.peers.len() {
            if config.peers[i].id == src.id {
                return Some(i as u64);
            }
        }
        None
    }

    // ---------------------------------------------------------------
    // Follower actions
    // ---------------------------------------------------------------

    /// Handle an incoming RequestVote message (Follower).
    ///
    /// CGrantVote requires:
    ///   candidate_term >= current_term
    ///   !has_voted || voted_for == candidate_id
    ///   log-up-to-date check (candidate's log is at least as up-to-date)
    ///
    /// If all guards pass, grants the vote and sends VoteResponse back.
    /// If the candidate's term is higher, we also step down first.
    fn handle_request_vote(
        &mut self,
        config: &RaftConfig,
        src: &EndPoint,
        term: u64,
        candidate_id: u64,
        last_log_index: u64,
        last_log_term: u64,
    ) -> StepResult<RaftMessage> {
        // If the candidate's term is higher than ours, step down first
        if term > self.state.current_term && term < u64::MAX {
            let (new_state, _sent) = raft_gen::CStepDown(&self.state, &config.constants, &term);
            self.state = new_state;
        }

        // Guard: candidate_term >= current_term
        if term < self.state.current_term {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: !has_voted || voted_for == candidate_id
        if self.state.has_voted && self.state.voted_for != candidate_id {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: log up-to-date check
        // The candidate's log must be at least as up-to-date as ours.
        let my_last_log_term: u64 = if self.state.log.len() == 0 {
            0
        } else {
            self.state.log[self.state.log.len() - 1].term
        };
        let log_ok = last_log_term > my_last_log_term
            || (last_log_term == my_last_log_term && last_log_index >= self.state.log.len() as u64);
        if !log_ok {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) = raft_gen::CGrantVote(
            &self.state,
            &config.constants,
            &term,
            &last_log_term,
            &last_log_index,
            &candidate_id,
        );
        self.state = new_state;

        // Send VoteResponse (granted=true) back to candidate
        StepResult {
            ok: true,
            outbound: GenericOutbound::Send {
                dst: src.clone_up_to_view(),
                msg: RaftMessage::VoteResponse {
                    term: self.state.current_term,
                    granted: true,
                    voter: config.my_index,
                },
            },
        }
    }

    /// Handle an incoming AppendEntries message (Follower).
    ///
    /// CFollowerAppendEntries requires:
    ///   ae_term >= current_term
    ///   log.len() < u64::MAX
    ///
    /// Applies the append entries and sends an AppendResponse back to the leader.
    fn handle_append_entries(
        &mut self,
        config: &RaftConfig,
        src: &EndPoint,
        term: u64,
        leader_id: u64,
        prev_log_index: u64,
        prev_log_term: u64,
        value: u64,
        has_entry: bool,
        leader_commit: u64,
    ) -> StepResult<RaftMessage> {
        // If the leader's term is higher than ours, step down first
        if term > self.state.current_term && term < u64::MAX {
            let (new_state, _sent) = raft_gen::CStepDown(&self.state, &config.constants, &term);
            self.state = new_state;
        }

        // Guard: term >= current_term
        if term < self.state.current_term {
            // Reject: stale term. Send failure response.
            return StepResult {
                ok: true,
                outbound: GenericOutbound::Send {
                    dst: src.clone_up_to_view(),
                    msg: RaftMessage::AppendResponse {
                        term: self.state.current_term,
                        success: false,
                        match_index: 0,
                        follower: config.my_index,
                    },
                },
            };
        }

        // Guard: log.len() < u64::MAX
        if self.state.log.len() as u64 >= u64::MAX {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Compute the match_index for the response before updating state
        let resp_match_index = if has_entry {
            (self.state.log.len() as u64) + 1
        } else {
            self.state.log.len() as u64
        };

        let (new_state, _sent) = raft_gen::CFollowerAppendEntries(
            &self.state,
            &config.constants,
            &term,
            &leader_id,
            &prev_log_index,
            &prev_log_term,
            &value,
            has_entry,
            &leader_commit,
        );
        self.state = new_state;

        // Send AppendResponse back to the leader
        StepResult {
            ok: true,
            outbound: GenericOutbound::Send {
                dst: src.clone_up_to_view(),
                msg: RaftMessage::AppendResponse {
                    term,
                    success: true,
                    match_index: resp_match_index,
                    follower: config.my_index,
                },
            },
        }
    }

    /// Follower timeout: start an election by becoming a candidate.
    ///
    /// CTimeout requires:
    ///   role is Follower or Candidate
    ///   current_term < u64::MAX
    fn try_follower_timeout(&mut self, config: &RaftConfig) -> StepResult<RaftMessage> {
        // Guard: role is Follower or Candidate
        if !matches!(
            self.state.role,
            CServerRole::Follower | CServerRole::Candidate
        ) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: current_term < MAX
        if self.state.current_term >= u64::MAX {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let new_term = self.state.current_term + 1;
        let (new_state, _sent) = raft_gen::CTimeout(&self.state, &config.constants);
        self.state = new_state;

        // Broadcast RequestVote to all peers
        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: RaftMessage::RequestVote {
                    term: new_term,
                    candidate_id: config.my_index,
                    last_log_index: 0,
                    last_log_term: 0,
                },
            },
        }
    }

    // ---------------------------------------------------------------
    // Candidate actions
    // ---------------------------------------------------------------

    /// Handle an incoming VoteResponse message (Candidate).
    ///
    /// CReceiveVoteGranted requires:
    ///   role is Candidate
    ///   vote_granted == true
    ///   voter in servers
    ///
    /// After adding the vote, check if we have a quorum and become leader.
    fn handle_vote_response(
        &mut self,
        config: &RaftConfig,
        term: u64,
        granted: bool,
        voter: u64,
    ) -> StepResult<RaftMessage> {
        // If the response has a higher term, step down
        if term > self.state.current_term && term < u64::MAX {
            let (new_state, _sent) = raft_gen::CStepDown(&self.state, &config.constants, &term);
            self.state = new_state;
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must be a candidate
        if !matches!(self.state.role, CServerRole::Candidate) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: vote must be granted
        if !granted {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: voter must be in servers set
        if !config.constants.servers.contains(&voter) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) =
            raft_gen::CReceiveVoteGranted(&self.state, &config.constants, &term, granted, &voter);
        self.state = new_state;

        // Check if we now have enough votes to become leader.
        if matches!(self.state.role, CServerRole::Candidate)
            && self.state.votes_granted.len() as u64 >= config.constants.quorum_size
        {
            let (new_state, _sent) = raft_gen::CBecomeLeader(&self.state, &config.constants);
            self.state = new_state;
            eprintln!(
                "Raft: Node {} became LEADER for term {}",
                config.my_index, self.state.current_term
            );
        }

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    // ---------------------------------------------------------------
    // Leader actions
    // ---------------------------------------------------------------

    /// Handle an incoming AppendResponse message (Leader).
    ///
    /// Dispatches to CHandleAppendResponse (success) or CHandleAppendReject
    /// (failure) depending on the success field.
    fn handle_append_response(
        &mut self,
        config: &RaftConfig,
        term: u64,
        success: bool,
        match_index: u64,
        follower: u64,
    ) -> StepResult<RaftMessage> {
        // If the response has a higher term, step down
        if term > self.state.current_term && term < u64::MAX {
            let (new_state, _sent) = raft_gen::CStepDown(&self.state, &config.constants, &term);
            self.state = new_state;
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must be leader
        if !matches!(self.state.role, CServerRole::Leader) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: follower must be in servers set
        if !config.constants.servers.contains(&follower) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        if success {
            // CHandleAppendResponse additional guards:
            //   new_match_index >= 0 (always true for u64)
            //   new_match_index <= log.len() (spec domain)
            //   new_match_index < u64::MAX
            if match_index > self.state.log.len() as u64 {
                return StepResult {
                    ok: true,
                    outbound: GenericOutbound::None,
                };
            }
            if match_index >= u64::MAX {
                return StepResult {
                    ok: true,
                    outbound: GenericOutbound::None,
                };
            }

            let (new_state, _sent) = raft_gen::CHandleAppendResponse(
                &self.state,
                &config.constants,
                &term,
                success,
                &match_index,
                &follower,
                &follower,
                &match_index,
            );
            self.state = new_state;
        } else {
            let (new_state, _sent) = raft_gen::CHandleAppendReject(
                &self.state,
                &config.constants,
                &term,
                success,
                &match_index,
                &follower,
                &follower,
            );
            self.state = new_state;
        }

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    /// Timer action: Leader sends AppendEntries to each follower.
    ///
    /// CSendAppendEntries requires:
    ///   role is Leader
    ///   follower in servers
    ///
    /// Iterates over all peers and sends appropriate entries based on
    /// each follower's next_index.
    fn try_send_append_entries(&mut self, config: &RaftConfig) -> StepResult<RaftMessage> {
        // Guard: must be leader
        if !matches!(self.state.role, CServerRole::Leader) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let mut packets: Vec<GenericPacket<RaftMessage>> = Vec::new();

        for i in 0..config.peers.len() {
            let follower_id = i as u64;
            if follower_id == config.my_index {
                continue; // Don't send to self
            }

            if !config.constants.servers.contains(&follower_id) {
                continue;
            }

            // Determine what to send based on next_index for this follower
            let next_idx = match self.state.next_index.get(&follower_id) {
                Some(idx) => *idx,
                None => 0,
            };

            let log_len = self.state.log.len() as u64;
            let has_entry = next_idx < log_len;

            let entry_value = if has_entry {
                self.state.log[next_idx as usize].value
            } else {
                0
            };

            let prev_log_index = if next_idx > 0 { next_idx } else { 0 };
            let prev_log_term = if next_idx > 0 && (next_idx - 1) < log_len {
                self.state.log[(next_idx - 1) as usize].term
            } else {
                0
            };

            // Call CSendAppendEntries
            let (new_state, _sent) = raft_gen::CSendAppendEntries(
                &self.state,
                &config.constants,
                &follower_id,
                &entry_value,
                &prev_log_index,
                &prev_log_term,
                has_entry,
            );
            self.state = new_state;

            // Build the network message
            let dst = config.peers[i].clone_up_to_view();
            packets.push(GenericPacket {
                dst,
                src: config.peers[config.my_index as usize].clone_up_to_view(),
                msg: RaftMessage::AppendEntries {
                    term: self.state.current_term,
                    leader_id: config.my_index,
                    prev_log_index,
                    prev_log_term,
                    value: entry_value,
                    has_entry,
                    leader_commit: self.state.commit_index,
                },
            });
        }

        if packets.is_empty() {
            StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            }
        } else {
            StepResult {
                ok: true,
                outbound: GenericOutbound::Sequence { packets },
            }
        }
    }

    /// Timer action: Leader tries to advance the commit index.
    ///
    /// CAdvanceCommitIndex requires:
    ///   role is Leader
    ///   new_commit_index > commit_index
    ///   new_commit_index <= log.len()
    ///   log[new_commit_index - 1].term == current_term
    ///
    /// Scans match_index values to find the highest index replicated
    /// on a quorum of servers.
    fn try_advance_commit_index(&mut self, config: &RaftConfig) -> StepResult<RaftMessage> {
        // Guard: must be leader
        if !matches!(self.state.role, CServerRole::Leader) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let log_len = self.state.log.len() as u64;
        if log_len == 0 {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Find the highest index N such that:
        // 1. N > commit_index
        // 2. log[N-1].term == current_term
        // 3. A majority of servers have match_index >= N
        //
        // Scan from log_len down to commit_index + 1
        let mut best_n: Option<u64> = None;
        let mut n = log_len;
        while n > self.state.commit_index {
            // Check if log[n-1].term == current_term
            if self.state.log[(n - 1) as usize].term == self.state.current_term {
                // Count how many servers have match_index >= n
                // (including self, since leader always has all its own log entries)
                let mut count: u64 = 1; // count self
                for j in 0..config.peers.len() {
                    let peer_id = j as u64;
                    if peer_id == config.my_index {
                        continue;
                    }
                    if let Some(mi) = self.state.match_index.get(&peer_id) {
                        if *mi >= n {
                            count += 1;
                        }
                    }
                }
                if count >= config.constants.quorum_size {
                    best_n = Some(n);
                    break; // Found the highest such N
                }
            }
            n -= 1;
        }

        if let Some(new_commit_index) = best_n {
            let (new_state, _sent) =
                raft_gen::CAdvanceCommitIndex(&self.state, &config.constants, &new_commit_index);
            self.state = new_state;
            eprintln!(
                "Raft: Node {} advanced commit_index to {}",
                config.my_index, new_commit_index
            );
        }

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    /// Handle an incoming ClientRequest message from a benchmark client.
    ///
    /// If this node is the leader, appends the value to the log via
    /// CClientRequest and sends a ClientResponse(success=true) back.
    /// If not the leader, sends a ClientResponse(success=false) back.
    fn handle_client_request(
        &mut self,
        config: &RaftConfig,
        src: &EndPoint,
        client_id: u64,
        seq_no: u64,
        value: u64,
    ) -> StepResult<RaftMessage> {
        // Only the leader can serve client requests
        if !matches!(self.state.role, CServerRole::Leader) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::Send {
                    dst: src.clone_up_to_view(),
                    msg: RaftMessage::ClientResponse {
                        client_id,
                        seq_no,
                        success: false,
                    },
                },
            };
        }

        let (new_state, _sent) = raft_gen::CClientRequest(&self.state, &config.constants, &value);
        self.state = new_state;

        StepResult {
            ok: true,
            outbound: GenericOutbound::Send {
                dst: src.clone_up_to_view(),
                msg: RaftMessage::ClientResponse {
                    client_id,
                    seq_no,
                    success: true,
                },
            },
        }
    }

    /// Timer action: Leader processes a client request.
    ///
    /// CClientRequest requires:
    ///   role is Leader
    ///
    /// In a real system, client requests would arrive via a separate channel.
    /// Here we use the timer to simulate periodic client requests.
    fn try_client_request(&mut self, config: &RaftConfig) -> StepResult<RaftMessage> {
        // Guard: must be leader
        if !matches!(self.state.role, CServerRole::Leader) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Generate a unique value for this request
        self.client_request_counter = self.client_request_counter.wrapping_add(1);
        let value = self.client_request_counter;

        let (new_state, _sent) = raft_gen::CClientRequest(&self.state, &config.constants, &value);
        self.state = new_state;

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }
}

impl ProtocolHost for RaftHost {
    type Msg = RaftMessage;
    type Cfg = RaftConfig;

    fn init(config: &Self::Cfg) -> Option<Self> {
        let state = raft_gen::CInit(&config.constants);
        Some(RaftHost {
            state,
            action_index: 0,
            client_request_counter: 0,
        })
    }

    fn next(
        &mut self,
        config: &Self::Cfg,
        packet: Option<GenericPacket<Self::Msg>>,
    ) -> StepResult<Self::Msg> {
        // Handle incoming message based on current role
        if let Some(pkt) = packet {
            return match pkt.msg {
                RaftMessage::RequestVote {
                    term,
                    candidate_id,
                    last_log_index,
                    last_log_term,
                } => self.handle_request_vote(
                    config,
                    &pkt.src,
                    term,
                    candidate_id,
                    last_log_index,
                    last_log_term,
                ),
                RaftMessage::VoteResponse {
                    term,
                    granted,
                    voter,
                } => self.handle_vote_response(config, term, granted, voter),
                RaftMessage::AppendEntries {
                    term,
                    leader_id,
                    prev_log_index,
                    prev_log_term,
                    value,
                    has_entry,
                    leader_commit,
                } => self.handle_append_entries(
                    config,
                    &pkt.src,
                    term,
                    leader_id,
                    prev_log_index,
                    prev_log_term,
                    value,
                    has_entry,
                    leader_commit,
                ),
                RaftMessage::AppendResponse {
                    term,
                    success,
                    match_index,
                    follower,
                } => self.handle_append_response(config, term, success, match_index, follower),
                RaftMessage::ClientRequest {
                    client_id,
                    seq_no,
                    value,
                } => self.handle_client_request(config, &pkt.src, client_id, seq_no, value),
                RaftMessage::ClientResponse { .. } => {
                    // Servers ignore client responses (these are for clients only)
                    StepResult {
                        ok: true,
                        outbound: GenericOutbound::None,
                    }
                }
            };
        }

        // No message -- run timer-driven actions round-robin based on role
        let result = match &self.state.role {
            CServerRole::Follower | CServerRole::Candidate => {
                // Followers and candidates: election timeout
                self.try_follower_timeout(config)
            }
            CServerRole::Leader => {
                // Leader cycles through: send heartbeats, advance commit, client requests
                let result = match self.action_index % 3 {
                    0 => self.try_send_append_entries(config),
                    1 => self.try_advance_commit_index(config),
                    _ => self.try_client_request(config),
                };
                self.action_index = self.action_index.wrapping_add(1);
                result
            }
        };
        result
    }
}
