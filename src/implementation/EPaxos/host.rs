//! EPaxos protocol host implementation.
//!
//! Bridges the generic framework traits with the transpiler-generated
//! verified exec functions. The host scheduler maps incoming network
//! messages to the appropriate C* function calls and drives timer-based
//! actions (Propose, FastCommit, StartAccept, SlowCommit, Execute,
//! NewInstance, Recover) in a round-robin fashion.
//!
//! EPaxos uses two commit paths:
//!   Fast path: PreAccept -> PreAcceptOk (fast quorum, no conflict) -> FastCommit
//!   Slow path: PreAccept -> PreAcceptOk (conflict) -> StartAccept -> AcceptOk -> SlowCommit
//!
//! The spec models messages as sent_packets output parameters. This
//! implementation translates that into explicit network messages.

use crate::common::framework::args_t::*;
use crate::common::framework::protocol_trait::*;
use crate::common::native::io_s::*;
use crate::generated::EPaxos::epaxos_gen;
use crate::generated::EPaxos::types_gen::*;
use crate::implementation::EPaxos::message::*;
use std::collections::HashSet;
use std::time::Instant;

/// EPaxos protocol configuration.
pub struct EPaxosConfig {
    /// All peer endpoints (ordered by node index).
    pub peers: Vec<EndPoint>,
    /// This node's index in the peers list.
    pub my_index: u64,
    /// The protocol constants (quorum sizes, node id, num replicas).
    pub constants: CConstants,
}

impl ProtocolConfig for EPaxosConfig {
    fn parse_config(me: &EndPoint, args: &Args) -> Option<Self> {
        // Expected args format: [endpoint0, endpoint1, ..., endpointN]
        // Each endpoint is a peer. The one matching `me` determines my_index.
        // quorum_size = (n / 2) + 1 (classic majority)
        // fast_quorum_size = n - 1 (EPaxos fast path requires all but one)
        if args.len() < 3 {
            eprintln!("EPaxos: need at least 3 args (self + 2 peers, minimum 3 nodes)");
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
                eprintln!("EPaxos: own endpoint not found in args");
                return None;
            }
        };

        let num_nodes = peers.len() as u64;
        let quorum_size = (num_nodes / 2) + 1;
        // EPaxos fast quorum: all replicas except possibly one (n - 1 for fast path)
        let fast_quorum_size = num_nodes - 1;

        let constants = CConstants {
            num_replicas: num_nodes,
            fast_quorum_size,
            quorum_size,
            my_id: my_index,
        };

        Some(EPaxosConfig {
            peers,
            my_index,
            constants,
        })
    }

    fn get_peers(&self) -> &Vec<EndPoint> {
        &self.peers
    }
}

/// The EPaxos host wrapping protocol state.
pub struct EPaxosHost {
    /// The verified protocol state.
    pub state: CState,
    /// Round-robin action index for timer-driven actions.
    pub action_index: u64,
    /// Counter for generating unique ballot numbers.
    /// Ballots are assigned as: ballot_counter * num_nodes + my_index
    /// to ensure globally unique, monotonically increasing ballots per node.
    pub ballot_counter: u64,
    /// Counter for generating proposal values.
    pub propose_counter: u64,
    /// Timestamp of last metrics output (for periodic throughput reporting).
    last_metrics_time: Instant,
    /// Committed count at last metrics output (for delta computation).
    last_metrics_committed: u64,
    /// Client endpoint for the current pending command (if any).
    pending_client: Option<EndPoint>,
}

impl EPaxosHost {
    /// Generate the next ballot number for this node.
    /// Uses the pattern: ballot = counter * num_nodes + my_index
    fn next_ballot(&mut self, config: &EPaxosConfig) -> u64 {
        self.ballot_counter = self.ballot_counter.wrapping_add(1);
        self.ballot_counter
            .wrapping_mul(config.peers.len() as u64)
            .wrapping_add(config.my_index)
    }

    /// Collect all peer endpoints except self for broadcasting.
    fn other_peers(config: &EPaxosConfig) -> Vec<EndPoint> {
        let mut others = Vec::new();
        for i in 0..config.peers.len() {
            if i as u64 != config.my_index {
                others.push(config.peers[i].clone_up_to_view());
            }
        }
        others
    }

    /// Resolve the sender's node index from their endpoint.
    fn resolve_sender_index(config: &EPaxosConfig, src: &EndPoint) -> Option<u64> {
        for i in 0..config.peers.len() {
            if config.peers[i].id == src.id {
                return Some(i as u64);
            }
        }
        None
    }

    // ---------------------------------------------------------------
    // Message-driven actions (called when a packet arrives)
    // ---------------------------------------------------------------

    /// Handle an incoming PreAccept message.
    /// Non-leader replicas respond with PreAcceptOk, reporting local conflict
    /// and sequence number.
    fn handle_preaccept(
        &mut self,
        config: &EPaxosConfig,
        src: &EndPoint,
        _ballot: u64,
        _cmd: u64,
        _seq: u64,
    ) -> StepResult<EPaxosMessage> {
        // Determine local conflict and sequence: for simplicity, use the
        // committed_count as a proxy for local sequence knowledge.
        let local_conflict = false;
        let local_seq = self.state.committed_count;

        let (new_state, _sent) = epaxos_gen::CSendPreAcceptOk(
            &self.state,
            &config.constants,
            local_conflict,
            &local_seq,
        );
        self.state = new_state;

        StepResult {
            ok: true,
            outbound: GenericOutbound::Send {
                dst: src.clone_up_to_view(),
                msg: EPaxosMessage::PreAcceptOk {
                    sender: config.my_index,
                    seq: local_seq,
                    conflict: local_conflict,
                },
            },
        }
    }

    /// Handle an incoming PreAcceptOk message.
    /// The leader records responses and updates conflict/sequence state.
    fn handle_preaccept_ok(
        &mut self,
        config: &EPaxosConfig,
        sender_id: u64,
        seq: u64,
        conflict: bool,
    ) -> StepResult<EPaxosMessage> {
        // Guard: must be leader in PreAccepted phase
        if !self.state.is_leader {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }
        if !matches!(self.state.phase, CInstancePhase::PreAccepted) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must not have already received from this sender
        if self.state.preaccept_senders.contains(&sender_id) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: dep_count overflow protection
        if conflict && self.state.dep_count >= u64::MAX {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) = epaxos_gen::CReceivePreAcceptOk(
            &self.state,
            &config.constants,
            &sender_id,
            &seq,
            conflict,
        );
        self.state = new_state;

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    /// Handle an incoming Accept message (slow path).
    /// Replicas respond with AcceptOk.
    fn handle_accept(
        &mut self,
        config: &EPaxosConfig,
        src: &EndPoint,
        _ballot: u64,
        _cmd: u64,
        _seq: u64,
    ) -> StepResult<EPaxosMessage> {
        let (new_state, _sent) = epaxos_gen::CSendAcceptOk(&self.state, &config.constants);
        self.state = new_state;

        StepResult {
            ok: true,
            outbound: GenericOutbound::Send {
                dst: src.clone_up_to_view(),
                msg: EPaxosMessage::AcceptOk {
                    sender: config.my_index,
                },
            },
        }
    }

    /// Handle an incoming AcceptOk message (slow path).
    /// The leader records acceptance acknowledgments.
    fn handle_accept_ok(
        &mut self,
        config: &EPaxosConfig,
        sender_id: u64,
    ) -> StepResult<EPaxosMessage> {
        // Guard: must be leader in Accepted phase
        if !self.state.is_leader {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }
        if !matches!(self.state.phase, CInstancePhase::Accepted) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must not have already received from this sender
        if self.state.accept_senders.contains(&sender_id) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) =
            epaxos_gen::CReceiveAcceptOk(&self.state, &config.constants, &sender_id);
        self.state = new_state;

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    /// Handle an incoming CommitMsg. No state transition needed beyond
    /// acknowledging the commit (the spec does not define a receiver action).
    fn handle_commit(
        &mut self,
        _config: &EPaxosConfig,
        _cmd: u64,
        _seq: u64,
    ) -> StepResult<EPaxosMessage> {
        // CommitMsg is informational; no protocol action required.
        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    // ---------------------------------------------------------------
    // Timer-driven actions (called on timeout, round-robin)
    // ---------------------------------------------------------------

    /// Propose a new command, driven by a ClientRequest.
    /// Only fires when the instance is Empty.
    fn try_propose(&mut self, config: &EPaxosConfig, value: u64, client_ep: Option<EndPoint>) -> StepResult<EPaxosMessage> {
        // Guard: phase must be Empty
        if !matches!(self.state.phase, CInstancePhase::Empty) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: committed_count overflow protection
        if self.state.committed_count >= u64::MAX {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        self.pending_client = client_ep;

        let (new_state, _sent) = epaxos_gen::CPropose(&self.state, &config.constants, &value);
        self.state = new_state;

        // Broadcast PreAccept to all other replicas
        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: EPaxosMessage::PreAccept {
                    ballot: self.state.ballot,
                    cmd: self.state.cmd,
                    seq: self.state.seq,
                },
            },
        }
    }

    /// Timer action: Try fast-path commit.
    /// Fires when the leader has a fast quorum of PreAcceptOk with no conflicts.
    fn try_fast_commit(&mut self, config: &EPaxosConfig) -> StepResult<EPaxosMessage> {
        // Guard: must be leader in PreAccepted phase
        if !self.state.is_leader {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }
        if !matches!(self.state.phase, CInstancePhase::PreAccepted) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must have fast quorum
        if (self.state.preaccept_senders.len() as u64) < config.constants.fast_quorum_size {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: no conflicts detected
        if self.state.has_conflict {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: committed_count overflow protection
        if self.state.committed_count >= u64::MAX {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) = epaxos_gen::CFastCommit(&self.state, &config.constants);
        self.state = new_state;

        eprintln!(
            "EPaxos: FAST COMMIT cmd={} seq={}",
            self.state.cmd, self.state.seq
        );

        // Broadcast commit to all replicas
        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: EPaxosMessage::CommitMsg {
                    cmd: self.state.cmd,
                    seq: self.state.seq,
                },
            },
        }
    }

    /// Timer action: Start slow-path Accept phase.
    /// Fires when the leader has a quorum of PreAcceptOk but with conflicts.
    fn try_start_accept(&mut self, config: &EPaxosConfig) -> StepResult<EPaxosMessage> {
        // Guard: must be leader in PreAccepted phase
        if !self.state.is_leader {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }
        if !matches!(self.state.phase, CInstancePhase::PreAccepted) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must have at least quorum_size responses
        if (self.state.preaccept_senders.len() as u64) < config.constants.fast_quorum_size {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must have conflicts
        if !self.state.has_conflict {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) = epaxos_gen::CStartAccept(&self.state, &config.constants);
        self.state = new_state;

        // Broadcast Accept to all other replicas
        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: EPaxosMessage::Accept {
                    ballot: self.state.ballot,
                    cmd: self.state.cmd,
                    seq: self.state.seq,
                },
            },
        }
    }

    /// Timer action: Slow-path commit.
    /// Fires when the leader in Accepted phase has a classic quorum of AcceptOk.
    fn try_slow_commit(&mut self, config: &EPaxosConfig) -> StepResult<EPaxosMessage> {
        // Guard: must be leader in Accepted phase
        if !self.state.is_leader {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }
        if !matches!(self.state.phase, CInstancePhase::Accepted) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must have classic quorum of accept acks
        if (self.state.accept_senders.len() as u64) < config.constants.quorum_size {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: committed_count overflow protection
        if self.state.committed_count >= u64::MAX {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) = epaxos_gen::CSlowCommit(&self.state, &config.constants);
        self.state = new_state;

        eprintln!(
            "EPaxos: SLOW COMMIT cmd={} seq={}",
            self.state.cmd, self.state.seq
        );

        // Broadcast commit to all replicas
        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: EPaxosMessage::CommitMsg {
                    cmd: self.state.cmd,
                    seq: self.state.seq,
                },
            },
        }
    }

    /// Timer action: Execute a committed command.
    /// Fires when the instance is in Committed phase.
    fn try_execute(&mut self, config: &EPaxosConfig) -> StepResult<EPaxosMessage> {
        // Guard: phase must be Committed
        if !matches!(self.state.phase, CInstancePhase::Committed) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: executed_count overflow protection
        if self.state.executed_count >= u64::MAX {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let cmd = self.state.cmd;
        let client_ep = if self.state.is_leader { self.pending_client.take() } else { None };

        let (new_state, _sent) = epaxos_gen::CExecute(&self.state, &config.constants);
        self.state = new_state;

        eprintln!(
            "EPaxos: EXECUTED cmd={} seq={}",
            self.state.cmd, self.state.seq
        );

        // Leader sends ClientReply to the requesting client
        match client_ep {
            Some(dst) => StepResult {
                ok: true,
                outbound: GenericOutbound::Send {
                    dst,
                    msg: EPaxosMessage::ClientReply { cmd },
                },
            },
            None => StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            },
        }
    }

    /// Timer action: Start a new instance after execution.
    /// Fires when the instance is in Executed phase.
    fn try_new_instance(&mut self, config: &EPaxosConfig) -> StepResult<EPaxosMessage> {
        // Guard: phase must be Executed
        if !matches!(self.state.phase, CInstancePhase::Executed) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) = epaxos_gen::CNewInstance(&self.state, &config.constants);
        self.state = new_state;

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    /// Timer action: Recover a stalled instance by proposing a new ballot.
    /// Fires when phase is PreAccepted or Accepted (not yet committed/executed).
    fn try_recover(&mut self, config: &EPaxosConfig) -> StepResult<EPaxosMessage> {
        // Guard: phase must be PreAccepted or Accepted
        if !matches!(
            self.state.phase,
            CInstancePhase::PreAccepted | CInstancePhase::Accepted
        ) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let new_ballot = self.next_ballot(config);

        // Guard: new ballot must be strictly greater than current
        if new_ballot <= self.state.ballot {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) = epaxos_gen::CRecover(&self.state, &config.constants, &new_ballot);
        self.state = new_state;

        // Broadcast PreAccept with new ballot to all replicas
        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: EPaxosMessage::PreAccept {
                    ballot: self.state.ballot,
                    cmd: self.state.cmd,
                    seq: self.state.seq,
                },
            },
        }
    }
}

impl ProtocolHost for EPaxosHost {
    type Msg = EPaxosMessage;
    type Cfg = EPaxosConfig;

    fn init(config: &Self::Cfg) -> Option<Self> {
        let state = epaxos_gen::CInit(&config.constants);
        Some(EPaxosHost {
            state,
            action_index: 0,
            ballot_counter: 0,
            propose_counter: 0,
            last_metrics_time: Instant::now(),
            last_metrics_committed: 0,
            pending_client: None,
        })
    }

    fn next(
        &mut self,
        config: &Self::Cfg,
        packet: Option<GenericPacket<Self::Msg>>,
    ) -> StepResult<Self::Msg> {
        // Periodic metrics output (every 1 second)
        let now = Instant::now();
        let elapsed = now.duration_since(self.last_metrics_time);
        if elapsed.as_secs() >= 1 {
            let committed = self.state.committed_count;
            let delta = committed - self.last_metrics_committed;
            let elapsed_secs = elapsed.as_secs_f64();
            eprintln!(
                "[METRICS] committed={} delta={} elapsed={:.2}s throughput={:.1} ops/s",
                committed,
                delta,
                elapsed_secs,
                delta as f64 / elapsed_secs,
            );
            self.last_metrics_time = now;
            self.last_metrics_committed = committed;
        }

        // Handle incoming message
        if let Some(pkt) = packet {
            let sender_id = Self::resolve_sender_index(config, &pkt.src);
            let _sender_id = match sender_id {
                Some(id) => id,
                None => {
                    // Unknown sender, ignore
                    return StepResult {
                        ok: true,
                        outbound: GenericOutbound::None,
                    };
                }
            };

            return match pkt.msg {
                EPaxosMessage::PreAccept { ballot, cmd, seq } => {
                    self.handle_preaccept(config, &pkt.src, ballot, cmd, seq)
                }
                EPaxosMessage::PreAcceptOk {
                    sender,
                    seq,
                    conflict,
                } => self.handle_preaccept_ok(config, sender, seq, conflict),
                EPaxosMessage::Accept { ballot, cmd, seq } => {
                    self.handle_accept(config, &pkt.src, ballot, cmd, seq)
                }
                EPaxosMessage::AcceptOk { sender } => self.handle_accept_ok(config, sender),
                EPaxosMessage::CommitMsg { cmd, seq } => self.handle_commit(config, cmd, seq),
                EPaxosMessage::ClientRequest { cmd } => {
                    self.try_propose(config, cmd, Some(pkt.src))
                }
                EPaxosMessage::ClientReply { .. } => {
                    // ClientReply is outbound-only; ignore if received
                    StepResult {
                        ok: true,
                        outbound: GenericOutbound::None,
                    }
                }
            };
        }

        // No message -- run timer-driven actions round-robin
        // Cycle through: FastCommit, StartAccept, SlowCommit,
        //                Execute, NewInstance, Recover
        // (Propose is now message-driven via ClientRequest)
        let result = match self.action_index % 6 {
            0 => self.try_fast_commit(config),
            1 => self.try_start_accept(config),
            2 => self.try_slow_commit(config),
            3 => self.try_execute(config),
            4 => self.try_new_instance(config),
            _ => self.try_recover(config),
        };
        self.action_index = self.action_index.wrapping_add(1);
        result
    }
}
