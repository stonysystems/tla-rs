//! LeaderElection protocol host implementation.
//!
//! Bridges the generic framework traits with the transpiler-generated
//! verified exec functions from election_gen. The host scheduler maps
//! incoming network messages to the appropriate C* function calls and
//! uses round-robin timer-driven actions for spontaneous transitions.
//!
//! The spec models a shared-state system with boolean message flags.
//! This implementation translates that into explicit network messages:
//! - Election messages are sent to all higher-ID peers
//! - Answer messages are sent back to the election initiator
//! - Coordinator messages are broadcast to all peers

use crate::common::framework::args_t::*;
use crate::common::framework::protocol_trait::*;
use crate::common::native::io_s::*;
use crate::generated::LeaderElection::election_gen;
use crate::generated::LeaderElection::types_gen::*;
use crate::implementation::LeaderElection::message::*;
use std::collections::HashSet;

/// LeaderElection protocol configuration.
pub struct LeaderElectionConfig {
    /// All peer endpoints (ordered by node ID; index = node ID).
    pub peers: Vec<EndPoint>,
    /// This node's index in the peers list (= its node ID).
    pub my_index: u64,
    /// The protocol constants (nodes set, num_nodes).
    pub constants: CConstants,
}

impl ProtocolConfig for LeaderElectionConfig {
    fn parse_config(me: &EndPoint, args: &Args) -> Option<Self> {
        // Expected args format: [endpoint0, endpoint1, ...]
        // Each endpoint is a peer; the index determines the node ID.
        // The endpoint matching `me` determines my_index.
        if args.len() < 2 {
            eprintln!("LeaderElection: need at least 2 args (peers)");
            return None;
        }

        let mut peers: Vec<EndPoint> = Vec::new();
        let mut my_index: Option<u64> = None;

        for i in 0..args.len() {
            let ep = EndPoint { id: args[i].clone() };
            if ep.id == me.id {
                my_index = Some(i as u64);
            }
            peers.push(ep);
        }

        let my_index = match my_index {
            Some(idx) => idx,
            None => {
                eprintln!("LeaderElection: own endpoint not found in args");
                return None;
            },
        };

        // Build the nodes set: all indices 0..n-1
        let mut nodes = HashSet::new();
        for i in 0..peers.len() {
            nodes.insert(i as u64);
        }
        let num_nodes = peers.len() as u64;

        let constants = CConstants { nodes, num_nodes };

        Some(LeaderElectionConfig {
            peers,
            my_index,
            constants,
        })
    }

    fn get_peers(&self) -> &Vec<EndPoint> {
        &self.peers
    }
}

/// The LeaderElection host wrapping protocol state.
pub struct LeaderElectionHost {
    /// The verified protocol state (shared-state model, local view).
    pub state: CState,
    /// This node's ID (same as config.my_index).
    pub my_node_id: u64,
    /// Round-robin action index for timer-driven actions.
    pub action_index: u64,
}

impl LeaderElectionHost {
    /// Handle an incoming Election message.
    ///
    /// If our ID is higher than the sender's, we respond with an Answer
    /// (suppressing their election) and also enter the election ourselves.
    /// This is the core of the Bully algorithm: higher-ID nodes bully
    /// lower-ID nodes out of their election attempts.
    fn handle_election(
        &mut self,
        config: &LeaderElectionConfig,
        sender: u64,
    ) -> StepResult<LeaderElectionMessage> {
        let my_id = self.my_node_id;

        // CSendAnswer requires:
        //   s.alive.contains(node)
        //   s.msgs_election == true
        //   node > s.msgs_election_sender
        //
        // We simulate having received the Election message by updating
        // the shared-state flags to reflect the message content.
        // First, set the election message flags so the guard can be checked.
        self.state.msgs_election = true;
        self.state.msgs_election_sender = sender;

        // Guard: we must be alive and have higher ID than sender
        if !self.state.alive.contains(&my_id) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if my_id <= sender {
            // We don't have a higher ID; ignore the election message.
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // All CSendAnswer preconditions are met: alive, msgs_election, my_id > sender
        self.state = election_gen::CSendAnswer(&self.state, &config.constants, &my_id);

        // Send Answer back to the sender to suppress their election
        if (sender as usize) < config.peers.len() {
            let dst = config.peers[sender as usize].clone_up_to_view();
            StepResult {
                ok: true,
                outbound: GenericOutbound::Send {
                    dst,
                    msg: LeaderElectionMessage::Answer { responder: my_id },
                },
            }
        } else {
            StepResult { ok: true, outbound: GenericOutbound::None }
        }
    }

    /// Handle an incoming Answer message.
    ///
    /// CReceiveAnswer requires:
    ///   s.alive.contains(node)
    ///   s.msgs_answer == true
    ///   s.waiting_answer == true
    ///   s.waiting_node == node
    ///
    /// Receiving an Answer means a higher-ID node is taking over the
    /// election, so we back off.
    fn handle_answer(
        &mut self,
        config: &LeaderElectionConfig,
        _responder: u64,
    ) -> StepResult<LeaderElectionMessage> {
        let my_id = self.my_node_id;

        // Set the answer flags to reflect the received message
        self.state.msgs_answer = true;
        self.state.msgs_answer_responder = _responder;

        // Check all guards for CReceiveAnswer
        if !self.state.alive.contains(&my_id) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !self.state.waiting_answer || self.state.waiting_node != my_id {
            // We were not waiting for an answer, ignore
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        self.state = election_gen::CReceiveAnswer(
            &self.state, &config.constants, &my_id,
        );

        StepResult { ok: true, outbound: GenericOutbound::None }
    }

    /// Handle an incoming Coordinator message.
    ///
    /// CReceiveCoordinator requires:
    ///   s.alive.contains(node)
    ///   s.msgs_coordinator == true
    ///
    /// The new leader is announced; we accept it.
    fn handle_coordinator(
        &mut self,
        config: &LeaderElectionConfig,
        leader: u64,
    ) -> StepResult<LeaderElectionMessage> {
        let my_id = self.my_node_id;

        // Set the coordinator flags to reflect the received message
        self.state.msgs_coordinator = true;
        self.state.msgs_coordinator_leader = leader;

        // Check guard for CReceiveCoordinator
        if !self.state.alive.contains(&my_id) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        self.state = election_gen::CReceiveCoordinator(
            &self.state, &config.constants, &my_id,
        );

        StepResult { ok: true, outbound: GenericOutbound::None }
    }

    /// Timer-driven actions, executed round-robin when no message arrives.
    ///
    /// Three actions are attempted in rotation:
    /// 0: CStartElection - periodic election trigger (leader heartbeat timeout)
    /// 1: CSendCoordinator - claim victory if waiting and no answer received
    /// 2: CDetectFailure - detect that the current leader has failed
    fn timer_step(
        &mut self,
        config: &LeaderElectionConfig,
    ) -> StepResult<LeaderElectionMessage> {
        let my_id = self.my_node_id;
        let result = match self.action_index % 3 {
            0 => self.try_start_election(config, my_id),
            1 => self.try_send_coordinator(config, my_id),
            _ => self.try_detect_failure(config, my_id),
        };
        self.action_index = self.action_index.wrapping_add(1);
        result
    }

    /// Try CStartElection: a node spontaneously starts an election.
    ///
    /// CStartElection requires:
    ///   s.alive.contains(node)
    ///
    /// In a distributed model, this is triggered by a heartbeat timeout
    /// or periodic check. We guard on: alive, and not already the leader
    /// (to avoid unnecessary elections).
    fn try_start_election(
        &mut self,
        config: &LeaderElectionConfig,
        my_id: u64,
    ) -> StepResult<LeaderElectionMessage> {
        // Guard: must be alive
        if !self.state.alive.contains(&my_id) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // Heuristic: don't start election if we already have a leader
        // and are not currently in an election. In a real system, this
        // would be triggered by a leader heartbeat timeout.
        if self.state.has_leader && self.state.alive.contains(&self.state.leader) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // Don't start if we are already electing
        if self.state.electing.contains(&my_id) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        self.state = election_gen::CStartElection(
            &self.state, &config.constants, &my_id,
        );

        // Send Election message to all nodes with higher IDs
        let higher_peers: Vec<EndPoint> = config.peers.iter()
            .enumerate()
            .filter(|(i, _)| (*i as u64) > my_id)
            .map(|(_, ep)| ep.clone_up_to_view())
            .collect();

        if higher_peers.is_empty() {
            // No higher-ID nodes: we win immediately.
            // Try to send Coordinator right away on the next timer tick.
            StepResult { ok: true, outbound: GenericOutbound::None }
        } else {
            StepResult {
                ok: true,
                outbound: GenericOutbound::Broadcast {
                    dsts: higher_peers,
                    msg: LeaderElectionMessage::Election { sender: my_id },
                },
            }
        }
    }

    /// Try CSendCoordinator: claim victory if we are in the electing set,
    /// waiting for an answer, and no answer has arrived.
    ///
    /// CSendCoordinator requires:
    ///   s.alive.contains(node)
    ///   s.electing.contains(node)
    ///   s.waiting_answer == true
    ///   s.waiting_node == node
    ///   s.msgs_answer == false
    ///
    /// In a real system, the "no answer received" condition is approximated
    /// by a timeout: if we sent Election messages and received no Answer
    /// within the timeout window, we declare ourselves the winner.
    fn try_send_coordinator(
        &mut self,
        config: &LeaderElectionConfig,
        my_id: u64,
    ) -> StepResult<LeaderElectionMessage> {
        // Check all CSendCoordinator guards
        if !self.state.alive.contains(&my_id) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !self.state.electing.contains(&my_id) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !self.state.waiting_answer || self.state.waiting_node != my_id {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if self.state.msgs_answer {
            // An answer is pending; we should process it first (handle_answer).
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        self.state = election_gen::CSendCoordinator(
            &self.state, &config.constants, &my_id,
        );

        // Broadcast Coordinator message to all peers
        let all_peers: Vec<EndPoint> = config.peers.iter()
            .enumerate()
            .filter(|(i, _)| (*i as u64) != my_id)
            .map(|(_, ep)| ep.clone_up_to_view())
            .collect();

        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: all_peers,
                msg: LeaderElectionMessage::Coordinator { leader: my_id },
            },
        }
    }

    /// Try CDetectFailure: detect that the current leader has failed.
    ///
    /// CDetectFailure requires:
    ///   s.alive.contains(node)
    ///   s.has_leader == true
    ///   !s.alive.contains(s.leader)
    ///
    /// In a distributed system, we cannot directly observe another node's
    /// liveness. We use a heuristic: the framework's timeout acts as a
    /// leader heartbeat timeout. If we have a leader but the timer fires
    /// repeatedly without hearing from it, we treat the leader as failed
    /// by removing it from our local alive set, then triggering the
    /// CDetectFailure action.
    ///
    /// Note: The spec's `!s.alive.contains(s.leader)` guard requires the
    /// leader to already be absent from the alive set. In a distributed
    /// model, this means we need to have previously marked the leader as
    /// failed (via CNodeFail or local timeout heuristic).
    fn try_detect_failure(
        &mut self,
        config: &LeaderElectionConfig,
        my_id: u64,
    ) -> StepResult<LeaderElectionMessage> {
        // Guard: must be alive and have a leader
        if !self.state.alive.contains(&my_id) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !self.state.has_leader {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // The spec requires !s.alive.contains(s.leader).
        // In a real distributed system, we would detect leader failure via
        // heartbeat timeout. If the leader is still in our alive set, we
        // cannot satisfy CDetectFailure's precondition directly. We skip
        // this action and rely on CStartElection (triggered by timeout
        // heuristics) for leader-less situations.
        if self.state.alive.contains(&self.state.leader) {
            // Leader still considered alive; cannot trigger CDetectFailure.
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // Leader is not in alive set: precondition satisfied.
        self.state = election_gen::CDetectFailure(
            &self.state, &config.constants, &my_id,
        );

        // Send Election message to all higher-ID nodes
        let higher_peers: Vec<EndPoint> = config.peers.iter()
            .enumerate()
            .filter(|(i, _)| (*i as u64) > my_id)
            .map(|(_, ep)| ep.clone_up_to_view())
            .collect();

        if higher_peers.is_empty() {
            StepResult { ok: true, outbound: GenericOutbound::None }
        } else {
            StepResult {
                ok: true,
                outbound: GenericOutbound::Broadcast {
                    dsts: higher_peers,
                    msg: LeaderElectionMessage::Election { sender: my_id },
                },
            }
        }
    }
}

impl ProtocolHost for LeaderElectionHost {
    type Msg = LeaderElectionMessage;
    type Cfg = LeaderElectionConfig;

    fn init(config: &Self::Cfg) -> Option<Self> {
        let state = election_gen::CInit(&config.constants);
        Some(LeaderElectionHost {
            state,
            my_node_id: config.my_index,
            action_index: 0,
        })
    }

    fn next(
        &mut self,
        config: &Self::Cfg,
        packet: Option<GenericPacket<Self::Msg>>,
    ) -> StepResult<Self::Msg> {
        if let Some(pkt) = packet {
            match pkt.msg {
                LeaderElectionMessage::Election { sender } => {
                    self.handle_election(config, sender)
                },
                LeaderElectionMessage::Answer { responder } => {
                    self.handle_answer(config, responder)
                },
                LeaderElectionMessage::Coordinator { leader } => {
                    self.handle_coordinator(config, leader)
                },
            }
        } else {
            // Timeout: run timer-driven actions
            self.timer_step(config)
        }
    }
}
