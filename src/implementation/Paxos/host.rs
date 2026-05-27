//! Paxos protocol host implementation.
//!
//! Bridges the generic framework traits with the transpiler-generated
//! verified exec functions. The host scheduler maps incoming network
//! messages to the appropriate C* function calls and drives timer-based
//! proposer actions (Send1a, Send2a, Learn) in a round-robin fashion.

use crate::common::framework::args_t::*;
use crate::common::framework::protocol_trait::*;
use crate::common::native::io_s::*;
use crate::generated::Paxos::paxos_gen;
use crate::generated::Paxos::types_gen::*;
use crate::implementation::Paxos::message::*;
use std::collections::HashSet;

/// Paxos protocol configuration.
pub struct PaxosConfig {
    /// All peer endpoints (ordered by node index).
    pub peers: Vec<EndPoint>,
    /// This node's index in the peers list.
    pub my_index: u64,
    /// The protocol constants (acceptor set, quorum size, node id).
    pub constants: CConstants,
}

impl ProtocolConfig for PaxosConfig {
    fn parse_config(me: &EndPoint, args: &Args) -> Option<Self> {
        // Expected args format: [endpoint0, endpoint1, ..., endpointN]
        // Each endpoint is a peer. The one matching `me` determines my_index.
        // Quorum size is majority: (n / 2) + 1.
        if args.len() < 2 {
            eprintln!("Paxos: need at least 2 args (self + peers)");
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
                eprintln!("Paxos: own endpoint not found in args");
                return None;
            }
        };

        let num_nodes = peers.len() as u64;
        let quorum_size = (num_nodes / 2) + 1;

        // Build acceptor set: all node indices
        let mut acceptors = HashSet::new();
        for i in 0..num_nodes {
            acceptors.insert(i);
        }

        let constants = CConstants {
            acceptors,
            quorum_size,
            node_id: my_index,
        };

        Some(PaxosConfig {
            peers,
            my_index,
            constants,
        })
    }

    fn get_peers(&self) -> &Vec<EndPoint> {
        &self.peers
    }
}

/// The Paxos host wrapping protocol state.
pub struct PaxosHost {
    /// The verified protocol state.
    pub state: CState,
    /// Round-robin action index for timer-driven actions.
    pub action_index: u64,
    /// Counter for generating unique ballot numbers.
    /// Ballots are assigned as: ballot_counter * num_nodes + my_index
    /// to ensure globally unique, monotonically increasing ballots per node.
    pub ballot_counter: u64,
}

impl PaxosHost {
    /// Generate the next ballot number for this node.
    /// Uses the pattern: ballot = counter * num_nodes + my_index
    /// This ensures ballots are globally unique and monotonically increasing per node.
    fn next_ballot(&mut self, config: &PaxosConfig) -> u64 {
        self.ballot_counter = self.ballot_counter.wrapping_add(1);
        self.ballot_counter
            .wrapping_mul(config.peers.len() as u64)
            .wrapping_add(config.my_index)
    }

    /// Collect all peer endpoints except self for broadcasting.
    fn other_peers(config: &PaxosConfig) -> Vec<EndPoint> {
        let mut others = Vec::new();
        for i in 0..config.peers.len() {
            if i as u64 != config.my_index {
                others.push(config.peers[i].clone_up_to_view());
            }
        }
        others
    }

    /// Get the endpoint for a specific node index.
    fn peer_endpoint(config: &PaxosConfig, node_id: u64) -> Option<EndPoint> {
        if (node_id as usize) < config.peers.len() {
            Some(config.peers[node_id as usize].clone_up_to_view())
        } else {
            None
        }
    }

    // ---------------------------------------------------------------
    // Message-driven actions (called when a packet arrives)
    // ---------------------------------------------------------------

    /// Handle an incoming Prepare message (Phase 1a).
    /// If the ballot is >= our promised_bal, respond with a Promise (Phase 1b).
    fn handle_prepare(
        &mut self,
        config: &PaxosConfig,
        src: &EndPoint,
        ballot: u64,
    ) -> StepResult<PaxosMessage> {
        // Guard: b >= promised_bal (CSend1b precondition)
        if ballot < self.state.promised_bal {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        self.state.CSend1b(&config.constants, &ballot);

        // Send Promise back to the proposer
        StepResult {
            ok: true,
            outbound: GenericOutbound::Send {
                dst: src.clone_up_to_view(),
                msg: PaxosMessage::Promise {
                    ballot,
                    accepted_bal: self.state.accepted_bal,
                    accepted_val: self.state.accepted_val,
                },
            },
        }
    }

    /// Handle an incoming Promise message (Phase 1b response).
    /// Records the promise and updates highest accepted ballot/value if needed.
    fn handle_promise(
        &mut self,
        config: &PaxosConfig,
        acceptor_id: u64,
        _ballot: u64,
        accepted_bal: u64,
        accepted_val: u64,
    ) -> StepResult<PaxosMessage> {
        // Guard: phase must be Phase1
        if !matches!(self.state.phase, CPhase::Phase1) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: acceptor must be in the acceptor set
        if !config.constants.acceptors.contains(&acceptor_id) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must not have already received a promise from this acceptor
        if self.state.promises_rcvd.contains(&acceptor_id) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        self.state.CRecvPromise(
            &config.constants,
            &acceptor_id,
            &accepted_bal,
            &accepted_val,
        );

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    /// Handle an incoming Accept message (Phase 2a).
    /// If the ballot is >= our promised_bal, accept it and respond (Phase 2b).
    fn handle_accept(
        &mut self,
        config: &PaxosConfig,
        src: &EndPoint,
        ballot: u64,
        value: u64,
    ) -> StepResult<PaxosMessage> {
        // Guard: b >= promised_bal (CSend2b precondition)
        if ballot < self.state.promised_bal {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        self.state.CSend2b(&config.constants, &ballot, &value);

        // Send Accepted back to the proposer
        StepResult {
            ok: true,
            outbound: GenericOutbound::Send {
                dst: src.clone_up_to_view(),
                msg: PaxosMessage::Accepted { ballot, value },
            },
        }
    }

    /// Handle an incoming Accepted message (Phase 2b response).
    /// Records that an acceptor has accepted our proposal.
    fn handle_accepted(
        &mut self,
        config: &PaxosConfig,
        acceptor_id: u64,
        _ballot: u64,
        _value: u64,
    ) -> StepResult<PaxosMessage> {
        // Guard: phase must be Phase2
        if !matches!(self.state.phase, CPhase::Phase2) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: acceptor must be in the acceptor set
        if !config.constants.acceptors.contains(&acceptor_id) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must not have already received an accepted from this acceptor
        if self.state.accepts_rcvd.contains(&acceptor_id) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        self.state.CRecvAccepted(&config.constants, &acceptor_id);

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    // ---------------------------------------------------------------
    // Timer-driven actions (called on timeout, round-robin)
    // ---------------------------------------------------------------

    /// Timer action: Try to start a new proposal (Phase 1a).
    /// Only fires when the node is Idle (not already running a proposal).
    fn try_send1a(&mut self, config: &PaxosConfig) -> StepResult<PaxosMessage> {
        // Guard: phase must be Idle
        if !matches!(self.state.phase, CPhase::Idle) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let new_ballot = self.next_ballot(config);

        // Guard: new ballot must be > proposer_bal
        if new_ballot <= self.state.proposer_bal {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        self.state.CSend1a(&config.constants, &new_ballot);

        // Broadcast Prepare to all other nodes
        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: PaxosMessage::Prepare { ballot: new_ballot },
            },
        }
    }

    /// Timer action: Try to send Accept (Phase 2a).
    /// Only fires when we have collected a quorum of promises in Phase 1.
    fn try_send2a(&mut self, config: &PaxosConfig) -> StepResult<PaxosMessage> {
        // Guard: phase must be Phase1
        if !matches!(self.state.phase, CPhase::Phase1) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must have received a quorum of promises
        if (self.state.promises_rcvd.len() as u64) < config.constants.quorum_size {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // The value to propose: if any acceptor reported a previously accepted
        // value (highest_accepted_bal > 0), we must use that value.
        // Otherwise we can propose our own value (proposed_val, which defaults to 0).
        let proposed_value = self.state.proposed_val;

        self.state.CSend2a(&config.constants, &proposed_value);

        let ballot = self.state.proposer_bal;
        let value = self.state.proposed_val;

        // Broadcast Accept to all other nodes
        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: PaxosMessage::Accept { ballot, value },
            },
        }
    }

    /// Timer action: Try to learn a decided value.
    /// Only fires when we have collected a quorum of Accepted in Phase 2.
    fn try_learn(&mut self, config: &PaxosConfig) -> StepResult<PaxosMessage> {
        // Guard: phase must be Phase2
        if !matches!(self.state.phase, CPhase::Phase2) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must have received a quorum of accepts
        if (self.state.accepts_rcvd.len() as u64) < config.constants.quorum_size {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        self.state.CLearn(&config.constants);

        eprintln!("Paxos: DECIDED value = {}", self.state.decided_val);

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    /// Resolve the sender's node index from their endpoint.
    fn resolve_sender_index(config: &PaxosConfig, src: &EndPoint) -> Option<u64> {
        for i in 0..config.peers.len() {
            if config.peers[i].id == src.id {
                return Some(i as u64);
            }
        }
        None
    }
}

impl ProtocolHost for PaxosHost {
    type Msg = PaxosMessage;
    type Cfg = PaxosConfig;

    fn init(config: &Self::Cfg) -> Option<Self> {
        let state = paxos_gen::CInit(&config.constants);
        Some(PaxosHost {
            state,
            action_index: 0,
            ballot_counter: 0,
        })
    }

    fn next(
        &mut self,
        config: &Self::Cfg,
        packet: Option<GenericPacket<Self::Msg>>,
    ) -> StepResult<Self::Msg> {
        // Handle incoming message
        if let Some(pkt) = packet {
            let sender_id = Self::resolve_sender_index(config, &pkt.src);
            let sender_id = match sender_id {
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
                PaxosMessage::Prepare { ballot } => self.handle_prepare(config, &pkt.src, ballot),
                PaxosMessage::Promise {
                    ballot,
                    accepted_bal,
                    accepted_val,
                } => self.handle_promise(config, sender_id, ballot, accepted_bal, accepted_val),
                PaxosMessage::Accept { ballot, value } => {
                    self.handle_accept(config, &pkt.src, ballot, value)
                }
                PaxosMessage::Accepted { ballot, value } => {
                    self.handle_accepted(config, sender_id, ballot, value)
                }
            };
        }

        // No message -- run timer-driven actions round-robin
        let result = match self.action_index % 3 {
            0 => self.try_send1a(config),
            1 => self.try_send2a(config),
            _ => self.try_learn(config),
        };
        self.action_index = self.action_index.wrapping_add(1);
        result
    }
}
