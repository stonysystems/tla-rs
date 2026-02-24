//! Vertical Paxos protocol host implementation.
//!
//! Bridges the generic framework traits with the transpiler-generated
//! verified exec functions. The host scheduler maps incoming network
//! messages to the appropriate C* function calls and drives timer-based
//! proposer actions (Prepare, Accept, Commit, Reconfigure) in a
//! round-robin fashion.
//!
//! Vertical Paxos extends single-decree Paxos with reconfiguration:
//! after committing a value in one configuration, nodes can move to
//! a new configuration via CReconfigure and CSync.
//!
//! The spec models a shared-state system with sent_packets output.
//! This implementation translates that into explicit network messages.

use crate::common::framework::args_t::*;
use crate::common::framework::protocol_trait::*;
use crate::common::native::io_s::*;
use crate::generated::VerticalPaxos::types_gen::*;
use crate::generated::VerticalPaxos::vpaxos_gen;
use crate::implementation::VerticalPaxos::message::*;
use std::collections::HashSet;

/// Vertical Paxos protocol configuration.
pub struct VerticalPaxosConfig {
    /// All peer endpoints (ordered by node index).
    pub peers: Vec<EndPoint>,
    /// This node's index in the peers list.
    pub my_index: u64,
    /// The protocol constants (quorum_size, node_id, num_nodes).
    pub constants: CConstants,
}

impl ProtocolConfig for VerticalPaxosConfig {
    fn parse_config(me: &EndPoint, args: &Args) -> Option<Self> {
        // Expected args format: [endpoint0, endpoint1, ..., endpointN]
        // Each endpoint is a peer. The one matching `me` determines my_index.
        // Quorum size is majority: (n / 2) + 1.
        if args.len() < 2 {
            eprintln!("VerticalPaxos: need at least 2 args (self + peers)");
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
                eprintln!("VerticalPaxos: own endpoint not found in args");
                return None;
            }
        };

        let num_nodes = peers.len() as u64;
        let quorum_size = (num_nodes / 2) + 1;

        let constants = CConstants {
            quorum_size,
            num_nodes,
            node_id: my_index,
        };

        Some(VerticalPaxosConfig {
            peers,
            my_index,
            constants,
        })
    }

    fn get_peers(&self) -> &Vec<EndPoint> {
        &self.peers
    }
}

/// The Vertical Paxos host wrapping protocol state.
pub struct VerticalPaxosHost {
    /// The verified protocol state.
    pub state: CState,
    /// Round-robin action index for timer-driven actions.
    pub action_index: u64,
    /// Counter for generating unique ballot numbers.
    /// Ballots are assigned as: ballot_counter * num_nodes + my_index
    /// to ensure globally unique, monotonically increasing ballots per node.
    pub ballot_counter: u64,
}

impl VerticalPaxosHost {
    /// Generate the next ballot number for this node.
    /// Uses the pattern: ballot = counter * num_nodes + my_index
    /// This ensures ballots are globally unique and monotonically increasing per node.
    fn next_ballot(&mut self, config: &VerticalPaxosConfig) -> u64 {
        self.ballot_counter = self.ballot_counter.wrapping_add(1);
        self.ballot_counter
            .wrapping_mul(config.peers.len() as u64)
            .wrapping_add(config.my_index)
    }

    /// Collect all peer endpoints except self for broadcasting.
    fn other_peers(config: &VerticalPaxosConfig) -> Vec<EndPoint> {
        let mut others = Vec::new();
        for i in 0..config.peers.len() {
            if i as u64 != config.my_index {
                others.push(config.peers[i].clone_up_to_view());
            }
        }
        others
    }

    /// Resolve the sender's node index from their endpoint.
    fn resolve_sender_index(config: &VerticalPaxosConfig, src: &EndPoint) -> Option<u64> {
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

    /// Handle an incoming Prepare message (Phase 1a).
    /// As an acceptor, respond with a Promise (Phase 1b) via CSendPromise.
    fn handle_prepare(
        &mut self,
        config: &VerticalPaxosConfig,
        src: &EndPoint,
        ballot: u64,
    ) -> StepResult<VerticalPaxosMessage> {
        // Guard: must be active
        if !self.state.is_active {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // CSendPromise requires: prepare_bal > max_bal
        if ballot <= self.state.max_bal {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Capture current accepted state before updating max_bal
        let promise_v_bal = self.state.max_v_bal;
        let promise_val = self.state.max_val;

        let (new_state, _sent) = vpaxos_gen::CSendPromise(&self.state, &config.constants, &ballot);
        self.state = new_state;

        // Send Promise back to the proposer
        StepResult {
            ok: true,
            outbound: GenericOutbound::Send {
                dst: src.clone_up_to_view(),
                msg: VerticalPaxosMessage::Promise {
                    ballot,
                    v_bal: promise_v_bal,
                    val: promise_val,
                    sender: config.my_index,
                },
            },
        }
    }

    /// Handle an incoming Promise message (Phase 1b response).
    /// Records the promise via CReceivePromise.
    fn handle_promise(
        &mut self,
        config: &VerticalPaxosConfig,
        ballot: u64,
        v_bal: u64,
        val: u64,
        sender: u64,
    ) -> StepResult<VerticalPaxosMessage> {
        // Guard: must be active
        if !self.state.is_active {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: promise ballot must match our current max_bal
        if ballot != self.state.max_bal {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must not have already received a promise from this sender
        if self.state.promises_rcvd.contains(&sender) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) = vpaxos_gen::CReceivePromise(
            &self.state,
            &config.constants,
            &sender,
            &ballot,
            &v_bal,
            &val,
        );
        self.state = new_state;

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    /// Handle an incoming Accept message (Phase 2a) as an acceptor.
    /// The acceptor receives an Accept, updates state, and responds with AcceptOk.
    fn handle_accept(
        &mut self,
        config: &VerticalPaxosConfig,
        src: &EndPoint,
        ballot: u64,
        value: u64,
    ) -> StepResult<VerticalPaxosMessage> {
        // Guard: must be active
        if !self.state.is_active {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // CAccept requires: b == max_bal and b > max_v_bal
        if ballot != self.state.max_bal {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        if ballot <= self.state.max_v_bal {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) =
            vpaxos_gen::CAccept(&self.state, &config.constants, &ballot, &value);
        self.state = new_state;

        // Send AcceptOk back to the proposer
        StepResult {
            ok: true,
            outbound: GenericOutbound::Send {
                dst: src.clone_up_to_view(),
                msg: VerticalPaxosMessage::AcceptOk {
                    sender: config.my_index,
                },
            },
        }
    }

    /// Handle an incoming AcceptOk message (Phase 2b ack).
    /// Records that an acceptor has accepted via CReceiveAccepted.
    fn handle_accept_ok(
        &mut self,
        config: &VerticalPaxosConfig,
        sender: u64,
    ) -> StepResult<VerticalPaxosMessage> {
        // Guard: must be active
        if !self.state.is_active {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // CReceiveAccepted requires: accept_bal == max_bal
        // The accept_bal for our outstanding Accept is our max_bal
        let accept_bal = self.state.max_bal;

        // Guard: must not have already received an accept from this sender
        if self.state.accepts_rcvd.contains(&sender) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) =
            vpaxos_gen::CReceiveAccepted(&self.state, &config.constants, &sender, &accept_bal);
        self.state = new_state;

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    /// Handle an incoming Commit message.
    /// This is informational -- the node learns the decided value.
    fn handle_commit(
        &mut self,
        _config: &VerticalPaxosConfig,
        value: u64,
    ) -> StepResult<VerticalPaxosMessage> {
        eprintln!("VerticalPaxos: received COMMIT for value = {}", value);
        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    /// Handle an incoming Sync message (reconfiguration).
    /// Activates an inactive node in a new configuration via CSync.
    fn handle_sync(
        &mut self,
        config: &VerticalPaxosConfig,
        new_config: u64,
        val: u64,
    ) -> StepResult<VerticalPaxosMessage> {
        // CSync requires: is_active == false, new_config > config_num
        if self.state.is_active {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        if new_config <= self.state.config_num {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) =
            vpaxos_gen::CSync(&self.state, &config.constants, &new_config, &val);
        self.state = new_state;

        eprintln!(
            "VerticalPaxos: SYNC to config {} with value = {}",
            new_config, val
        );

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    // ---------------------------------------------------------------
    // Timer-driven actions (called on timeout, round-robin)
    // ---------------------------------------------------------------

    /// Timer action: Try to start a new proposal (Phase 1a via CPrepare).
    /// Only fires when the node is active and idle (no pending prepare/accept).
    fn try_prepare(&mut self, config: &VerticalPaxosConfig) -> StepResult<VerticalPaxosMessage> {
        // Guard: must be active
        if !self.state.is_active {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let new_ballot = self.next_ballot(config);

        // CPrepare requires: b > max_bal
        if new_ballot <= self.state.max_bal {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) = vpaxos_gen::CPrepare(&self.state, &config.constants, &new_ballot);
        self.state = new_state;

        // Broadcast Prepare to all other nodes
        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: VerticalPaxosMessage::Prepare { ballot: new_ballot },
            },
        }
    }

    /// Timer action: Try to send Accept (Phase 2a via CAccept).
    /// Only fires when we have collected a quorum of promises.
    fn try_accept(&mut self, config: &VerticalPaxosConfig) -> StepResult<VerticalPaxosMessage> {
        // Guard: must be active
        if !self.state.is_active {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must have received enough promises
        if (self.state.promises_rcvd.len() as u64) < config.constants.quorum_size {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let ballot = self.state.max_bal;
        let value = self.state.max_val;

        // CAccept requires: b == max_bal, b > max_v_bal
        if ballot <= self.state.max_v_bal {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) =
            vpaxos_gen::CAccept(&self.state, &config.constants, &ballot, &value);
        self.state = new_state;

        // Broadcast Accept to all other nodes
        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: VerticalPaxosMessage::Accept { ballot, value },
            },
        }
    }

    /// Timer action: Try to commit.
    /// Only fires when we have collected a quorum of accepts and have not committed yet.
    fn try_commit(&mut self, config: &VerticalPaxosConfig) -> StepResult<VerticalPaxosMessage> {
        // Guard: must be active
        if !self.state.is_active {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must not have already committed
        if self.state.committed {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: must have a quorum of accepts
        if (self.state.accepts_rcvd.len() as u64) < config.constants.quorum_size {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (new_state, _sent) = vpaxos_gen::CCommit(&self.state, &config.constants);
        self.state = new_state;

        let decided_val = self.state.committed_val;
        eprintln!("VerticalPaxos: COMMITTED value = {}", decided_val);

        // Broadcast Commit to all other nodes
        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: VerticalPaxosMessage::Commit { value: decided_val },
            },
        }
    }

    /// Timer action: Try to reconfigure.
    /// Only fires when the node is active and has committed (ready for next config).
    fn try_reconfigure(
        &mut self,
        config: &VerticalPaxosConfig,
    ) -> StepResult<VerticalPaxosMessage> {
        // Guard: must be active
        if !self.state.is_active {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // CReconfigure requires: config_num < u64::MAX
        if self.state.config_num >= u64::MAX {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Only reconfigure after a commit to move to the next configuration
        if !self.state.committed {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let old_val = self.state.committed_val;
        let (new_state, _sent) = vpaxos_gen::CReconfigure(&self.state, &config.constants);
        self.state = new_state;

        let new_config_num = self.state.config_num;
        eprintln!(
            "VerticalPaxos: RECONFIGURE to config {} (carrying value = {})",
            new_config_num, old_val
        );

        // Broadcast Sync to all other nodes so they can join the new configuration
        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: VerticalPaxosMessage::Sync {
                    config: new_config_num,
                    value: old_val,
                },
            },
        }
    }
}

impl ProtocolHost for VerticalPaxosHost {
    type Msg = VerticalPaxosMessage;
    type Cfg = VerticalPaxosConfig;

    fn init(config: &Self::Cfg) -> Option<Self> {
        let state = vpaxos_gen::CInit(&config.constants);
        Some(VerticalPaxosHost {
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
                VerticalPaxosMessage::Prepare { ballot } => {
                    self.handle_prepare(config, &pkt.src, ballot)
                }
                VerticalPaxosMessage::Promise {
                    ballot,
                    v_bal,
                    val,
                    sender,
                } => self.handle_promise(config, ballot, v_bal, val, sender),
                VerticalPaxosMessage::Accept { ballot, value } => {
                    self.handle_accept(config, &pkt.src, ballot, value)
                }
                VerticalPaxosMessage::AcceptOk { sender } => self.handle_accept_ok(config, sender),
                VerticalPaxosMessage::Commit { value } => self.handle_commit(config, value),
                VerticalPaxosMessage::Sync {
                    config: new_config,
                    value,
                } => self.handle_sync(config, new_config, value),
            };
        }

        // No message -- run timer-driven actions round-robin
        let result = match self.action_index % 4 {
            0 => self.try_prepare(config),
            1 => self.try_accept(config),
            2 => self.try_commit(config),
            _ => self.try_reconfigure(config),
        };
        self.action_index = self.action_index.wrapping_add(1);
        result
    }
}
