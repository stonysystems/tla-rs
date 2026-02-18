//! PBFT protocol host implementation.
//!
//! Bridges the generic framework traits with the transpiler-generated
//! verified exec functions. The host scheduler maps incoming network
//! messages to the appropriate C* function calls and drives timer-based
//! actions (checkpoint, view change, new round) in a round-robin fashion.

use crate::common::framework::args_t::*;
use crate::common::framework::protocol_trait::*;
use crate::common::native::io_s::*;
use crate::generated::PBFT::pbft_gen;
use crate::generated::PBFT::types_gen::*;
use crate::implementation::PBFT::message::*;
use std::collections::HashSet;

/// PBFT protocol configuration.
pub struct PBFTConfig {
    /// All peer endpoints (ordered by node index).
    pub peers: Vec<EndPoint>,
    /// This node's index in the peers list.
    pub my_index: u64,
    /// The protocol constants (f, n, node_id, checkpoint_interval).
    pub constants: CConstants,
}

impl ProtocolConfig for PBFTConfig {
    fn parse_config(me: &EndPoint, args: &Args) -> Option<Self> {
        // Expected args format: [endpoint0, endpoint1, ..., endpointN]
        // Each endpoint is a peer. The one matching `me` determines my_index.
        // f = (n - 1) / 3, checkpoint_interval = 100.
        if args.len() < 4 {
            eprintln!("PBFT: need at least 4 args (3f+1 nodes, f >= 1)");
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
                eprintln!("PBFT: own endpoint not found in args");
                return None;
            },
        };

        let num_nodes = peers.len() as u64;
        let f = (num_nodes - 1) / 3;
        let checkpoint_interval = 100u64;

        let constants = CConstants {
            n: num_nodes,
            f,
            node_id: my_index,
            checkpoint_interval,
        };

        Some(PBFTConfig {
            peers,
            my_index,
            constants,
        })
    }

    fn get_peers(&self) -> &Vec<EndPoint> {
        &self.peers
    }
}

/// The PBFT host wrapping protocol state.
pub struct PBFTHost {
    /// The verified protocol state.
    pub state: CState,
    /// Round-robin action index for timer-driven actions.
    pub action_index: u64,
}

impl PBFTHost {
    /// Check if this node is currently the primary for the current view.
    fn is_primary(&self) -> bool {
        self.state.is_primary
    }

    /// Collect all peer endpoints except self for broadcasting.
    fn other_peers(config: &PBFTConfig) -> Vec<EndPoint> {
        let mut others = Vec::new();
        for i in 0..config.peers.len() {
            if i as u64 != config.my_index {
                others.push(config.peers[i].clone_up_to_view());
            }
        }
        others
    }

    /// Collect all peer endpoints for broadcasting (including self).
    fn all_peers(config: &PBFTConfig) -> Vec<EndPoint> {
        let mut all = Vec::new();
        for i in 0..config.peers.len() {
            all.push(config.peers[i].clone_up_to_view());
        }
        all
    }

    /// Resolve the sender's node index from their endpoint.
    fn resolve_sender_index(config: &PBFTConfig, src: &EndPoint) -> Option<u64> {
        for i in 0..config.peers.len() {
            if config.peers[i].id == src.id {
                return Some(i as u64);
            }
        }
        None
    }

    // ---------------------------------------------------------------
    // Message-driven actions
    // ---------------------------------------------------------------

    /// Primary: receive a ClientRequest and call CPrePrepare.
    /// Guards: phase is PrePrepare, is_primary, seq >= low_watermark,
    ///         seq < high_watermark.
    fn handle_client_request(
        &mut self,
        config: &PBFTConfig,
        digest: u64,
    ) -> StepResult<PBFTMessage> {
        if !self.is_primary() {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !matches!(self.state.phase, CPhase::PrePrepare) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if self.state.seq_num < self.state.low_watermark
            || self.state.seq_num >= self.state.high_watermark
        {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        self.state = pbft_gen::CPrePrepare(&self.state, &config.constants, &digest);

        // Broadcast PrePrepare to all other replicas
        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: PBFTMessage::PrePrepare {
                    view: self.state.view,
                    seq: self.state.seq_num,
                    digest,
                },
            },
        }
    }

    /// Non-primary: receive a PrePrepare and call CReceivePrePrepare.
    /// Guards: phase is PrePrepare, not primary, msgs_preprepare == true,
    ///         msgs_preprepare_view == view.
    fn handle_pre_prepare(
        &mut self,
        config: &PBFTConfig,
        view: u64,
        seq: u64,
        digest: u64,
    ) -> StepResult<PBFTMessage> {
        if self.is_primary() {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !matches!(self.state.phase, CPhase::PrePrepare) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // Set the pre-prepare message fields in state before calling CReceivePrePrepare.
        // The gen function reads these from the state as guards.
        self.state.msgs_preprepare = true;
        self.state.msgs_preprepare_view = view;
        self.state.msgs_preprepare_seq = seq;
        self.state.msgs_preprepare_digest = digest;

        // Guard: msgs_preprepare_view must equal current view
        if self.state.msgs_preprepare_view != self.state.view {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        self.state = pbft_gen::CReceivePrePrepare(&self.state, &config.constants);

        // Broadcast Prepare to all peers
        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: PBFTMessage::Prepare {
                    view: self.state.view,
                    seq: self.state.seq_num,
                    digest: self.state.request_digest,
                    sender: config.constants.node_id,
                },
            },
        }
    }

    /// Receive a Prepare message and call CReceivePrepare.
    /// Guards: phase is Prepare, sender not already in prepare_senders.
    fn handle_prepare(
        &mut self,
        config: &PBFTConfig,
        sender: u64,
    ) -> StepResult<PBFTMessage> {
        if !matches!(self.state.phase, CPhase::Prepare) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // Guard: sender must not already be in prepare_senders
        if self.state.prepare_senders.contains(&sender) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        self.state = pbft_gen::CReceivePrepare(&self.state, &config.constants, &sender);

        // Check if we have enough prepares to enter commit phase.
        // Guard for CEnterCommit: phase is Prepare, prepare_senders.len() >= 2f+1.
        let threshold = 2 * config.constants.f + 1;
        if self.state.prepare_senders.len() as u64 >= threshold {
            self.state = pbft_gen::CEnterCommit(&self.state, &config.constants);

            // Broadcast Commit to all peers
            let others = Self::other_peers(config);
            return StepResult {
                ok: true,
                outbound: GenericOutbound::Broadcast {
                    dsts: others,
                    msg: PBFTMessage::Commit {
                        view: self.state.view,
                        seq: self.state.seq_num,
                        sender: config.constants.node_id,
                    },
                },
            };
        }

        StepResult { ok: true, outbound: GenericOutbound::None }
    }

    /// Receive a Commit message and call CReceiveCommit.
    /// Guards: phase is Commit, sender not already in commit_senders.
    fn handle_commit(
        &mut self,
        config: &PBFTConfig,
        sender: u64,
    ) -> StepResult<PBFTMessage> {
        if !matches!(self.state.phase, CPhase::Commit) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // Guard: sender must not already be in commit_senders
        if self.state.commit_senders.contains(&sender) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        self.state = pbft_gen::CReceiveCommit(&self.state, &config.constants, &sender);

        // Check if we have enough commits to execute and reply.
        // Guard for CExecuteReply: phase is Commit, commit_senders.len() >= 2f+1,
        //                          seq_num < u64::MAX.
        let threshold = 2 * config.constants.f + 1;
        if self.state.commit_senders.len() as u64 >= threshold
            && self.state.seq_num < u64::MAX
        {
            self.state = pbft_gen::CExecuteReply(&self.state, &config.constants);
            eprintln!(
                "PBFT: COMMITTED seq={} digest={}",
                self.state.seq_num, self.state.request_digest
            );
        }

        StepResult { ok: true, outbound: GenericOutbound::None }
    }

    // ---------------------------------------------------------------
    // Timer-driven actions (called on timeout, round-robin)
    // ---------------------------------------------------------------

    /// Timer action: attempt a checkpoint.
    /// Guards: phase is Replied, seq_num > checkpoint_seq,
    ///         seq_num <= u64::MAX - checkpoint_interval.
    fn try_checkpoint(
        &mut self,
        config: &PBFTConfig,
    ) -> StepResult<PBFTMessage> {
        if !matches!(self.state.phase, CPhase::Replied) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if self.state.seq_num <= self.state.checkpoint_seq {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if self.state.seq_num > u64::MAX - config.constants.checkpoint_interval {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // Use seq_num as a simple digest for the checkpoint.
        let digest = self.state.seq_num;
        self.state = pbft_gen::CCheckpoint(&self.state, &config.constants, &digest);

        StepResult { ok: true, outbound: GenericOutbound::None }
    }

    /// Timer action: attempt a view change.
    /// Guards: view < u64::MAX.
    fn try_view_change(
        &mut self,
        config: &PBFTConfig,
    ) -> StepResult<PBFTMessage> {
        if self.state.view >= u64::MAX {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        self.state = pbft_gen::CViewChange(&self.state, &config.constants);

        StepResult { ok: true, outbound: GenericOutbound::None }
    }

    /// Timer action: attempt a new round.
    /// Guards: phase is Replied.
    fn try_new_round(
        &mut self,
        config: &PBFTConfig,
    ) -> StepResult<PBFTMessage> {
        if !matches!(self.state.phase, CPhase::Replied) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        self.state = pbft_gen::CNewRound(&self.state, &config.constants);

        StepResult { ok: true, outbound: GenericOutbound::None }
    }

    /// Primary timer action: attempt CPrePrepare with a synthetic digest
    /// followed by CNewRound to advance through rounds.
    fn try_pre_prepare_and_new_round(
        &mut self,
        config: &PBFTConfig,
    ) -> StepResult<PBFTMessage> {
        // First try new round if in Replied phase
        if matches!(self.state.phase, CPhase::Replied) {
            self.state = pbft_gen::CNewRound(&self.state, &config.constants);
        }

        // Then try pre-prepare if primary and in PrePrepare phase
        if !self.is_primary() {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !matches!(self.state.phase, CPhase::PrePrepare) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if self.state.seq_num < self.state.low_watermark
            || self.state.seq_num >= self.state.high_watermark
        {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // Use action_index as a synthetic digest for timer-driven proposals
        let digest = self.action_index;
        self.state = pbft_gen::CPrePrepare(&self.state, &config.constants, &digest);

        let others = Self::other_peers(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Broadcast {
                dsts: others,
                msg: PBFTMessage::PrePrepare {
                    view: self.state.view,
                    seq: self.state.seq_num,
                    digest,
                },
            },
        }
    }
}

impl ProtocolHost for PBFTHost {
    type Msg = PBFTMessage;
    type Cfg = PBFTConfig;

    fn init(config: &Self::Cfg) -> Option<Self> {
        let state = pbft_gen::CInit(&config.constants);
        Some(PBFTHost {
            state,
            action_index: 0,
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
                    return StepResult { ok: true, outbound: GenericOutbound::None };
                },
            };

            return match pkt.msg {
                PBFTMessage::ClientRequest { digest } => {
                    self.handle_client_request(config, digest)
                },
                PBFTMessage::PrePrepare { view, seq, digest } => {
                    self.handle_pre_prepare(config, view, seq, digest)
                },
                PBFTMessage::Prepare { view: _, seq: _, digest: _, sender } => {
                    self.handle_prepare(config, sender)
                },
                PBFTMessage::Commit { view: _, seq: _, sender } => {
                    self.handle_commit(config, sender)
                },
            };
        }

        // No message -- run timer-driven actions round-robin
        let result = match self.action_index % 4 {
            0 => self.try_pre_prepare_and_new_round(config),
            1 => self.try_checkpoint(config),
            2 => self.try_view_change(config),
            _ => self.try_new_round(config),
        };
        self.action_index = self.action_index.wrapping_add(1);
        result
    }
}
