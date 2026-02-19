//! ChainReplication protocol host implementation.
//!
//! Bridges the generic framework traits with the transpiler-generated
//! verified exec functions. The host scheduler maps incoming network
//! messages to the appropriate C* function calls.

use crate::common::framework::args_t::*;
use crate::common::framework::protocol_trait::*;
use crate::common::native::io_s::*;
use crate::generated::ChainReplication::chain_gen;
use crate::generated::ChainReplication::types_gen::*;
use crate::implementation::ChainReplication::message::*;
use std::collections::HashSet;

/// ChainReplication protocol configuration.
pub struct ChainConfig {
    /// All peer endpoints (ordered along the chain: index 0 = head, last = tail).
    pub peers: Vec<EndPoint>,
    /// This node's index in the peers list (determines role).
    pub my_index: u64,
    /// The protocol constants (node_id, chain_len).
    pub constants: CConstants,
}

impl ProtocolConfig for ChainConfig {
    fn parse_config(me: &EndPoint, args: &Args) -> Option<Self> {
        // Expected args format: [endpoint0, endpoint1, ..., endpointN]
        // Ordered along the chain: index 0 = head, last index = tail.
        // The endpoint matching `me` determines my_index.
        if args.len() < 2 {
            eprintln!("ChainReplication: need at least 2 args (chain of >= 2 nodes)");
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
                eprintln!("ChainReplication: own endpoint not found in args");
                return None;
            },
        };

        let chain_len = peers.len() as u64;

        // CInit requires: node_id < u64::MAX, chain_len >= 1,
        // node_id >= 1 (spec says node_id >= 1 for predecessor math),
        // node_id < chain_len.
        // However, the head has node_id == 0 which violates node_id >= 1.
        // The generated CInit guards this; we pass node_id = my_index and
        // let the caller arrange the chain so that node_id 0 is the head.
        let constants = CConstants {
            node_id: my_index,
            chain_len,
        };

        Some(ChainConfig {
            peers,
            my_index,
            constants,
        })
    }

    fn get_peers(&self) -> &Vec<EndPoint> {
        &self.peers
    }
}

/// The ChainReplication host wrapping protocol state.
pub struct ChainHost {
    /// The verified protocol state.
    pub state: CState,
    /// Round-robin action index for internal (non-message-driven) actions.
    pub action_index: u64,
}

impl ChainHost {
    /// Get the successor endpoint (if any).
    fn successor_endpoint(config: &ChainConfig, state: &CState) -> Option<EndPoint> {
        if state.has_successor {
            let succ_idx = state.successor as usize;
            if succ_idx < config.peers.len() {
                Some(config.peers[succ_idx].clone_up_to_view())
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Get the predecessor endpoint (if any).
    fn predecessor_endpoint(config: &ChainConfig, state: &CState) -> Option<EndPoint> {
        if state.has_predecessor {
            let pred_idx = state.predecessor as usize;
            if pred_idx < config.peers.len() {
                Some(config.peers[pred_idx].clone_up_to_view())
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Head node step: handle incoming ClientWrite, round-robin CForwardToSuccessor.
    fn head_step(
        &mut self,
        config: &ChainConfig,
        packet: Option<GenericPacket<ChainMessage>>,
    ) -> StepResult<ChainMessage> {
        if !self.state.alive {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // Handle incoming message
        if let Some(pkt) = packet {
            match pkt.msg {
                ChainMessage::ClientWrite { value } => {
                    return self.head_receive_write(config, value);
                },
                ChainMessage::Ack { value } => {
                    return self.receive_ack(config, value);
                },
                _ => {
                    // Head ignores Forward and ClientRead
                    return StepResult { ok: true, outbound: GenericOutbound::None };
                },
            }
        }

        // No message -- try round-robin internal action: forward to successor
        let result = self.try_forward_to_successor(config);
        self.action_index = self.action_index.wrapping_add(1);
        result
    }

    /// Middle node step: handle incoming Forward and Ack, round-robin CForwardToSuccessor.
    fn middle_step(
        &mut self,
        config: &ChainConfig,
        packet: Option<GenericPacket<ChainMessage>>,
    ) -> StepResult<ChainMessage> {
        if !self.state.alive {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // Handle incoming message
        if let Some(pkt) = packet {
            match pkt.msg {
                ChainMessage::Forward { value } => {
                    return self.receive_update(config, value);
                },
                ChainMessage::Ack { value } => {
                    return self.receive_ack(config, value);
                },
                _ => {
                    // Middle ignores ClientWrite and ClientRead
                    return StepResult { ok: true, outbound: GenericOutbound::None };
                },
            }
        }

        // No message -- try round-robin internal action: forward to successor
        let result = self.try_forward_to_successor(config);
        self.action_index = self.action_index.wrapping_add(1);
        result
    }

    /// Tail node step: handle incoming Forward, round-robin CTailCommit.
    fn tail_step(
        &mut self,
        config: &ChainConfig,
        packet: Option<GenericPacket<ChainMessage>>,
    ) -> StepResult<ChainMessage> {
        if !self.state.alive {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // Handle incoming message
        if let Some(pkt) = packet {
            match pkt.msg {
                ChainMessage::Forward { value } => {
                    return self.receive_update(config, value);
                },
                ChainMessage::ClientRead => {
                    return self.client_read(config);
                },
                _ => {
                    // Tail ignores ClientWrite and Ack
                    return StepResult { ok: true, outbound: GenericOutbound::None };
                },
            }
        }

        // No message -- try round-robin internal action: commit
        let result = self.try_tail_commit(config);
        self.action_index = self.action_index.wrapping_add(1);
        result
    }

    /// Head: receive a ClientWrite, add to history and pending_sent.
    fn head_receive_write(
        &mut self,
        config: &ChainConfig,
        value: u64,
    ) -> StepResult<ChainMessage> {
        // Guard: role is Head, alive, !pending_sent.contains(value)
        if !matches!(self.state.role, CNodeRole::Head) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !self.state.alive {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if self.state.pending_sent.contains(&value) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        let (new_state, _sent) = chain_gen::CHeadReceiveWrite(&self.state, &config.constants, &value);
        self.state = new_state;

        StepResult { ok: true, outbound: GenericOutbound::None }
    }

    /// Head/Middle: pick a value from pending_sent and forward to successor.
    fn try_forward_to_successor(
        &mut self,
        config: &ChainConfig,
    ) -> StepResult<ChainMessage> {
        // Guard: role is Head|Middle, alive, pending_sent non-empty, has_successor
        if !matches!(self.state.role, CNodeRole::Head | CNodeRole::Middle) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !self.state.alive {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !self.state.has_successor {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if self.state.pending_sent.is_empty() {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // Pick first element from pending_sent
        let value = match self.state.pending_sent.iter().next() {
            Some(v) => *v,
            None => return StepResult { ok: true, outbound: GenericOutbound::None },
        };

        let (new_state, _sent) = chain_gen::CForwardToSuccessor(&self.state, &config.constants, &value);
        self.state = new_state;

        // Send Forward message to successor
        match Self::successor_endpoint(config, &self.state) {
            Some(succ_ep) => {
                StepResult {
                    ok: true,
                    outbound: GenericOutbound::Send {
                        dst: succ_ep,
                        msg: ChainMessage::Forward { value },
                    },
                }
            },
            None => StepResult { ok: true, outbound: GenericOutbound::None },
        }
    }

    /// Middle/Tail: receive a Forward message, add to history.
    fn receive_update(
        &mut self,
        config: &ChainConfig,
        value: u64,
    ) -> StepResult<ChainMessage> {
        // Guard: role is Middle|Tail, alive, !history.contains(value)
        if !matches!(self.state.role, CNodeRole::Middle | CNodeRole::Tail) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !self.state.alive {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if self.state.history.contains(&value) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        let (new_state, _sent) = chain_gen::CReceiveUpdate(&self.state, &config.constants, &value);
        self.state = new_state;

        StepResult { ok: true, outbound: GenericOutbound::None }
    }

    /// Tail: commit a value from history, send Ack to predecessor.
    fn try_tail_commit(
        &mut self,
        config: &ChainConfig,
    ) -> StepResult<ChainMessage> {
        // Guard: role is Tail, alive, history non-empty, committed_count < u64::MAX
        if !matches!(self.state.role, CNodeRole::Tail) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !self.state.alive {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if self.state.history.is_empty() {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if self.state.committed_count >= u64::MAX {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        // Pick a value from history to commit (use first element)
        let value = self.state.history[0];

        let (new_state, _sent) = chain_gen::CTailCommit(&self.state, &config.constants, &value);
        self.state = new_state;

        // Send Ack to predecessor
        match Self::predecessor_endpoint(config, &self.state) {
            Some(pred_ep) => {
                StepResult {
                    ok: true,
                    outbound: GenericOutbound::Send {
                        dst: pred_ep,
                        msg: ChainMessage::Ack { value },
                    },
                }
            },
            None => StepResult { ok: true, outbound: GenericOutbound::None },
        }
    }

    /// Head/Middle: receive an Ack, remove value from pending_sent.
    fn receive_ack(
        &mut self,
        config: &ChainConfig,
        value: u64,
    ) -> StepResult<ChainMessage> {
        // Guard: role is Head|Middle, alive, pending_sent.contains(value)
        if !matches!(self.state.role, CNodeRole::Head | CNodeRole::Middle) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !self.state.alive {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !self.state.pending_sent.contains(&value) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        let (new_state, _sent) = chain_gen::CReceiveAck(&self.state, &config.constants, &value);
        self.state = new_state;

        // If this is a Middle node, propagate Ack to predecessor
        if matches!(self.state.role, CNodeRole::Middle) {
            match Self::predecessor_endpoint(config, &self.state) {
                Some(pred_ep) => {
                    return StepResult {
                        ok: true,
                        outbound: GenericOutbound::Send {
                            dst: pred_ep,
                            msg: ChainMessage::Ack { value },
                        },
                    };
                },
                None => {},
            }
        }

        StepResult { ok: true, outbound: GenericOutbound::None }
    }

    /// Tail: handle a ClientRead (returns current obj_value, no state change).
    fn client_read(
        &mut self,
        config: &ChainConfig,
    ) -> StepResult<ChainMessage> {
        if !matches!(self.state.role, CNodeRole::Tail) {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }
        if !self.state.alive {
            return StepResult { ok: true, outbound: GenericOutbound::None };
        }

        let (new_state, _sent) = chain_gen::CClientRead(&self.state, &config.constants);
        self.state = new_state;

        // In a real deployment, the read result (self.state.obj_value) would be
        // returned to the client. For now, this is a no-op on the network.
        StepResult { ok: true, outbound: GenericOutbound::None }
    }
}

impl ProtocolHost for ChainHost {
    type Msg = ChainMessage;
    type Cfg = ChainConfig;

    fn init(config: &Self::Cfg) -> Option<Self> {
        // CInit requires: node_id < u64::MAX, chain_len >= 1,
        // node_id >= 1, node_id < chain_len.
        // The head (node_id == 0) does not satisfy node_id >= 1,
        // so we handle it specially: build the initial state directly.
        if config.constants.chain_len < 1 {
            return None;
        }
        if config.constants.node_id >= config.constants.chain_len {
            return None;
        }
        if config.constants.node_id >= u64::MAX {
            return None;
        }

        if config.constants.node_id == 0 {
            // Head node: build initial state directly (CInit requires node_id >= 1)
            let state = CState {
                role: CNodeRole::Head,
                history: Vec::new(),
                pending_sent: HashSet::new(),
                committed_count: 0,
                obj_value: 0,
                has_predecessor: false,
                predecessor: 0,
                has_successor: config.constants.chain_len > 1,
                successor: if config.constants.chain_len > 1 { 1 } else { 0 },
                alive: true,
            };
            Some(ChainHost { state, action_index: 0 })
        } else {
            // Non-head nodes: use generated CInit
            let state = chain_gen::CInit(&config.constants);
            Some(ChainHost { state, action_index: 0 })
        }
    }

    fn next(
        &mut self,
        config: &Self::Cfg,
        packet: Option<GenericPacket<Self::Msg>>,
    ) -> StepResult<Self::Msg> {
        match &self.state.role {
            CNodeRole::Head => self.head_step(config, packet),
            CNodeRole::Middle => self.middle_step(config, packet),
            CNodeRole::Tail => self.tail_step(config, packet),
        }
    }
}
