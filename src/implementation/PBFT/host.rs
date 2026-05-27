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
use std::time::Instant;

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
                eprintln!("PBFT: own endpoint not found in args");
                return None;
            }
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
    /// Timestamp of last metrics output (for periodic throughput reporting).
    last_metrics_time: Instant,
    /// seq_num at last metrics output (for delta computation).
    last_metrics_seq_num: u64,
    /// Buffered client digest: avoids dropping client requests when not in
    /// PrePrepare phase. The timer-driven pre-prepare uses this instead of
    /// a synthetic digest, so client flooding doesn't starve the protocol.
    pending_digest: Option<u64>,
    /// Timestamp of last PrePrepare send (for rate-limiting retransmits).
    last_pre_prepare_time: Instant,
    /// Timestamp of last Prepare/Commit resend (for backup-side retransmit).
    last_resend_time: Instant,
    /// Timestamp of last catch-up Commit sent (rate-limits catch-up responses).
    last_catchup_time: Instant,
    /// Current and previous round's PrePrepare params (view, seq, digest).
    /// The primary may be 1 round ahead of backups; retransmitting the previous
    /// round's PrePrepare unsticks lagging backups.
    cur_pre_prepare: Option<(u64, u64, u64)>,
    prev_pre_prepare: Option<(u64, u64, u64)>,
    /// Client endpoint for the current pending request (if any).
    pending_client: Option<EndPoint>,
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
    /// If in Replied phase, proactively advances through Checkpoint→NewRound→PrePrepare
    /// in a single call to avoid client flooding starvation (the framework's timeout=0
    /// receive means timer ticks never fire while client packets are queued).
    fn handle_client_request(
        &mut self,
        config: &PBFTConfig,
        digest: u64,
        client_ep: EndPoint,
    ) -> StepResult<PBFTMessage> {
        if !self.is_primary() {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Buffer the digest and track the client endpoint
        self.pending_digest = Some(digest);
        self.pending_client = Some(client_ep);

        // Inline PrePrepare: the timer path may never fire during client
        // flooding (148K packets/sec), so try to start a new round here.
        self.try_pre_prepare_and_new_round(config)
    }

    /// Non-primary: receive a PrePrepare and call CReceivePrePrepare.
    /// Guards: phase is PrePrepare, not primary, view matches current view.
    /// If in Replied phase, proactively advances to PrePrepare first.
    fn handle_pre_prepare(
        &mut self,
        config: &PBFTConfig,
        view: u64,
        seq: u64,
        digest: u64,
    ) -> StepResult<PBFTMessage> {
        if self.is_primary() {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // If in Replied phase when PrePrepare arrives, advance to PrePrepare
        // so we can accept this round. This is safe: triggered by a real
        // PrePrepare from the primary, not a timer.
        if matches!(self.state.phase, CPhase::Replied) {
            let _ = self.try_checkpoint(config);
            let _ = self.try_new_round(config);
        }

        // If already in Prepare or Commit for this round and receiving a retransmit
        // PrePrepare, re-send our Prepare. Other backups may have missed it
        // because they hadn't entered Prepare yet when we first sent it.
        // We always resend Prepare (not Commit) because lagging backups need
        // the Prepare to reach their 2f+1 threshold and enter Commit.
        if (matches!(self.state.phase, CPhase::Prepare) || matches!(self.state.phase, CPhase::Commit))
            && view == self.state.view && seq == self.state.seq_num
        {
            let others = Self::other_peers(config);
            return StepResult {
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
            };
        }

        if !matches!(self.state.phase, CPhase::PrePrepare) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: view must equal current view, seq must match our seq_num
        if view != self.state.view || seq != self.state.seq_num {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let _sent = self.state.CReceivePrePrepare(&config.constants, &view, &seq, &digest);
        self.last_resend_time = Instant::now();

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
    /// Guards: phase is Prepare, view/seq match, sender not already in prepare_senders.
    fn handle_prepare(&mut self, config: &PBFTConfig, view: u64, seq: u64, sender: u64, src: &EndPoint) -> StepResult<PBFTMessage> {
        // If we already completed this round, help the stuck sender catch up
        // by sending our Prepare for their round (they need Prepares to enter
        // Commit). Rate-limited to 1/ms to avoid flooding.
        if view == self.state.view && seq < self.state.seq_num {
            let now = Instant::now();
            if now.duration_since(self.last_catchup_time).as_millis() >= 1 {
                self.last_catchup_time = now;
                return StepResult {
                    ok: true,
                    outbound: GenericOutbound::Send {
                        dst: src.clone_up_to_view(),
                        msg: PBFTMessage::Prepare {
                            view,
                            seq,
                            digest: 0, // digest is not checked by receiver
                            sender: config.constants.node_id,
                        },
                    },
                };
            }
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Reject stale or future messages from different rounds
        if view != self.state.view || seq != self.state.seq_num {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }
        // If already in Commit phase and receiving a Prepare for this round,
        // resend our Commit. The sender may not have entered Commit yet.
        if matches!(self.state.phase, CPhase::Commit) {
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

        if !matches!(self.state.phase, CPhase::Prepare) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: sender must not already be in prepare_senders
        if self.state.prepare_senders.contains(&sender) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let _sent = self.state.CReceivePrepare(&config.constants, &sender);
        self.last_resend_time = Instant::now();

        // Check if we have enough prepares to enter commit phase.
        // Guard for CEnterCommit: phase is Prepare, prepare_senders.len() >= 2f+1.
        let threshold = 2 * config.constants.f + 1;
        if self.state.prepare_senders.len() as u64 >= threshold {
            let _sent = self.state.CEnterCommit(&config.constants);
            self.last_resend_time = Instant::now();

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

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    /// Receive a Commit message and call CReceiveCommit.
    /// Guards: phase is Commit, sender not already in commit_senders.
    /// After reaching Replied, immediately advances through Checkpoint→NewRound
    /// so the node is ready for the next PrePrepare without waiting for a timer tick.
    fn handle_commit(&mut self, config: &PBFTConfig, view: u64, seq: u64, sender: u64, src: &EndPoint) -> StepResult<PBFTMessage> {
        // If we already completed this round, help the stuck sender catch up.
        if view == self.state.view && seq < self.state.seq_num {
            let now = Instant::now();
            if now.duration_since(self.last_catchup_time).as_millis() >= 1 {
                self.last_catchup_time = now;
                return StepResult {
                    ok: true,
                    outbound: GenericOutbound::Send {
                        dst: src.clone_up_to_view(),
                        msg: PBFTMessage::Commit {
                            view,
                            seq,
                            sender: config.constants.node_id,
                        },
                    },
                };
            }
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Reject stale or future messages from different rounds
        if view != self.state.view || seq != self.state.seq_num {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }
        if !matches!(self.state.phase, CPhase::Commit) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Guard: sender must not already be in commit_senders
        if self.state.commit_senders.contains(&sender) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let _sent = self.state.CReceiveCommit(&config.constants, &sender);
        self.last_resend_time = Instant::now();

        // Check if we have enough commits to execute and reply.
        let threshold = 2 * config.constants.f + 1;
        if self.state.commit_senders.len() as u64 >= threshold && self.state.seq_num < u64::MAX {
            let digest = self.state.request_digest;
            let client_ep = self.pending_client.take();

            let _sent = self.state.CExecuteReply(&config.constants);
            // Advance to PrePrepare immediately so we're ready for the next round.
            // Do NOT call CPrePrepare here — let the timer-driven
            // try_pre_prepare_and_new_round handle it. This prevents the primary
            // from racing a full round ahead of backups.
            let _ = self.try_checkpoint(config);
            let _ = self.try_new_round(config);

            // Send ClientReply to the requesting client (primary only)
            if let Some(dst) = client_ep {
                return StepResult {
                    ok: true,
                    outbound: GenericOutbound::Send {
                        dst,
                        msg: PBFTMessage::ClientReply { digest },
                    },
                };
            }
        }

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    // ---------------------------------------------------------------
    // Timer-driven actions (called on timeout, round-robin)
    // ---------------------------------------------------------------

    /// Timer action: attempt a checkpoint.
    /// Guards: phase is Replied, seq_num > checkpoint_seq,
    ///         seq_num <= u64::MAX - checkpoint_interval.
    fn try_checkpoint(&mut self, config: &PBFTConfig) -> StepResult<PBFTMessage> {
        if !matches!(self.state.phase, CPhase::Replied) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }
        if self.state.seq_num <= self.state.checkpoint_seq {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }
        if self.state.seq_num > u64::MAX - config.constants.checkpoint_interval {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Use seq_num as a simple digest for the checkpoint.
        let digest = self.state.seq_num;
        let _sent = self.state.CCheckpoint(&config.constants, &digest);

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    /// Timer action: attempt a view change.
    /// Guards: view < u64::MAX.
    fn try_view_change(&mut self, config: &PBFTConfig) -> StepResult<PBFTMessage> {
        if self.state.view >= u64::MAX {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let _sent = self.state.CViewChange(&config.constants);

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    /// Timer action: attempt a new round.
    /// Guards: phase is Replied.
    fn try_new_round(&mut self, config: &PBFTConfig) -> StepResult<PBFTMessage> {
        if !matches!(self.state.phase, CPhase::Replied) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let _sent = self.state.CNewRound(&config.constants);

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    /// Primary timer action: attempt CPrePrepare with a buffered or synthetic
    /// digest, preceded by CNewRound to advance through rounds.
    /// Also re-sends the current PrePrepare if stuck in Prepare phase
    /// (backups may have missed the original due to timing).
    fn try_pre_prepare_and_new_round(&mut self, config: &PBFTConfig) -> StepResult<PBFTMessage> {
        // First try new round if in Replied phase
        if matches!(self.state.phase, CPhase::Replied) {
            let _sent = self.state.CNewRound(&config.constants);
        }

        if !self.is_primary() {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // If stuck in Prepare or Commit waiting for backups, retransmit
        // PrePrepare at most once per 1ms. Also retransmit the PREVIOUS round's
        // PrePrepare, since backups may be 1 round behind.
        if matches!(self.state.phase, CPhase::Prepare | CPhase::Commit) {
            let now = Instant::now();
            if now.duration_since(self.last_pre_prepare_time).as_millis() >= 1 {
                self.last_pre_prepare_time = now;
                let others = Self::other_peers(config);
                let src = config.peers[config.my_index as usize].clone_up_to_view();

                let mut packets = Vec::new();
                // Send current round's PrePrepare
                for peer in &others {
                    packets.push(GenericPacket {
                        dst: peer.clone_up_to_view(),
                        src: src.clone_up_to_view(),
                        msg: PBFTMessage::PrePrepare {
                            view: self.state.view,
                            seq: self.state.seq_num,
                            digest: self.state.request_digest,
                        },
                    });
                }
                // In Commit phase, also resend our own Commit (peers may have
                // missed the original due to UDP drops).
                if matches!(self.state.phase, CPhase::Commit) {
                    for peer in &others {
                        packets.push(GenericPacket {
                            dst: peer.clone_up_to_view(),
                            src: src.clone_up_to_view(),
                            msg: PBFTMessage::Commit {
                                view: self.state.view,
                                seq: self.state.seq_num,
                                sender: config.constants.node_id,
                            },
                        });
                    }
                }
                // Also send previous round's PrePrepare (backups may be 1 behind)
                if let Some((pv, ps, pd)) = self.prev_pre_prepare {
                    if ps < self.state.seq_num {
                        for peer in &others {
                            packets.push(GenericPacket {
                                dst: peer.clone_up_to_view(),
                                src: src.clone_up_to_view(),
                                msg: PBFTMessage::PrePrepare {
                                    view: pv,
                                    seq: ps,
                                    digest: pd,
                                },
                            });
                        }
                    }
                }
                return StepResult {
                    ok: true,
                    outbound: GenericOutbound::Sequence { packets },
                };
            }
        }

        if !matches!(self.state.phase, CPhase::PrePrepare) {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }
        if self.state.seq_num < self.state.low_watermark
            || self.state.seq_num >= self.state.high_watermark
        {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Pace new rounds: wait at least 300μs since the last PrePrepare.
        // This prevents the primary from outrunning backups during the burst.
        {
            let now = Instant::now();
            if now.duration_since(self.last_pre_prepare_time).as_micros() < 500 {
                return StepResult {
                    ok: true,
                    outbound: GenericOutbound::None,
                };
            }
        }

        // Use buffered client digest if available, otherwise synthetic
        let digest = self.pending_digest.take().unwrap_or(self.action_index);
        // Shift current → prev before starting new round
        self.prev_pre_prepare = self.cur_pre_prepare.take();
        self.cur_pre_prepare = Some((self.state.view, self.state.seq_num, digest));
        let _sent = self.state.CPrePrepare(&config.constants, &digest);
        self.last_pre_prepare_time = Instant::now();

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
        let mut state = pbft_gen::CInit(&config.constants);
        // CInit always sets is_primary=true; override for non-primary nodes.
        // Primary is the node whose index equals view % n (initially view=0, so node 0).
        state.is_primary = config.my_index == (state.view % config.constants.n);
        Some(PBFTHost {
            state,
            action_index: 0,
            last_metrics_time: Instant::now(),
            last_metrics_seq_num: 0,
            pending_digest: None,
            last_pre_prepare_time: Instant::now(),
            last_resend_time: Instant::now(),
            last_catchup_time: Instant::now(),
            cur_pre_prepare: None,
            prev_pre_prepare: None,
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
            let seq = self.state.seq_num;
            let delta = seq.wrapping_sub(self.last_metrics_seq_num);
            let elapsed_secs = elapsed.as_secs_f64();
            let role = if self.is_primary() { "primary" } else { "replica" };
            eprintln!(
                "[METRICS] role={} seq_num={} delta={} elapsed={:.2}s throughput={:.1} ops/s",
                role, seq, delta, elapsed_secs, delta as f64 / elapsed_secs,
            );
            self.last_metrics_time = now;
            self.last_metrics_seq_num = seq;
        }

        // Handle incoming message
        let mut result = None;
        if let Some(pkt) = packet {
            // ClientRequest and ClientReply come from external clients,
            // not from known peers — handle them before sender resolution.
            match &pkt.msg {
                PBFTMessage::ClientRequest { digest } => {
                    let src = pkt.src;
                    result = Some(self.handle_client_request(config, *digest, src.clone_up_to_view()));
                }
                PBFTMessage::ClientReply { .. } => {
                    // ClientReply is outbound-only; ignore if received
                    result = Some(StepResult {
                        ok: true,
                        outbound: GenericOutbound::None,
                    });
                }
                _ => {
                    if Self::resolve_sender_index(config, &pkt.src).is_some() {
                        let src = pkt.src;
                        result = Some(match pkt.msg {
                            PBFTMessage::PrePrepare { view, seq, digest } => {
                                self.handle_pre_prepare(config, view, seq, digest)
                            }
                            PBFTMessage::Prepare {
                                view,
                                seq,
                                digest: _,
                                sender,
                            } => self.handle_prepare(config, view, seq, sender, &src),
                            PBFTMessage::Commit {
                                view,
                                seq,
                                sender,
                            } => self.handle_commit(config, view, seq, sender, &src),
                            // ClientRequest/ClientReply already handled above
                            _ => StepResult {
                                ok: true,
                                outbound: GenericOutbound::None,
                            },
                        });
                    }
                }
            }
        }

        // If the handler produced no outbound (e.g. client request buffered, or
        // duplicate message), check if we should piggyback a periodic resend.
        // This ensures resends fire even when the socket is flooded with client
        // packets that would otherwise prevent the timer path from executing.
        let has_outbound = result.as_ref().map_or(false, |r| !matches!(r.outbound, GenericOutbound::None));
        if !has_outbound
            && (matches!(self.state.phase, CPhase::Prepare) || matches!(self.state.phase, CPhase::Commit))
            && now.duration_since(self.last_resend_time).as_millis() >= 1
        {
            self.last_resend_time = now;
            let others = Self::other_peers(config);
            let msg = if matches!(self.state.phase, CPhase::Prepare) {
                PBFTMessage::Prepare {
                    view: self.state.view,
                    seq: self.state.seq_num,
                    digest: self.state.request_digest,
                    sender: config.constants.node_id,
                }
            } else {
                PBFTMessage::Commit {
                    view: self.state.view,
                    seq: self.state.seq_num,
                    sender: config.constants.node_id,
                }
            };
            return StepResult {
                ok: true,
                outbound: GenericOutbound::Broadcast {
                    dsts: others,
                    msg,
                },
            };
        }

        if let Some(r) = result {
            return r;
        }

        // No message -- run timer-driven actions round-robin.
        let result = match self.action_index % 3 {
            0 => self.try_pre_prepare_and_new_round(config),
            1 => self.try_checkpoint(config),
            _ => self.try_new_round(config),
        };
        self.action_index = self.action_index.wrapping_add(1);
        result
    }
}
