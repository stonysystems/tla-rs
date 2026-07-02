//! PrimaryBackup protocol host implementation.
//!
//! Bridges the generic framework traits with the transpiler-generated
//! verified exec functions. The host scheduler maps incoming network
//! messages to the appropriate C* function calls.

use crate::common::framework::args_t::*;
use crate::common::framework::protocol_trait::*;
use crate::common::native::io_s::*;
use crate::generated::PrimaryBackup::primarybackup_gen;
use crate::generated::PrimaryBackup::types_gen::*;
use crate::implementation::PrimaryBackup::message::*;
use std::time::Instant;

/// PrimaryBackup protocol configuration.
pub struct PrimaryBackupConfig {
    /// All peer endpoints (index 0 = primary, index 1 = backup).
    pub peers: Vec<EndPoint>,
    /// This node's index in the peers list.
    pub my_index: u64,
    /// The protocol constants.
    pub constants: CConstants,
}

impl ProtocolConfig for PrimaryBackupConfig {
    fn parse_config(me: &EndPoint, args: &Args) -> Option<Self> {
        // Expected args format: [endpoint0, endpoint1, ...]
        // Index 0 is the initial primary, index 1 is the backup.
        // The endpoint matching `me` determines my_index.
        if args.len() < 2 {
            eprintln!("PrimaryBackup: need at least 2 args (primary + backup endpoints)");
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
                eprintln!("PrimaryBackup: own endpoint not found in args");
                return None;
            }
        };

        // Default max_log_len; could be made configurable via extra args.
        let constants = CConstants {
            max_log_len: 100_000_000,
        };

        Some(PrimaryBackupConfig {
            peers,
            my_index,
            constants,
        })
    }

    fn get_peers(&self) -> &Vec<EndPoint> {
        &self.peers
    }
}

/// The PrimaryBackup host wrapping protocol state.
pub struct PrimaryBackupHost {
    /// The verified protocol state.
    pub state: CState,
    /// Round-robin action index for internal (non-message-driven) actions.
    pub action_index: u64,
    /// Timestamp of last metrics output (for periodic throughput reporting).
    last_metrics_time: Instant,
    /// log_length at last metrics output (for delta computation).
    last_metrics_log_length: u64,
    /// Client endpoint for the current pending request (if any).
    pending_client: Option<EndPoint>,
}

impl PrimaryBackupHost {
    /// Check if this node is currently the primary based on its state role.
    fn is_primary(&self) -> bool {
        matches!(self.state.role, CNodeRole::Primary)
    }

    /// Check if this node is currently the backup based on its state role.
    fn is_backup(&self) -> bool {
        matches!(self.state.role, CNodeRole::Backup)
    }

    /// Check if this node is inactive (failed primary or promoted backup).
    fn is_inactive(&self) -> bool {
        matches!(self.state.role, CNodeRole::Inactive)
    }

    /// Get the backup endpoint (index 1).
    fn backup_endpoint(config: &PrimaryBackupConfig) -> EndPoint {
        config.peers[1].clone_up_to_view()
    }

    /// Get the primary endpoint (index 0).
    fn primary_endpoint(config: &PrimaryBackupConfig) -> EndPoint {
        config.peers[0].clone_up_to_view()
    }

    // ---------------------------------------------------------------
    // Primary actions
    // ---------------------------------------------------------------

    /// Primary: receive a ClientRequest and call CPrimaryWrite.
    fn primary_handle_client_request(
        &mut self,
        config: &PrimaryBackupConfig,
        value: u64,
        client_ep: EndPoint,
    ) -> StepResult<PrimaryBackupMessage> {
        // Guards from CPrimaryWrite requires:
        //   s.role is Primary, s.acked == true, s.has_pending == false,
        //   s.log_length < c.max_log_len
        if !self.is_primary()
            || !self.state.acked
            || self.state.has_pending
            || self.state.log_length >= config.constants.max_log_len
        {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (ns, _sent) = primarybackup_gen::CPrimaryWrite(&self.state, &config.constants, &value);
        self.state = ns;
        self.pending_client = Some(client_ep);

        // After writing, immediately attempt to send replicate to backup.
        self.primary_try_send_replicate(config)
    }

    /// Primary: send Replicate message to backup.
    /// Guards from CPrimarySendReplicate requires:
    ///   s.role is Primary, s.has_pending == true, s.acked == false
    fn primary_try_send_replicate(
        &mut self,
        config: &PrimaryBackupConfig,
    ) -> StepResult<PrimaryBackupMessage> {
        if !self.is_primary() || !self.state.has_pending || self.state.acked {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        // Capture pending_value before the state transition for the outbound message.
        let value = self.state.pending_value;

        let (ns, _sent) = primarybackup_gen::CPrimarySendReplicate(&self.state, &config.constants);
        self.state = ns;

        // Send Replicate to backup
        let dst = Self::backup_endpoint(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Send {
                dst,
                msg: PrimaryBackupMessage::Replicate { value },
            },
        }
    }

    /// Primary: receive Ack from backup.
    /// Guards from CPrimaryReceiveAck requires:
    ///   s.role is Primary, s.has_pending == true
    fn primary_receive_ack(
        &mut self,
        config: &PrimaryBackupConfig,
    ) -> StepResult<PrimaryBackupMessage> {
        if !self.is_primary() || !self.state.has_pending {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (ns, _sent) = primarybackup_gen::CPrimaryReceiveAck(&self.state, &config.constants);
        self.state = ns;

        // After receiving ack, try to commit
        self.primary_try_commit(config)
    }

    /// Primary: commit the pending value.
    /// Guards from CPrimaryCommit requires:
    ///   s.role is Primary, s.acked == true, s.has_pending == true,
    ///   s.log_length < u64::MAX
    fn primary_try_commit(
        &mut self,
        config: &PrimaryBackupConfig,
    ) -> StepResult<PrimaryBackupMessage> {
        if !self.is_primary()
            || !self.state.acked
            || !self.state.has_pending
            || self.state.log_length >= u64::MAX
        {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let committed_value = self.state.pending_value;
        let client_ep = self.pending_client.take();

        let (ns, _sent) = primarybackup_gen::CPrimaryCommit(&self.state, &config.constants);
        self.state = ns;

        // Send ClientReply to the requesting client
        match client_ep {
            Some(dst) => StepResult {
                ok: true,
                outbound: GenericOutbound::Send {
                    dst,
                    msg: PrimaryBackupMessage::ClientReply { value: committed_value },
                },
            },
            None => StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            },
        }
    }

    /// Primary: simulate failure (transition to Inactive).
    /// Guards from CPrimaryFail requires:
    ///   s.role is Primary
    fn primary_fail(&mut self, config: &PrimaryBackupConfig) -> StepResult<PrimaryBackupMessage> {
        if !self.is_primary() {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (ns, _sent) = primarybackup_gen::CPrimaryFail(&self.state, &config.constants);
        self.state = ns;

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    // ---------------------------------------------------------------
    // Backup actions
    // ---------------------------------------------------------------

    /// Backup: receive Replicate message from primary.
    /// Guards from CBackupReceiveReplicate requires:
    ///   s.role is Primary (shared-state: both roles see same state),
    ///   s.backup_log_length < u64::MAX
    fn backup_receive_replicate(
        &mut self,
        config: &PrimaryBackupConfig,
        value: u64,
    ) -> StepResult<PrimaryBackupMessage> {
        if self.state.backup_log_length >= u64::MAX {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (ns, _sent) = primarybackup_gen::CBackupReceiveReplicate(&self.state, &config.constants, &value);
        self.state = ns;

        // After receiving replicate, try to send ack
        self.backup_try_send_ack(config)
    }

    /// Backup: send Ack back to primary.
    /// Guards from CBackupSendAck requires:
    ///   s.role is Primary (shared-state),
    ///   s.backup_synced == true
    fn backup_try_send_ack(
        &mut self,
        config: &PrimaryBackupConfig,
    ) -> StepResult<PrimaryBackupMessage> {
        if !self.state.backup_synced {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (ns, _sent) = primarybackup_gen::CBackupSendAck(&self.state, &config.constants);
        self.state = ns;

        // Send Ack to primary
        let dst = Self::primary_endpoint(config);
        StepResult {
            ok: true,
            outbound: GenericOutbound::Send {
                dst,
                msg: PrimaryBackupMessage::Ack,
            },
        }
    }

    /// Backup: promote to primary after detecting primary failure.
    /// Guards from CBackupPromote requires:
    ///   s.role is Inactive, s.view < u64::MAX
    fn backup_try_promote(
        &mut self,
        config: &PrimaryBackupConfig,
    ) -> StepResult<PrimaryBackupMessage> {
        if !self.is_inactive() || self.state.view >= u64::MAX {
            return StepResult {
                ok: true,
                outbound: GenericOutbound::None,
            };
        }

        let (ns, _sent) = primarybackup_gen::CBackupPromote(&self.state, &config.constants);
        self.state = ns;

        StepResult {
            ok: true,
            outbound: GenericOutbound::None,
        }
    }

    // ---------------------------------------------------------------
    // Dispatch
    // ---------------------------------------------------------------

    /// Primary dispatch: handle incoming messages or run round-robin actions.
    fn primary_step(
        &mut self,
        config: &PrimaryBackupConfig,
        packet: Option<GenericPacket<PrimaryBackupMessage>>,
    ) -> StepResult<PrimaryBackupMessage> {
        // Handle incoming messages
        if let Some(pkt) = packet {
            match pkt.msg {
                PrimaryBackupMessage::ClientRequest { value } => {
                    return self.primary_handle_client_request(config, value, pkt.src);
                }
                PrimaryBackupMessage::Ack => {
                    return self.primary_receive_ack(config);
                }
                _ => {
                    // Primary ignores Replicate messages
                    return StepResult {
                        ok: true,
                        outbound: GenericOutbound::None,
                    };
                }
            }
        }

        // No message -- run internal primary actions round-robin
        let result = match self.action_index % 3 {
            0 => self.primary_try_send_replicate(config),
            1 => self.primary_try_commit(config),
            _ => {
                // Slot 2: no spontaneous primary fail in normal operation.
                // In a real system, failure would be injected externally.
                StepResult {
                    ok: true,
                    outbound: GenericOutbound::None,
                }
            }
        };
        self.action_index = self.action_index.wrapping_add(1);
        result
    }

    /// Backup dispatch: handle incoming messages or run round-robin actions.
    fn backup_step(
        &mut self,
        config: &PrimaryBackupConfig,
        packet: Option<GenericPacket<PrimaryBackupMessage>>,
    ) -> StepResult<PrimaryBackupMessage> {
        // Handle incoming messages
        if let Some(pkt) = packet {
            match pkt.msg {
                PrimaryBackupMessage::Replicate { value } => {
                    return self.backup_receive_replicate(config, value);
                }
                _ => {
                    // Backup ignores Ack and ClientRequest messages
                    return StepResult {
                        ok: true,
                        outbound: GenericOutbound::None,
                    };
                }
            }
        }

        // No message -- backup tries to send ack if synced
        let result = match self.action_index % 2 {
            0 => self.backup_try_send_ack(config),
            _ => self.backup_try_promote(config),
        };
        self.action_index = self.action_index.wrapping_add(1);
        result
    }

    /// Inactive node dispatch: attempt promotion.
    fn inactive_step(
        &mut self,
        config: &PrimaryBackupConfig,
        _packet: Option<GenericPacket<PrimaryBackupMessage>>,
    ) -> StepResult<PrimaryBackupMessage> {
        // Inactive nodes only try to promote
        self.backup_try_promote(config)
    }
}

impl ProtocolHost for PrimaryBackupHost {
    type Msg = PrimaryBackupMessage;
    type Cfg = PrimaryBackupConfig;

    fn init(config: &Self::Cfg) -> Option<Self> {
        let mut state = primarybackup_gen::CInit(&config.constants);
        // CInit always creates Primary role; override for non-primary nodes.
        // Index 0 = primary, index 1 = backup, others = inactive.
        if config.my_index == 1 {
            state.role = CNodeRole::Backup;
        } else if config.my_index > 1 {
            state.role = CNodeRole::Inactive;
        }
        Some(PrimaryBackupHost {
            state,
            action_index: 0,
            last_metrics_time: Instant::now(),
            last_metrics_log_length: 0,
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
            // The spec models a shared state: `log_length` is the primary's log
            // counter, `backup_log_length` is the backup's. Each node reports
            // the field relevant to its role.
            let (role, log_len) = if self.is_primary() {
                ("primary", self.state.log_length)
            } else if self.is_backup() {
                ("backup", self.state.backup_log_length)
            } else {
                ("inactive", self.state.log_length)
            };
            let delta = log_len - self.last_metrics_log_length;
            let elapsed_secs = elapsed.as_secs_f64();
            eprintln!(
                "[METRICS] role={} log_length={} delta={} elapsed={:.2}s throughput={:.1} ops/s",
                role, log_len, delta, elapsed_secs, delta as f64 / elapsed_secs,
            );
            self.last_metrics_time = now;
            self.last_metrics_log_length = log_len;
        }

        if self.is_primary() {
            self.primary_step(config, packet)
        } else if self.is_backup() {
            self.backup_step(config, packet)
        } else {
            self.inactive_step(config, packet)
        }
    }
}
