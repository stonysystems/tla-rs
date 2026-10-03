//! Native, ownership-preserving boundary between protocol transitions and Lion.
//!
//! No socket operations, callbacks, or threads live here. Each call completes a
//! bounded scheduling turn; the caller owns waiting and outbound buffer lifetimes.
use crate::common::framework::generic_host::GenericHostState;
use crate::common::framework::protocol_trait::ProtocolHost;
use crate::common::native::io_s::{EndPoint, NetClient, WirePacket};
use crate::implementation::{
    ChainReplication::host::ChainHost, EPaxos::host::EPaxosHost,
    LeaderElection::host::LeaderElectionHost, PBFT::host::PBFTHost,
    Paxos::host::PaxosHost, PrimaryBackup::host::PrimaryBackupHost,
    Raft::host::RaftHost, TwoPhase::host::TwoPhaseHost,
    VerticalPaxos::host::VerticalPaxosHost,
};
use crate::implementation::RSL::{
    ExecutorImpl::CIncompleteBatchTimer, host_i::HostState,
};

enum ReplicaState {
    Rsl(HostState),
    Raft(GenericHostState<RaftHost>),
    Epaxos(GenericHostState<EPaxosHost>),
    Pbft(GenericHostState<PBFTHost>),
    Paxos(GenericHostState<PaxosHost>),
    VerticalPaxos(GenericHostState<VerticalPaxosHost>),
    TwoPhase(GenericHostState<TwoPhaseHost>),
    PrimaryBackup(GenericHostState<PrimaryBackupHost>),
    Chain(GenericHostState<ChainHost>),
    Election(GenericHostState<LeaderElectionHost>),
}

pub struct NativeReplica {
    state: ReplicaState,
    net: NetClient,
    runnable: bool,
}

pub struct RslParameters {
    pub max_batch_size: u64,
    pub max_batch_delay: u64,
    pub max_log_length: u64,
    pub baseline_view_timeout_period: u64,
    pub heartbeat_period: u64,
}

fn init<H: ProtocolHost>(net: &NetClient, peers: &Vec<Vec<u8>>) -> Result<GenericHostState<H>, String> {
    GenericHostState::<H>::init(net, peers).ok_or_else(|| "invalid protocol configuration".to_owned())
}

// Run all of the generic hosts' round-robin internal action slots even when
// receive traffic is continuous. Their actual time guards remain in the hosts.
fn generic_turn<H: ProtocolHost>(host: &mut GenericHostState<H>, net: &mut NetClient) -> bool {
    for _ in 0..9 {
        net.reset();
        if !host.next(net) {
            return false;
        }
    }
    true
}

impl NativeReplica {
    pub fn new(protocol: &str, me: Vec<u8>, peers: Vec<Vec<u8>>) -> Result<Self, String> {
        if peers.is_empty() || !peers.contains(&me) {
            return Err("local endpoint must occur in the nonempty replica list".to_owned());
        }
        for (index, peer) in peers.iter().enumerate() {
            if peer.is_empty() || peers[..index].contains(peer) {
                return Err("replica endpoints must be nonempty and unique".to_owned());
            }
        }
        let net = NetClient::new(EndPoint { id: me });
        let state = match protocol {
            "rsl" => ReplicaState::Rsl(HostState::init_impl(&net, &peers)
                .ok_or_else(|| "invalid RSL configuration".to_owned())?),
            "raft" => ReplicaState::Raft(init(&net, &peers)?),
            "epaxos" => ReplicaState::Epaxos(init(&net, &peers)?),
            "pbft" => ReplicaState::Pbft(init(&net, &peers)?),
            "paxos" => ReplicaState::Paxos(init(&net, &peers)?),
            "verticalpaxos" => ReplicaState::VerticalPaxos(init(&net, &peers)?),
            "twophase" => ReplicaState::TwoPhase(init(&net, &peers)?),
            "primarybackup" => ReplicaState::PrimaryBackup(init(&net, &peers)?),
            "chainreplication" => ReplicaState::Chain(init(&net, &peers)?),
            "leaderelection" => ReplicaState::Election(init(&net, &peers)?),
            _ => return Err(format!("unknown protocol: {protocol}")),
        };
        Ok(Self { state, net, runnable: true })
    }

    pub fn rsl_parameters(&self) -> Option<RslParameters> {
        match &self.state {
            ReplicaState::Rsl(host) => {
                let params = &host.replica_impl.replica.constants.all.params;
                Some(RslParameters {
                    max_batch_size: params.max_batch_size,
                    max_batch_delay: params.max_batch_delay,
                    max_log_length: params.max_log_length,
                    baseline_view_timeout_period: params.baseline_view_timeout_period,
                    heartbeat_period: params.heartbeat_period,
                })
            }
            _ => None,
        }
    }

    pub fn step(&mut self, now_ms: u64, incoming: Option<WirePacket>) -> Result<(), String> {
        if now_ms < self.net.native.clock_ms {
            return Err("protocol clock must be monotonic".to_owned());
        }
        self.net.native.clock_ms = now_ms;
        self.net.native.incoming = incoming;
        self.runnable = false;
        let ok = match &mut self.state {
            ReplicaState::Rsl(host) => {
                let replica = &host.replica_impl.replica;
                let before = (
                    replica.executor.ops_complete,
                    replica.proposer.current_state,
                    replica.proposer.election_state.current_view,
                    replica.proposer.next_operation_number_to_propose,
                    replica.acceptor.log_truncation_point,
                );
                let mut ok = true;
                // Exactly one complete round, including receive, all spontaneous
                // actions, and clocks. The next call always starts at receive.
                for _ in 0..10 {
                    self.net.reset();
                    if !host.next_impl(&mut self.net).0 {
                        ok = false;
                        break;
                    }
                }
                let replica = &host.replica_impl.replica;
                let after = (
                    replica.executor.ops_complete,
                    replica.proposer.current_state,
                    replica.proposer.election_state.current_view,
                    replica.proposer.next_operation_number_to_propose,
                    replica.acceptor.log_truncation_point,
                );
                // Later actions can enable an earlier action (e.g. a view
                // change at action 8 enables phase 1 at action 1). Do not sleep
                // before that work gets another bounded scheduling turn.
                self.runnable = before != after;
                ok
            }
            ReplicaState::Raft(host) => generic_turn(host, &mut self.net),
            ReplicaState::Epaxos(host) => generic_turn(host, &mut self.net),
            ReplicaState::Pbft(host) => generic_turn(host, &mut self.net),
            ReplicaState::Paxos(host) => generic_turn(host, &mut self.net),
            ReplicaState::VerticalPaxos(host) => generic_turn(host, &mut self.net),
            ReplicaState::TwoPhase(host) => generic_turn(host, &mut self.net),
            ReplicaState::PrimaryBackup(host) => generic_turn(host, &mut self.net),
            ReplicaState::Chain(host) => generic_turn(host, &mut self.net),
            ReplicaState::Election(host) => generic_turn(host, &mut self.net),
        };
        if !ok {
            return Err("protocol step or outbound enqueue failed".to_owned());
        }
        if self.net.native.incoming.is_some() {
            return Err("protocol scheduling turn did not consume its input".to_owned());
        }
        Ok(())
    }

    pub fn outbound(&mut self) -> &mut Vec<WirePacket> {
        &mut self.net.native.outbound
    }

    pub fn recycle(&mut self, mut packet: WirePacket) {
        self.net.recycle_buffer(packet.bytes);
        if self.net.native.endpoints.len() < 256 && packet.peer.capacity() <= 1024 {
            packet.peer.clear();
            self.net.native.endpoints.push(packet.peer);
        }
    }

    pub fn take_buffer(&mut self) -> Vec<u8> {
        self.net.take_buffer()
    }

    pub fn next_deadline(&self, now_ms: u64) -> u64 {
        if self.runnable {
            return now_ms;
        }
        if let ReplicaState::Rsl(host) = &self.state {
            let replica = &host.replica_impl.replica;
            let mut deadline = replica.nextHeartbeatTime
                .min(replica.proposer.election_state.epoch_end_time);
            if let CIncompleteBatchTimer::CIncompleteBatchTimerOn { when } =
                replica.proposer.incomplete_batch_timer
            {
                deadline = deadline.min(when);
            }
            // An expired guard can be disabled by another protocol condition.
            // Retry at millisecond precision rather than spinning on its past deadline.
            deadline.max(now_ms.saturating_add(1))
        } else {
            // Generic hosts expose round-robin internal actions and guard real
            // timers themselves (Raft elections, PBFT retransmissions). A bounded
            // 1ms maintenance turn preserves those guards without busy polling.
            now_ms.saturating_add(1)
        }
    }
}
