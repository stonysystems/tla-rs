//! Raft protocol host — thin I/O shell over verified composite functions.
use crate::common::framework::args_t::*;
use crate::common::framework::protocol_trait::*;
use crate::common::native::io_s::*;
use crate::generated::Raft::raft_gen;
use crate::generated::Raft::types_gen::*;
use crate::implementation::Raft::membership_helpers::Chas_active_commit_quorum;
use crate::implementation::Raft::message::*;
use std::collections::HashSet;

const ELECTION_TIMEOUT_MIN_MS: u128 = 1000;
const ELECTION_TIMEOUT_MAX_MS: u128 = 2000;
const HEARTBEAT_INTERVAL_MS: u128 = 100;

fn random_election_timeout() -> u128 {
    let ns = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default().subsec_nanos() as u128;
    ELECTION_TIMEOUT_MIN_MS + (ns % (ELECTION_TIMEOUT_MAX_MS - ELECTION_TIMEOUT_MIN_MS + 1))
}

fn to_wire(cm: &CRaftMessage) -> RaftMessage {
    match cm {
        CRaftMessage::RequestVote { term, candidate, last_log_index, last_log_term } =>
            RaftMessage::RequestVote { term: *term, candidate_id: *candidate, last_log_index: *last_log_index, last_log_term: *last_log_term },
        CRaftMessage::VoteResponse { term, granted, voter, voter_last_log_index, voter_last_log_term } =>
            RaftMessage::VoteResponse { term: *term, granted: *granted, voter: *voter, voter_last_log_index: *voter_last_log_index, voter_last_log_term: *voter_last_log_term },
        CRaftMessage::AppendEntries {
            term,
            leader,
            prev_index,
            prev_term,
            value,
            payload,
            has_entry,
            leader_commit,
        } =>
            RaftMessage::AppendEntries {
                term: *term,
                leader_id: *leader,
                prev_log_index: *prev_index,
                prev_log_term: *prev_term,
                value: *value,
                payload: payload.clone(),
                has_entry: *has_entry,
                leader_commit: *leader_commit,
            },
        CRaftMessage::AppendResponse { term, success, match_index, follower } =>
            RaftMessage::AppendResponse { term: *term, success: *success, match_index: *match_index, follower: *follower },
    }
}

fn from_wire(msg: &RaftMessage) -> Option<CRaftMessage> {
    match msg {
        RaftMessage::RequestVote { term, candidate_id, last_log_index, last_log_term } =>
            Some(CRaftMessage::RequestVote { term: *term, candidate: *candidate_id, last_log_index: *last_log_index, last_log_term: *last_log_term }),
        RaftMessage::VoteResponse { term, granted, voter, voter_last_log_index, voter_last_log_term } =>
            Some(CRaftMessage::VoteResponse { term: *term, granted: *granted, voter: *voter, voter_last_log_index: *voter_last_log_index, voter_last_log_term: *voter_last_log_term }),
        RaftMessage::AppendEntries {
            term,
            leader_id,
            prev_log_index,
            prev_log_term,
            value,
            payload,
            has_entry,
            leader_commit,
        } =>
            Some(CRaftMessage::AppendEntries {
                term: *term,
                leader: *leader_id,
                prev_index: *prev_log_index,
                prev_term: *prev_log_term,
                value: *value,
                payload: payload.clone(),
                has_entry: *has_entry,
                leader_commit: *leader_commit,
            }),
        RaftMessage::AppendResponse { term, success, match_index, follower } =>
            Some(CRaftMessage::AppendResponse { term: *term, success: *success, match_index: *match_index, follower: *follower }),
        _ => None,
    }
}

pub struct RaftConfig { pub peers: Vec<EndPoint>, pub my_index: u64, pub constants: CConstants }

impl ProtocolConfig for RaftConfig {
    fn parse_config(me: &EndPoint, args: &Args) -> Option<Self> {
        if args.len() < 2 { return None; }
        let mut peers = Vec::new();
        let mut my_index = None;
        for i in 0..args.len() {
            let ep = EndPoint { id: args[i].clone() };
            if ep.id == me.id { my_index = Some(i as u64); }
            peers.push(ep);
        }
        let my_index = my_index?;
        let n = peers.len() as u64;
        let mut servers = HashSet::new();
        for i in 0..n { servers.insert(i); }
        Some(RaftConfig { peers, my_index,
            constants: CConstants { servers, quorum_size: n / 2 + 1, my_id: my_index } })
    }
    fn get_peers(&self) -> &Vec<EndPoint> { &self.peers }
}

pub struct RaftHost {
    pub state: CState, pub client_request_counter: u64,
    pub last_heartbeat: std::time::Instant, pub last_heartbeat_sent: std::time::Instant,
    pub election_timeout_ms: u128,
}

impl RaftHost {
    fn leader_heartbeat(&mut self, config: &RaftConfig) -> Vec<GenericPacket<RaftMessage>> {
        let mut pkts = Vec::new();
        let me = config.my_index;
        for i in 0..config.peers.len() {
            let fid = i as u64;
            if fid == me || !config.constants.servers.contains(&fid) { continue; }
            let ni = self.state.next_index.get(&fid).copied().unwrap_or(0);
            let ll = self.state.log.len() as u64;
            let has = ni < ll;
            let val = if has { self.state.log[ni as usize].value } else { 0 };
            let payload = if has {
                self.state.log[ni as usize].payload.clone()
            } else {
                CLogValue::Data {
                    value: 0,
                }
            };
            let pi = if ni > 0 { ni } else { 0 };
            let pt = if ni > 0 && ni - 1 < ll { self.state.log[(ni - 1) as usize].term } else { 0 };
            let (ns, sent) = raft_gen::CSendAppendEntries(
                &self.state,
                &config.constants,
                &fid,
                &val,
                &payload,
                &pi,
                &pt,
                has,
            );
            self.state = ns;
            if !sent.is_empty() {
                pkts.push(GenericPacket { dst: config.peers[i].clone_up_to_view(),
                    src: config.peers[me as usize].clone_up_to_view(), msg: to_wire(&sent[0]) });
            }
        }
        pkts
    }

    fn find_commit_index(&self, config: &RaftConfig) -> Option<u64> {
        // A commit search is governed by the membership phase derived from
        // the current committed prefix. Stop the search at the first
        // Configuration entry so one old-phase quorum cannot skip across a
        // membership boundary.
        let mut commit_limit = self.state.log.len() as u64;
        let mut index = self.state.commit_index;

        while index < commit_limit {
            if matches!(
                self.state.log[index as usize].payload,
                CLogValue::Configuration { .. }
            ) {
                commit_limit = index + 1;
                break;
            }
            index += 1;
        }

        let mut n = commit_limit;
        while n > self.state.commit_index {
            if self.state.log[(n - 1) as usize].term == self.state.current_term {
                if Chas_active_commit_quorum(
                    &self.state,
                    &config.constants,
                    &n,
                ) {
                    return Some(n);
                }
            }
            n -= 1;
        }
        None
    }
}

impl ProtocolHost for RaftHost {
    type Msg = RaftMessage;
    type Cfg = RaftConfig;

    fn init(config: &Self::Cfg) -> Option<Self> {
        Some(RaftHost { state: raft_gen::CInit(&config.constants), client_request_counter: 0,
            last_heartbeat: std::time::Instant::now(), last_heartbeat_sent: std::time::Instant::now(),
            election_timeout_ms: random_election_timeout() })
    }

    fn next(&mut self, config: &Self::Cfg, packet: Option<GenericPacket<Self::Msg>>) -> StepResult<Self::Msg> {
        // Leader heartbeats (periodic, regardless of message traffic)
        let mut hb = Vec::new();
        if matches!(self.state.role, CServerRole::Leader)
            && self.last_heartbeat_sent.elapsed().as_millis() >= HEARTBEAT_INTERVAL_MS {
            self.last_heartbeat_sent = std::time::Instant::now();
            hb = self.leader_heartbeat(config);
        }
        if let Some(pkt) = packet {
            // Client requests (not part of spec's LHandleMessage)
            if let RaftMessage::ClientRequest { client_id, seq_no, value } = pkt.msg {
                let ok = matches!(self.state.role, CServerRole::Leader);
                if ok { let (ns, _sent) = raft_gen::CClientRequest(&self.state, &config.constants, &value); self.state = ns; }
                return merge(StepResult { ok: true, outbound: GenericOutbound::Send {
                    dst: pkt.src.clone_up_to_view(), msg: RaftMessage::ClientResponse { client_id, seq_no, success: ok } } }, hb);
            }
            // Protocol messages → verified CHandleMessage
            if let Some(cmsg) = from_wire(&pkt.msg) {
                let old_term = self.state.current_term;
                let old_voted = self.state.has_voted;
                let (ns, sent) = raft_gen::CHandleMessage(&self.state, &config.constants, &cmsg);
                self.state = ns;
                // Reset election timer on valid heartbeat, vote grant, or step-down
                let reset = match &pkt.msg {
                    RaftMessage::AppendEntries { term, .. } if *term >= old_term => true,
                    _ => self.state.current_term > old_term || (!old_voted && self.state.has_voted),
                };
                if reset { self.last_heartbeat = std::time::Instant::now(); }
                let out = if sent.is_empty() { GenericOutbound::None }
                    else { GenericOutbound::Send { dst: pkt.src.clone_up_to_view(), msg: to_wire(&sent[0]) } };
                return merge(StepResult { ok: true, outbound: out }, hb);
            }
            return merge(StepResult { ok: true, outbound: GenericOutbound::None }, hb);
        }
        // Timer-driven actions (no incoming message)
        match &self.state.role {
            CServerRole::Follower | CServerRole::Candidate => {
                if self.last_heartbeat.elapsed().as_millis() >= self.election_timeout_ms
                    && self.state.current_term < u64::MAX {
                    self.last_heartbeat = std::time::Instant::now();
                    self.election_timeout_ms = random_election_timeout();
                    eprintln!("Raft: Node {} election timeout, term {}", config.my_index, self.state.current_term + 1);
                    let (ns, sent) = raft_gen::CTimeout(&self.state, &config.constants);
                    self.state = ns;
                    if !sent.is_empty() {
                        let others: Vec<EndPoint> = (0..config.peers.len())
                            .filter(|&i| i as u64 != config.my_index)
                            .map(|i| config.peers[i].clone_up_to_view()).collect();
                        return StepResult { ok: true, outbound: GenericOutbound::Broadcast { dsts: others, msg: to_wire(&sent[0]) } };
                    }
                }
                StepResult { ok: true, outbound: GenericOutbound::None }
            }
            CServerRole::Leader => {
                if let Some(ci) = self.find_commit_index(config) {
                    let (ns, _sent) = raft_gen::CTryAdvanceCommitIndex(&self.state, &config.constants, &ci);
                    self.state = ns;
                    eprintln!("Raft: Node {} commit_index -> {}", config.my_index, ci);
                }
                merge(StepResult { ok: true, outbound: GenericOutbound::None }, hb)
            }
        }
    }
}

fn merge(r: StepResult<RaftMessage>, p: Vec<GenericPacket<RaftMessage>>) -> StepResult<RaftMessage> {
    if p.is_empty() { return r; }
    let mut all = p;
    match r.outbound {
        GenericOutbound::None => {}
        GenericOutbound::Send { dst, msg } => all.push(GenericPacket { dst, src: EndPoint { id: Vec::new() }, msg }),
        GenericOutbound::Broadcast { dsts, msg } =>
            for d in dsts { all.push(GenericPacket { dst: d, src: EndPoint { id: Vec::new() }, msg: msg.clone() }); },
        GenericOutbound::Sequence { packets } => all.extend(packets),
    }
    StepResult { ok: true, outbound: GenericOutbound::Sequence { packets: all } }
}
