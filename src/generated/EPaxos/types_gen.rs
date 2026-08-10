// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::common::collections::hashsets::clone_hashset_u64;
use crate::protocol::EPaxos::epaxos::*;
use crate::protocol::EPaxos::types::*;
use std::collections::HashSet;
use vstd::prelude::*;
use vstd::set::*;
use vstd::set_lib::*;

verus! {

pub struct CState {
    pub ballot: u64,
    pub phase: CInstancePhase,
    pub cmd: u64,
    pub seq: u64,
    pub dep_count: u64,
    pub is_leader: bool,
    pub committed_count: u64,
    pub executed_count: u64,
    pub preaccept_senders: HashSet<u64>,
    pub accept_senders: HashSet<u64>,
    pub has_conflict: bool,
    pub max_resp_seq: u64,
}

impl Clone for CState {
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
        res.ballot == self.ballot,
        res.phase == self.phase,
        res.cmd == self.cmd,
        res.seq == self.seq,
        res.dep_count == self.dep_count,
        res.is_leader == self.is_leader,
        res.committed_count == self.committed_count,
        res.executed_count == self.executed_count,
        res.has_conflict == self.has_conflict,
        res.max_resp_seq == self.max_resp_seq,
    {
        CState {
            ballot: self.ballot,
            phase: self.phase,
            cmd: self.cmd,
            seq: self.seq,
            dep_count: self.dep_count,
            is_leader: self.is_leader,
            committed_count: self.committed_count,
            executed_count: self.executed_count,
            preaccept_senders: clone_hashset_u64(&self.preaccept_senders),
            accept_senders: clone_hashset_u64(&self.accept_senders),
            has_conflict: self.has_conflict,
            max_resp_seq: self.max_resp_seq,
        }
    }
}

impl CState {
    pub open spec fn valid(&self) -> bool {
        &&& self.phase.valid()
    }
}

impl View for CState {
    type V = LState;

    open spec fn view(&self) -> LState {
        LState {
            ballot: self.ballot as int,
            phase: self.phase@,
            cmd: self.cmd as int,
            seq: self.seq as int,
            dep_count: self.dep_count as int,
            is_leader: self.is_leader,
            committed_count: self.committed_count as int,
            executed_count: self.executed_count as int,
            preaccept_senders: self.preaccept_senders@.map(|x: u64| x as int),
            accept_senders: self.accept_senders@.map(|x: u64| x as int),
            has_conflict: self.has_conflict,
            max_resp_seq: self.max_resp_seq as int,
        }
    }
}

#[derive(Clone, Copy)]
pub struct CConstants {
    pub num_replicas: u64,
    pub fast_quorum_size: u64,
    pub quorum_size: u64,
    pub my_id: u64,
}

impl CConstants {
    pub open spec fn valid(&self) -> bool {
        true
    }
}

impl View for CConstants {
    type V = LConstants;

    open spec fn view(&self) -> LConstants {
        LConstants {
            num_replicas: self.num_replicas as int,
            fast_quorum_size: self.fast_quorum_size as int,
            quorum_size: self.quorum_size as int,
            my_id: self.my_id as int,
        }
    }
}

#[derive(Clone, Copy)]
pub enum CInstancePhase {
    Empty,
    PreAccepted,
    Accepted,
    Committed,
    Executed,
}

impl CInstancePhase {
    pub open spec fn valid(&self) -> bool {
        match self {
            CInstancePhase::Empty => true,
            CInstancePhase::PreAccepted => true,
            CInstancePhase::Accepted => true,
            CInstancePhase::Committed => true,
            CInstancePhase::Executed => true,
        }
    }
}

impl View for CInstancePhase {
    type V = LInstancePhase;

    open spec fn view(&self) -> LInstancePhase {
        match self {
            CInstancePhase::Empty => LInstancePhase::Empty,
            CInstancePhase::PreAccepted => LInstancePhase::PreAccepted,
            CInstancePhase::Accepted => LInstancePhase::Accepted,
            CInstancePhase::Committed => LInstancePhase::Committed,
            CInstancePhase::Executed => LInstancePhase::Executed,
        }
    }
}

#[derive(Clone, Copy)]
pub enum CEPaxosMessage {
    PreAccept {
        ballot: u64,
        cmd: u64,
        seq: u64,
    },
    PreAcceptOk {
        sender: u64,
        seq: u64,
        conflict: bool,
    },
    Accept {
        ballot: u64,
        cmd: u64,
        seq: u64,
    },
    AcceptOk {
        sender: u64,
    },
    Commit {
        cmd: u64,
        seq: u64,
    },
    ClientReply {
        cmd: u64,
    },
}

impl CEPaxosMessage {
    pub open spec fn valid(&self) -> bool {
        match self {
            CEPaxosMessage::PreAccept { ballot, cmd, seq } => true,
            CEPaxosMessage::PreAcceptOk { sender, seq, conflict } => true,
            CEPaxosMessage::Accept { ballot, cmd, seq } => true,
            CEPaxosMessage::AcceptOk { sender } => true,
            CEPaxosMessage::Commit { cmd, seq } => true,
            CEPaxosMessage::ClientReply { cmd } => true,
        }
    }
}

impl View for CEPaxosMessage {
    type V = LEPaxosMessage;

    open spec fn view(&self) -> LEPaxosMessage {
        match self {
            CEPaxosMessage::PreAccept { ballot, cmd, seq } => LEPaxosMessage::PreAccept { ballot: *ballot as int, cmd: *cmd as int, seq: *seq as int },
            CEPaxosMessage::PreAcceptOk { sender, seq, conflict } => LEPaxosMessage::PreAcceptOk { sender: *sender as int, seq: *seq as int, conflict: *conflict },
            CEPaxosMessage::Accept { ballot, cmd, seq } => LEPaxosMessage::Accept { ballot: *ballot as int, cmd: *cmd as int, seq: *seq as int },
            CEPaxosMessage::AcceptOk { sender } => LEPaxosMessage::AcceptOk { sender: *sender as int },
            CEPaxosMessage::Commit { cmd, seq } => LEPaxosMessage::Commit { cmd: *cmd as int, seq: *seq as int },
            CEPaxosMessage::ClientReply { cmd } => LEPaxosMessage::ClientReply { cmd: *cmd as int },
        }
    }
}

} // verus!
