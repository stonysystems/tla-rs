// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

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
    pub msgs_preaccept: bool,
    pub msgs_preaccept_ballot: u64,
    pub msgs_preaccept_cmd: u64,
    pub msgs_preaccept_seq: u64,
    pub msgs_preaccept_ok: bool,
    pub msgs_preaccept_ok_sender: u64,
    pub msgs_preaccept_ok_seq: u64,
    pub msgs_preaccept_ok_conflict: bool,
    pub msgs_accept: bool,
    pub msgs_accept_ballot: u64,
    pub msgs_accept_cmd: u64,
    pub msgs_accept_seq: u64,
    pub msgs_accept_ok: bool,
    pub msgs_accept_ok_sender: u64,
    pub msgs_commit: bool,
    pub msgs_commit_cmd: u64,
    pub msgs_commit_seq: u64,
}

impl Clone for CState {
    #[verifier(external_body)]
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
    { unimplemented!() }
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
            msgs_preaccept: self.msgs_preaccept,
            msgs_preaccept_ballot: self.msgs_preaccept_ballot as int,
            msgs_preaccept_cmd: self.msgs_preaccept_cmd as int,
            msgs_preaccept_seq: self.msgs_preaccept_seq as int,
            msgs_preaccept_ok: self.msgs_preaccept_ok,
            msgs_preaccept_ok_sender: self.msgs_preaccept_ok_sender as int,
            msgs_preaccept_ok_seq: self.msgs_preaccept_ok_seq as int,
            msgs_preaccept_ok_conflict: self.msgs_preaccept_ok_conflict,
            msgs_accept: self.msgs_accept,
            msgs_accept_ballot: self.msgs_accept_ballot as int,
            msgs_accept_cmd: self.msgs_accept_cmd as int,
            msgs_accept_seq: self.msgs_accept_seq as int,
            msgs_accept_ok: self.msgs_accept_ok,
            msgs_accept_ok_sender: self.msgs_accept_ok_sender as int,
            msgs_commit: self.msgs_commit,
            msgs_commit_cmd: self.msgs_commit_cmd as int,
            msgs_commit_seq: self.msgs_commit_seq as int,
        }
    }
}

#[derive(Clone)]
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

#[derive(Clone)]
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

} // verus!
