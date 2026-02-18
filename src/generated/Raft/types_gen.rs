// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::types::*;
use std::collections::HashMap;
use std::collections::HashSet;
use vstd::prelude::*;
use vstd::set::*;
use vstd::set_lib::*;

verus! {

#[derive(Clone)]
pub struct CLogEntry {
    pub term: u64,
    pub value: u64,
}

impl CLogEntry {
    pub open spec fn valid(&self) -> bool {
        true
    }
}

impl View for CLogEntry {
    type V = LLogEntry;

    open spec fn view(&self) -> LLogEntry {
        LLogEntry {
            term: self.term as int,
            value: self.value as int,
        }
    }
}

pub struct CState {
    pub current_term: u64,
    pub role: CServerRole,
    pub has_voted: bool,
    pub voted_for: u64,
    pub log: Vec<CLogEntry>,
    pub commit_index: u64,
    pub votes_granted: HashSet<u64>,
    pub match_index: HashMap<u64, u64>,
    pub next_index: HashMap<u64, u64>,
    pub msgs_request_vote: bool,
    pub msgs_request_vote_term: u64,
    pub msgs_request_vote_candidate: u64,
    pub msgs_request_vote_last_log_index: u64,
    pub msgs_request_vote_last_log_term: u64,
    pub msgs_vote_response: bool,
    pub msgs_vote_response_term: u64,
    pub msgs_vote_response_granted: bool,
    pub msgs_vote_response_voter: u64,
    pub msgs_append_entries: bool,
    pub msgs_append_entries_term: u64,
    pub msgs_append_entries_leader: u64,
    pub msgs_append_entries_prev_index: u64,
    pub msgs_append_entries_prev_term: u64,
    pub msgs_append_entries_value: u64,
    pub msgs_append_entries_has_entry: bool,
    pub msgs_append_entries_leader_commit: u64,
    pub msgs_append_response: bool,
    pub msgs_append_response_term: u64,
    pub msgs_append_response_success: bool,
    pub msgs_append_response_match_index: u64,
    pub msgs_append_response_follower: u64,
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
        &&& self.role.valid()
    }
}

impl View for CState {
    type V = LState;

    open spec fn view(&self) -> LState {
        LState {
            current_term: self.current_term as int,
            role: self.role@,
            has_voted: self.has_voted,
            voted_for: self.voted_for as int,
            log: self.log@.map(|i: int, x: CLogEntry| x@),
            commit_index: self.commit_index as int,
            votes_granted: self.votes_granted@.map(|x: u64| x as int),
            match_index: self.match_index@,
            next_index: self.next_index@,
            msgs_request_vote: self.msgs_request_vote,
            msgs_request_vote_term: self.msgs_request_vote_term as int,
            msgs_request_vote_candidate: self.msgs_request_vote_candidate as int,
            msgs_request_vote_last_log_index: self.msgs_request_vote_last_log_index as int,
            msgs_request_vote_last_log_term: self.msgs_request_vote_last_log_term as int,
            msgs_vote_response: self.msgs_vote_response,
            msgs_vote_response_term: self.msgs_vote_response_term as int,
            msgs_vote_response_granted: self.msgs_vote_response_granted,
            msgs_vote_response_voter: self.msgs_vote_response_voter as int,
            msgs_append_entries: self.msgs_append_entries,
            msgs_append_entries_term: self.msgs_append_entries_term as int,
            msgs_append_entries_leader: self.msgs_append_entries_leader as int,
            msgs_append_entries_prev_index: self.msgs_append_entries_prev_index as int,
            msgs_append_entries_prev_term: self.msgs_append_entries_prev_term as int,
            msgs_append_entries_value: self.msgs_append_entries_value as int,
            msgs_append_entries_has_entry: self.msgs_append_entries_has_entry,
            msgs_append_entries_leader_commit: self.msgs_append_entries_leader_commit as int,
            msgs_append_response: self.msgs_append_response,
            msgs_append_response_term: self.msgs_append_response_term as int,
            msgs_append_response_success: self.msgs_append_response_success,
            msgs_append_response_match_index: self.msgs_append_response_match_index as int,
            msgs_append_response_follower: self.msgs_append_response_follower as int,
        }
    }
}

pub struct CConstants {
    pub servers: HashSet<u64>,
    pub quorum_size: u64,
    pub my_id: u64,
}

impl Clone for CConstants {
    #[verifier(external_body)]
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
    { unimplemented!() }
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
            servers: self.servers@.map(|x: u64| x as int),
            quorum_size: self.quorum_size as int,
            my_id: self.my_id as int,
        }
    }
}

#[derive(Clone)]
pub enum CServerRole {
    Follower,
    Candidate,
    Leader,
}

impl CServerRole {
    pub open spec fn valid(&self) -> bool {
        match self {
            CServerRole::Follower => true,
            CServerRole::Candidate => true,
            CServerRole::Leader => true,
        }
    }
}

impl View for CServerRole {
    type V = LServerRole;

    open spec fn view(&self) -> LServerRole {
        match self {
            CServerRole::Follower => LServerRole::Follower,
            CServerRole::Candidate => LServerRole::Candidate,
            CServerRole::Leader => LServerRole::Leader,
        }
    }
}


// Manual exec helper functions for Raft protocol
// These implement exec versions of spec helper functions u64_inc/u64_dec

pub exec fn Cu64_inc(x: &u64) -> (result: u64)
requires
    *x < u64::MAX,
ensures
    result == u64_inc(*x),
{
    *x + 1
}

pub exec fn Cu64_dec(x: &u64) -> (result: u64)
requires
    *x > 0,
ensures
    result == u64_dec(*x),
{
    *x - 1
}
} // verus!
