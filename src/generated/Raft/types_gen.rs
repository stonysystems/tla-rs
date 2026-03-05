// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::common::collections::hashsets::clone_hashset_u64;
use crate::implementation::Raft::helpers::*;
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
}

impl Clone for CState {
    #[verifier(external_body)]
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
        res.current_term == self.current_term,
        res.role == self.role,
        res.has_voted == self.has_voted,
        res.voted_for == self.voted_for,
        res.commit_index == self.commit_index,
    {
        CState {
            current_term: self.current_term,
            role: self.role,
            has_voted: self.has_voted,
            voted_for: self.voted_for,
            log: self.log.clone(),
            commit_index: self.commit_index,
            votes_granted: self.votes_granted.clone(),
            match_index: self.match_index.clone(),
            next_index: self.next_index.clone(),
        }
    }
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
        }
    }
}

pub struct CConstants {
    pub servers: HashSet<u64>,
    pub quorum_size: u64,
    pub my_id: u64,
}

impl Clone for CConstants {
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
        res.quorum_size == self.quorum_size,
        res.my_id == self.my_id,
    {
        CConstants {
            servers: clone_hashset_u64(&self.servers),
            quorum_size: self.quorum_size,
            my_id: self.my_id,
        }
    }
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

#[derive(Clone, Copy)]
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

#[derive(Clone)]
pub enum CRaftMessage {
    RequestVote {
        term: u64,
        candidate: u64,
        last_log_index: u64,
        last_log_term: u64,
    },
    VoteResponse {
        term: u64,
        granted: bool,
        voter: u64,
        voter_last_log_index: u64,
        voter_last_log_term: u64,
    },
    AppendEntries {
        term: u64,
        leader: u64,
        prev_index: u64,
        prev_term: u64,
        value: u64,
        has_entry: bool,
        leader_commit: u64,
    },
    AppendResponse {
        term: u64,
        success: bool,
        match_index: u64,
        follower: u64,
    },
}

impl CRaftMessage {
    pub open spec fn valid(&self) -> bool {
        match self {
            CRaftMessage::RequestVote { term, candidate, last_log_index, last_log_term } => true,
            CRaftMessage::VoteResponse { term, granted, voter, .. } => true,
            CRaftMessage::AppendEntries { term, leader, prev_index, prev_term, value, has_entry, leader_commit } => true,
            CRaftMessage::AppendResponse { term, success, match_index, follower } => true,
        }
    }
}

impl View for CRaftMessage {
    type V = LRaftMessage;

    open spec fn view(&self) -> LRaftMessage {
        match self {
            CRaftMessage::RequestVote { term, candidate, last_log_index, last_log_term } => LRaftMessage::RequestVote { term: *term as int, candidate: *candidate as int, last_log_index: *last_log_index as int, last_log_term: *last_log_term as int },
            CRaftMessage::VoteResponse { term, granted, voter, voter_last_log_index, voter_last_log_term } => LRaftMessage::VoteResponse { term: *term as int, granted: *granted, voter: *voter as int, voter_last_log_index: *voter_last_log_index as int, voter_last_log_term: *voter_last_log_term as int },
            CRaftMessage::AppendEntries { term, leader, prev_index, prev_term, value, has_entry, leader_commit } => LRaftMessage::AppendEntries { term: *term as int, leader: *leader as int, prev_index: *prev_index as int, prev_term: *prev_term as int, value: *value as int, has_entry: *has_entry, leader_commit: *leader_commit as int },
            CRaftMessage::AppendResponse { term, success, match_index, follower } => LRaftMessage::AppendResponse { term: *term as int, success: *success, match_index: *match_index as int, follower: *follower as int },
        }
    }
}

} // verus!
