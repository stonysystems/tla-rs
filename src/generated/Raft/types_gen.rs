// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::common::collections::hashsets::clone_hashset;
use crate::protocol::Raft::types::*;
use std::collections::HashMap;
use std::collections::HashSet;
use vstd::prelude::*;
use vstd::set::*;

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
}

impl Clone for CState {
    #[verifier(external_body)]
    fn clone(&self) -> Self {
        CState {
            current_term: self.current_term,
            role: self.role.clone(),
            has_voted: self.has_voted,
            voted_for: self.voted_for,
            log: self.log.clone(),
            commit_index: self.commit_index,
            votes_granted: self.votes_granted.clone(),
            match_index: self.match_index.clone(),
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
            log: self.log@.map(|i: int, e: CLogEntry| e@),
            commit_index: self.commit_index as int,
            votes_granted: self.votes_granted@.map(|x: u64| x as int),
            match_index: self.match_index@,
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
    fn clone(&self) -> Self {
        CConstants {
            servers: self.servers.clone(),
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

} // verus!
