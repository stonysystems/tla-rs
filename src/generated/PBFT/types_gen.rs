// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::protocol::PBFT::pbft::*;
use crate::protocol::PBFT::types::*;
use std::collections::HashSet;
use vstd::prelude::*;
use vstd::set::*;

verus! {

pub struct CState {
    pub view: u64,
    pub phase: CPhase,
    pub prepare_senders: HashSet<u64>,
    pub commit_senders: HashSet<u64>,
    pub seq_num: u64,
    pub is_primary: bool,
    pub request_digest: u64,
    pub checkpoint_seq: u64,
    pub checkpoint_digest: u64,
    pub low_watermark: u64,
    pub high_watermark: u64,
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
            view: self.view as int,
            phase: self.phase@,
            prepare_senders: self.prepare_senders@.map(|x: u64| x as int),
            commit_senders: self.commit_senders@.map(|x: u64| x as int),
            seq_num: self.seq_num as int,
            is_primary: self.is_primary,
            request_digest: self.request_digest as int,
            checkpoint_seq: self.checkpoint_seq as int,
            checkpoint_digest: self.checkpoint_digest as int,
            low_watermark: self.low_watermark as int,
            high_watermark: self.high_watermark as int,
        }
    }
}

#[derive(Clone)]
pub struct CConstants {
    pub f: u64,
    pub n: u64,
    pub node_id: u64,
    pub checkpoint_interval: u64,
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
            f: self.f as int,
            n: self.n as int,
            node_id: self.node_id as int,
            checkpoint_interval: self.checkpoint_interval as int,
        }
    }
}

#[derive(Clone)]
pub enum CPhase {
    PrePrepare,
    Prepare,
    Commit,
    Replied,
}

impl CPhase {
    pub open spec fn valid(&self) -> bool {
        match self {
            CPhase::PrePrepare => true,
            CPhase::Prepare => true,
            CPhase::Commit => true,
            CPhase::Replied => true,
        }
    }
}

impl View for CPhase {
    type V = LPhase;

    open spec fn view(&self) -> LPhase {
        match self {
            CPhase::PrePrepare => LPhase::PrePrepare,
            CPhase::Prepare => LPhase::Prepare,
            CPhase::Commit => LPhase::Commit,
            CPhase::Replied => LPhase::Replied,
        }
    }
}

#[derive(Clone)]
pub enum CPBFTMessage {
    PrePrepare {
        view: u64,
        seq: u64,
        digest: u64,
    },
}

impl CPBFTMessage {
    pub open spec fn valid(&self) -> bool {
        match self {
            CPBFTMessage::PrePrepare { view, seq, digest } => true,
        }
    }
}

impl View for CPBFTMessage {
    type V = LPBFTMessage;

    open spec fn view(&self) -> LPBFTMessage {
        match self {
            CPBFTMessage::PrePrepare { view, seq, digest } => LPBFTMessage::PrePrepare { view: *view as int, seq: *seq as int, digest: *digest as int },
        }
    }
}

} // verus!
