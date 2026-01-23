// Complete LAcceptorProcess1a example with both spec and exec
// Tests: complex conditional, struct update, enum variant access
// Simplified from RSL acceptor.rs LAcceptorProcess1a predicate (no packets)

use vstd::prelude::*;
use vstd::map::*;
use vstd::seq::*;

verus! {
    // === SPEC TYPES ===

    pub type OperationNumber = int;

    pub struct Ballot {
        pub seqno: int,
        pub proposer_id: int,
    }

    pub open spec fn BalLt(ba: Ballot, bb: Ballot) -> bool
    {
        ||| ba.seqno < bb.seqno
        ||| (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)
    }

    pub struct Vote {
        pub max_value_bal: Ballot,
        pub max_val: int,  // Simplified from RequestBatch
    }

    pub type Votes = Map<OperationNumber, Vote>;

    pub struct LConfiguration {
        pub replica_ids: Seq<int>,  // Simplified endpoint
    }

    pub struct LParameters {
        pub max_log_length: int,
    }

    pub struct LConstants {
        pub config: LConfiguration,
        pub params: LParameters,
    }

    pub struct LReplicaConstants {
        pub my_index: int,
        pub all: LConstants,
    }

    pub open spec fn LReplicaConstantsValid(c: LReplicaConstants) -> bool
    {
        0 <= c.my_index < c.all.config.replica_ids.len()
    }

    pub struct LAcceptor {
        pub constants: LReplicaConstants,
        pub max_bal: Ballot,
        pub votes: Votes,
        pub log_truncation_point: OperationNumber,
    }

    // Simplified message types
    pub enum RslMessage {
        RslMessage1a { bal_1a: Ballot },
        RslMessage1b { bal_1b: Ballot, log_truncation_point: OperationNumber, votes: Votes },
    }

    pub struct RslPacket {
        pub src: int,
        pub dst: int,
        pub msg: RslMessage,
    }

    // === SPEC PREDICATE (simplified from RSL acceptor.rs) ===
    // Focuses on state update, without packet generation for simplicity

    pub open spec fn LAcceptorProcess1a_StateUpdate(
        s: LAcceptor,
        s_: LAcceptor,
        inp: RslPacket,
    ) -> bool
        recommends
            inp.msg is RslMessage1a,
    {
        let bal = inp.msg->bal_1a;
        if s.constants.all.config.replica_ids.contains(inp.src)
            && BalLt(s.max_bal, bal)
            && LReplicaConstantsValid(s.constants)
        {
            s_ == LAcceptor {
                constants: s.constants,
                max_bal: bal,
                votes: s.votes,
                log_truncation_point: s.log_truncation_point,
            }
        } else {
            s_ == s
        }
    }

    // === EXEC TYPES ===

    pub struct CBallot {
        pub seqno: i64,
        pub proposer_id: i64,
    }

    impl CBallot {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn clone_for_view(&self) -> (result: CBallot)
            ensures result@ == self@
        {
            CBallot { seqno: self.seqno, proposer_id: self.proposer_id }
        }
    }

    impl View for CBallot {
        type V = Ballot;
        open spec fn view(&self) -> Ballot {
            Ballot {
                seqno: self.seqno as int,
                proposer_id: self.proposer_id as int,
            }
        }
    }

    // Exec version of BalLt
    pub fn ballot_lt(a: &CBallot, b: &CBallot) -> (result: bool)
        ensures result == BalLt(a@, b@)
    {
        a.seqno < b.seqno || (a.seqno == b.seqno && a.proposer_id < b.proposer_id)
    }

    pub struct CVotes {
        // Simplified - would be HashMap<i64, CVote>
        pub ghost_state: Ghost<Votes>,
    }

    impl CVotes {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn clone_for_view(&self) -> (result: CVotes)
            ensures result@ == self@
        {
            CVotes { ghost_state: Ghost(self.ghost_state@) }
        }
    }

    impl View for CVotes {
        type V = Votes;
        open spec fn view(&self) -> Votes {
            self.ghost_state@
        }
    }

    pub struct CConfiguration {
        pub num_replicas: i64,
        // In real impl, would have Vec of endpoint IDs
        pub ghost_replica_ids: Ghost<Seq<int>>,
    }

    impl CConfiguration {
        pub open spec fn well_formed(&self) -> bool {
            self.num_replicas > 0 && self.ghost_replica_ids@.len() == self.num_replicas
        }

        #[verifier::external_body]
        pub fn contains(&self, src: i64) -> (result: bool)
            ensures result == self@.replica_ids.contains(src as int)
        {
            unimplemented!()
        }

        pub fn clone_for_view(&self) -> (result: CConfiguration)
            requires self.well_formed()
            ensures result@ == self@, result.well_formed()
        {
            CConfiguration {
                num_replicas: self.num_replicas,
                ghost_replica_ids: Ghost(self.ghost_replica_ids@),
            }
        }
    }

    impl View for CConfiguration {
        type V = LConfiguration;
        open spec fn view(&self) -> LConfiguration {
            LConfiguration {
                replica_ids: self.ghost_replica_ids@,
            }
        }
    }

    pub struct CParameters {
        pub max_log_length: i64,
    }

    impl CParameters {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn clone_for_view(&self) -> (result: CParameters)
            ensures result@ == self@
        {
            CParameters { max_log_length: self.max_log_length }
        }
    }

    impl View for CParameters {
        type V = LParameters;
        open spec fn view(&self) -> LParameters {
            LParameters { max_log_length: self.max_log_length as int }
        }
    }

    pub struct CConstants {
        pub config: CConfiguration,
        pub params: CParameters,
    }

    impl CConstants {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.config.well_formed()
            &&& self.params.well_formed()
        }

        pub fn clone_for_view(&self) -> (result: CConstants)
            requires self.well_formed()
            ensures result@ == self@, result.well_formed()
        {
            CConstants {
                config: self.config.clone_for_view(),
                params: self.params.clone_for_view(),
            }
        }
    }

    impl View for CConstants {
        type V = LConstants;
        open spec fn view(&self) -> LConstants {
            LConstants {
                config: self.config@,
                params: self.params@,
            }
        }
    }

    pub struct CReplicaConstants {
        pub my_index: i64,
        pub all: CConstants,
    }

    impl CReplicaConstants {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.my_index >= 0
            &&& self.all.well_formed()
            &&& self.my_index < self.all.config.num_replicas
        }

        pub fn clone_for_view(&self) -> (result: CReplicaConstants)
            requires self.well_formed()
            ensures result@ == self@, result.well_formed()
        {
            CReplicaConstants {
                my_index: self.my_index,
                all: self.all.clone_for_view(),
            }
        }

        pub fn is_valid(&self) -> (result: bool)
            requires self.well_formed()
            ensures result == LReplicaConstantsValid(self@)
        {
            0 <= self.my_index && self.my_index < self.all.config.num_replicas
        }
    }

    impl View for CReplicaConstants {
        type V = LReplicaConstants;
        open spec fn view(&self) -> LReplicaConstants {
            LReplicaConstants {
                my_index: self.my_index as int,
                all: self.all@,
            }
        }
    }

    pub struct CAcceptor {
        pub constants: CReplicaConstants,
        pub max_bal: CBallot,
        pub votes: CVotes,
        pub log_truncation_point: i64,
    }

    impl CAcceptor {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.constants.well_formed()
            &&& self.max_bal.well_formed()
            &&& self.votes.well_formed()
        }

        pub fn clone_for_view(&self) -> (result: CAcceptor)
            requires self.well_formed()
            ensures result@ == self@, result.well_formed()
        {
            CAcceptor {
                constants: self.constants.clone_for_view(),
                max_bal: self.max_bal.clone_for_view(),
                votes: self.votes.clone_for_view(),
                log_truncation_point: self.log_truncation_point,
            }
        }
    }

    impl View for CAcceptor {
        type V = LAcceptor;
        open spec fn view(&self) -> LAcceptor {
            LAcceptor {
                constants: self.constants@,
                max_bal: self.max_bal@,
                votes: self.votes@,
                log_truncation_point: self.log_truncation_point as int,
            }
        }
    }

    // Exec message types
    pub enum CRslMessage {
        CRslMessage1a { bal_1a: CBallot },
        CRslMessage1b { bal_1b: CBallot, log_truncation_point: i64 },
    }

    impl CRslMessage {
        pub open spec fn well_formed(&self) -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        pub fn get_bal_1a(&self) -> (result: &CBallot)
            requires self is CRslMessage1a
            ensures result@ == self@->bal_1a
        {
            match self {
                CRslMessage::CRslMessage1a { bal_1a } => bal_1a,
                CRslMessage::CRslMessage1b { .. } => {
                    proof { assert(false); }
                    loop {}
                }
            }
        }
    }

    impl View for CRslMessage {
        type V = RslMessage;
        open spec fn view(&self) -> RslMessage {
            match self {
                CRslMessage::CRslMessage1a { bal_1a } => {
                    RslMessage::RslMessage1a { bal_1a: bal_1a@ }
                }
                CRslMessage::CRslMessage1b { bal_1b, log_truncation_point } => {
                    RslMessage::RslMessage1b {
                        bal_1b: bal_1b@,
                        log_truncation_point: *log_truncation_point as int,
                        votes: Map::empty(),  // Simplified
                    }
                }
            }
        }
    }

    pub struct CRslPacket {
        pub src: i64,
        pub dst: i64,
        pub msg: CRslMessage,
    }

    impl CRslPacket {
        pub open spec fn well_formed(&self) -> bool {
            self.msg.well_formed()
        }
    }

    impl View for CRslPacket {
        type V = RslPacket;
        open spec fn view(&self) -> RslPacket {
            RslPacket {
                src: self.src as int,
                dst: self.dst as int,
                msg: self.msg@,
            }
        }
    }

    // === EXEC FUNCTION (transpiler-generated pattern) ===

    pub fn c_acceptor_process1a_state_update(
        s: &CAcceptor,
        inp: &CRslPacket,
    ) -> (result: CAcceptor)
        requires
            s.well_formed(),
            inp.well_formed(),
            inp.msg is CRslMessage1a,
        ensures
            result.well_formed(),
            LAcceptorProcess1a_StateUpdate(s@, result@, inp@),
    {
        let bal = inp.msg.get_bal_1a();
        if s.constants.all.config.contains(inp.src)
            && ballot_lt(&s.max_bal, bal)
            && s.constants.is_valid()
        {
            CAcceptor {
                constants: s.constants.clone_for_view(),
                max_bal: bal.clone_for_view(),
                votes: s.votes.clone_for_view(),
                log_truncation_point: s.log_truncation_point,
            }
        } else {
            s.clone_for_view()
        }
    }
}

fn main() {}
