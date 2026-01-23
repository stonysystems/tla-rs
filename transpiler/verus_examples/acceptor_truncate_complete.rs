// Test for LAcceptorTruncateLog predicate
// Tests: conditional branching, struct construction, map filtering
// Pattern: Cross-component predicate used by LReplicaNextProcess1b

use vstd::prelude::*;
use vstd::map::*;

verus! {
    // === SPEC TYPES ===

    pub type OperationNumber = int;

    // Simplified vote type
    pub struct Vote {
        pub max_value_bal: int,
        pub max_val: int,
    }

    pub type Votes = Map<OperationNumber, Vote>;

    // Simplified acceptor state
    pub struct LAcceptor {
        pub constants: int,  // Simplified
        pub max_bal: int,
        pub votes: Votes,
        pub last_checkpointed_operation: int,  // Simplified
        pub log_truncation_point: OperationNumber,
    }

    // === SPEC PREDICATES ===

    // Helper predicate for filtering votes
    pub open spec fn RemoveVotesBeforeLogTruncationPoint(
        votes: Votes,
        votes_: Votes,
        log_truncation_point: OperationNumber
    ) -> bool
    {
        &&& (forall |opn: OperationNumber| votes_.contains_key(opn) ==> votes.contains_key(opn) && votes_[opn] == votes[opn])
        &&& (forall |opn: OperationNumber| opn < log_truncation_point ==> !votes_.contains_key(opn))
        &&& (forall |opn: OperationNumber| opn >= log_truncation_point && votes.contains_key(opn) ==> votes_.contains_key(opn))
    }

    // Main predicate under test
    pub open spec fn LAcceptorTruncateLog(
        s: LAcceptor,
        s_: LAcceptor,
        opn: OperationNumber
    ) -> bool
    {
        if opn <= s.log_truncation_point {
            s_ == s
        } else {
            &&& s_ == LAcceptor {
                constants: s.constants,
                max_bal: s.max_bal,
                votes: s_.votes,
                last_checkpointed_operation: s.last_checkpointed_operation,
                log_truncation_point: opn,
            }
            &&& RemoveVotesBeforeLogTruncationPoint(s.votes, s_.votes, opn)
        }
    }

    // === EXEC TYPES ===

    pub struct CVotes {
        pub ghost_state: Ghost<Votes>,
    }

    impl CVotes {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn empty() -> (result: CVotes)
            ensures result@ == Map::<OperationNumber, Vote>::empty()
        {
            CVotes { ghost_state: Ghost(Map::empty()) }
        }

        // Filter votes to retain only keys >= threshold
        #[verifier::external_body]
        pub fn filter_by_threshold(&self, threshold: i64) -> (result: CVotes)
            ensures RemoveVotesBeforeLogTruncationPoint(self@, result@, threshold as int)
        {
            // Real impl would iterate HashMap and filter
            unimplemented!()
        }

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

    // Concrete acceptor type
    pub struct CAcceptor {
        pub constants: i64,
        pub max_bal: i64,
        pub votes: CVotes,
        pub last_checkpointed_operation: i64,
        pub log_truncation_point: i64,
    }

    impl CAcceptor {
        pub open spec fn well_formed(&self) -> bool {
            self.votes.well_formed()
        }

        pub fn clone_for_view(&self) -> (result: CAcceptor)
            ensures result@ == self@
        {
            CAcceptor {
                constants: self.constants,
                max_bal: self.max_bal,
                votes: self.votes.clone_for_view(),
                last_checkpointed_operation: self.last_checkpointed_operation,
                log_truncation_point: self.log_truncation_point,
            }
        }
    }

    impl View for CAcceptor {
        type V = LAcceptor;
        open spec fn view(&self) -> LAcceptor {
            LAcceptor {
                constants: self.constants as int,
                max_bal: self.max_bal as int,
                votes: self.votes@,
                last_checkpointed_operation: self.last_checkpointed_operation as int,
                log_truncation_point: self.log_truncation_point as int,
            }
        }
    }

    // === EXEC FUNCTION ===
    // Implements LAcceptorTruncateLog

    pub fn c_acceptor_truncate_log(s: &CAcceptor, opn: i64) -> (result: CAcceptor)
        requires
            s.well_formed(),
        ensures
            result.well_formed(),
            LAcceptorTruncateLog(s@, result@, opn as int),
    {
        if opn <= s.log_truncation_point {
            // No change case
            s.clone_for_view()
        } else {
            // Update log_truncation_point and filter votes
            let filtered_votes = s.votes.filter_by_threshold(opn);
            CAcceptor {
                constants: s.constants,
                max_bal: s.max_bal,
                votes: filtered_votes,
                last_checkpointed_operation: s.last_checkpointed_operation,
                log_truncation_point: opn,
            }
        }
    }
}

fn main() {}
