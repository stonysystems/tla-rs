// Test for vote manipulation pattern from LAcceptorProcess2a
// Tests: LAddVoteAndRemoveOldOnes - map manipulation with vote addition and filtering
//
// Pattern demonstrated:
// - Map manipulation with biconditional domain constraint
// - Conditional value assignment inside forall
// - Nested conditional logic for state updates

use vstd::prelude::*;
use vstd::map::*;
use vstd::seq::*;

verus! {
    // === SPEC TYPES ===

    pub type OperationNumber = int;

    // Simplified vote
    pub struct Vote {
        pub ballot: int,
        pub value: int,
    }

    pub type Votes = Map<OperationNumber, Vote>;

    // Simplified acceptor state (focused on votes)
    pub struct LAcceptor {
        pub votes: Votes,
        pub log_truncation_point: OperationNumber,
        pub max_bal: int,
    }

    // === MAIN PREDICATE ===
    // Add vote and remove old ones - complex map manipulation

    pub open spec fn LAddVoteAndRemoveOldOnes(
        votes: Votes,
        votes_: Votes,
        new_opn: OperationNumber,
        new_vote: Vote,
        log_truncation_point: OperationNumber
    ) -> bool
    {
        // Domain condition: key in new map iff key >= threshold AND (was in old map OR is the new key)
        &&& (forall |opn: OperationNumber| #![auto] votes_.dom().contains(opn) <==>
            opn >= log_truncation_point && (votes.dom().contains(opn) || opn == new_opn))
        // Value condition: value is either the new vote (if key matches) or the old value
        &&& (forall |opn: OperationNumber| #![auto] votes_.dom().contains(opn) ==>
            votes_[opn] == (if opn == new_opn { new_vote } else { votes[opn] }))
    }

    // Simplified Process2a - focuses on vote update pattern
    pub open spec fn LAcceptorProcess2aVotes(
        s: LAcceptor,
        s_: LAcceptor,
        inp_opn: OperationNumber,
        new_vote: Vote,
        new_log_truncation_point: OperationNumber,
        should_update_votes: bool  // Abstracts: s.log_truncation_point <= inp_opn
    ) -> bool
    {
        &&& s_.max_bal == new_vote.ballot
        &&& s_.log_truncation_point == new_log_truncation_point
        &&& (if should_update_votes {
                LAddVoteAndRemoveOldOnes(s.votes, s_.votes, inp_opn, new_vote, new_log_truncation_point)
            } else {
                s_.votes == s.votes
            })
    }

    // === EXEC TYPES ===

    // Concrete vote
    pub struct CVote {
        pub ballot: i64,
        pub value: i64,
    }

    impl CVote {
        pub open spec fn well_formed(&self) -> bool { true }
    }

    impl View for CVote {
        type V = Vote;
        open spec fn view(&self) -> Vote {
            Vote {
                ballot: self.ballot as int,
                value: self.value as int,
            }
        }
    }

    // Ghost wrapper for votes
    pub struct CVotes {
        pub ghost_state: Ghost<Votes>,
    }

    impl CVotes {
        pub open spec fn well_formed(&self) -> bool { true }

        // Add vote and remove old ones
        #[verifier::external_body]
        pub fn add_vote_and_remove_old(
            &self,
            new_opn: i64,
            new_vote: &CVote,
            log_truncation_point: i64
        ) -> (result: CVotes)
            ensures LAddVoteAndRemoveOldOnes(self@, result@, new_opn as int, new_vote@, log_truncation_point as int)
        {
            unimplemented!()
        }

        pub fn clone_ghost(&self) -> (result: CVotes)
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

    // Concrete acceptor
    pub struct CAcceptor {
        pub votes: CVotes,
        pub log_truncation_point: i64,
        pub max_bal: i64,
    }

    impl CAcceptor {
        pub open spec fn well_formed(&self) -> bool {
            self.votes.well_formed()
        }
    }

    impl View for CAcceptor {
        type V = LAcceptor;
        open spec fn view(&self) -> LAcceptor {
            LAcceptor {
                votes: self.votes@,
                log_truncation_point: self.log_truncation_point as int,
                max_bal: self.max_bal as int,
            }
        }
    }

    // === MAIN EXEC FUNCTION ===
    // Implements vote update pattern from LAcceptorProcess2a

    pub fn c_acceptor_process_2a_votes(
        s: &CAcceptor,
        inp_opn: i64,
        new_vote: &CVote,
        new_log_truncation_point: i64,
        should_update_votes: bool,
    ) -> (result: CAcceptor)
        requires
            s.well_formed(),
            new_vote.well_formed(),
        ensures
            result.well_formed(),
            LAcceptorProcess2aVotes(s@, result@, inp_opn as int, new_vote@, new_log_truncation_point as int, should_update_votes),
    {
        // Update votes based on condition
        let new_votes = if should_update_votes {
            s.votes.add_vote_and_remove_old(inp_opn, new_vote, new_log_truncation_point)
        } else {
            s.votes.clone_ghost()
        };

        // Construct new acceptor state
        CAcceptor {
            votes: new_votes,
            log_truncation_point: new_log_truncation_point,
            max_bal: new_vote.ballot,
        }
    }
}

fn main() {}
