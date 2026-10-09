use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::invariants::*;
use crate::protocol::Raft::refinement_proof::induction::*;
use crate::protocol::Raft::refinement_proof::committed::*;
use vstd::prelude::*;
use vstd::{map::*, seq::*, set::*};

verus! {

    // =========================================================================
    // Refinement map: distributed state → abstract sequential state
    // =========================================================================

    /// Map a distributed Raft state to its abstract sequential state.
    /// The committed log is extracted via GetCommittedLog, and
    /// server_ids is the set {0, ..., num_servers - 1}.
    pub open spec fn AbstractifyRaftState(ds: RaftDistributedState) -> RaftSystemState {
        RaftSystemState {
            committed_log: GetCommittedLog(ds),
            server_ids: Set::<int>::range(0, ds.num_servers),
        }
    }

    proof fn lemma_init_committed_log_empty(ds: RaftDistributedState)
        requires RaftDistributedInit(ds)
        ensures GetCommittedLog(ds) == Seq::<int>::empty()
    {
        assert(GetCommittedLog(ds) =~= Seq::<int>::empty());
    }

    // =========================================================================
    // Top-level refinement theorem
    // =========================================================================
    //
    // Given a valid Raft distributed behavior, including membership changes,
    // there exists an abstract sequential state machine behavior that
    // refines it.
    //
    // The abstract behavior is constructed by applying AbstractifyRaftState
    // pointwise to the distributed behavior.
    //
    // Key dependencies:
    // - lemma_init_establishes_invariant: invariant holds at step 0
    // - lemma_next_preserves_invariant: invariant is inductive
    // - lemma_invariant_holds_throughout_behavior: invariant at every step
    // - lemma_abstract_step_valid: each distributed step maps to a valid abstract step

    pub proof fn lemma_refinement_correct(b: RaftBehavior)
        requires IsValidRaftBehavior(b)
        ensures
            exists |h: Seq<RaftSystemState>|
                RaftSystemBehaviorRefinementCorrect(b, h)
    {
        // Construct the abstract behavior pointwise
        let h = Seq::new(b.len(), |i: int| AbstractifyRaftState(b[i]));

        // -- Property 1: same length --
        assert(h.len() == b.len());

        // -- Property 2: non-empty --
        assert(h.len() > 0);

        // -- Property 3: abstract initial state --
        lemma_init_committed_log_empty(b[0]);
        assert(h[0] == AbstractifyRaftState(b[0]));

        // -- Property 4: pointwise refinement relation --
        assert forall |i: int| #![trigger b[i]]
            0 <= i < b.len()
        implies
            RaftSystemRefinement(b[i], h[i])
        by {
            assert(h[i] == AbstractifyRaftState(b[i]));
            // AbstractifyRaftState(b[i]).committed_log == GetCommittedLog(b[i])
            // AbstractifyRaftState(b[i]).server_ids == Set::new(|j| ...)
            // These match RaftSystemRefinement's definition
        }

        // -- Property 5: each abstract step is a valid RaftSystemNext --
        assert forall |i: int| #![trigger h[i]]
            0 <= i < h.len() - 1
        implies
            RaftSystemNext(h[i], h[i + 1])
        by {
            assert(h[i] == AbstractifyRaftState(b[i]));
            assert(h[i + 1] == AbstractifyRaftState(b[i + 1]));

            // Establish invariants at steps i and i+1
            lemma_invariant_holds_throughout_behavior(b, i);
            lemma_invariant_holds_throughout_behavior(b, i + 1);

            // b[i] → b[i+1] is a valid distributed step (from IsValidRaftBehavior)
            // Invariants hold at both steps
            // Therefore the abstract step is valid
            lemma_abstract_step_valid(b[i], b[i + 1], h[i], h[i + 1]);
        }

        // Assemble: the constructed h satisfies all properties
        assert(RaftSystemBehaviorRefinementCorrect(b, h));
    }
}
