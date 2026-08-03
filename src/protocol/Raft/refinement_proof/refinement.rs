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
            server_ids: Set::new(|j: int| 0 <= j < ds.num_servers),
        }
    }

    // =========================================================================
    // Helper: MaxCommitIndex is 0 when all commit indices are 0
    // =========================================================================

    proof fn lemma_max_commit_index_zero_when_all_zero(ds: RaftDistributedState)
        requires
            ds.server_states.len() == ds.num_servers,
            ds.server_constants.len() == ds.num_servers,
            ds.num_servers >= 0,
            forall |i: int| 0 <= i < ds.num_servers ==>
                ds.server_states[i].commit_index == 0,
        ensures
            MaxCommitIndex(ds) == 0
        decreases ds.num_servers
    {
        if ds.num_servers > 0 {
            let sub_ds = RaftDistributedState {
                server_states: ds.server_states.subrange(0, ds.num_servers - 1),
                server_constants: ds.server_constants.subrange(0, ds.num_servers - 1),
                network: ds.network,
                num_servers: ds.num_servers - 1,
                vote_log_len: ds.vote_log_len,
                configuration_commit_certificates:
                    ds.configuration_commit_certificates,
                log_commit_certificates: ds.log_commit_certificates,
            };

            assert forall |i: int| 0 <= i < sub_ds.num_servers
            implies sub_ds.server_states[i].commit_index == 0
            by {
                // sub_ds.server_states[i] == ds.server_states[i] for i < n-1
                // and ds.server_states[i].commit_index == 0 by hypothesis
            }

            lemma_max_commit_index_zero_when_all_zero(sub_ds);
            // MaxCommitIndex(sub_ds) == 0
            // ds.server_states[n-1].commit_index == 0
            // MaxCommitIndex(ds) = max(0, 0) = 0
        }
    }

    // =========================================================================
    // Init: committed log is empty at initialization
    // =========================================================================

    proof fn lemma_init_committed_log_empty(ds: RaftDistributedState)
        requires RaftDistributedInit(ds)
        ensures GetCommittedLog(ds) == Seq::<int>::empty()
    {
        // All servers at init satisfy LInit, which sets commit_index == 0
        assert forall |i: int| 0 <= i < ds.num_servers
        implies ds.server_states[i].commit_index == 0
        by {
            // RaftDistributedInit ensures LInit for each server
            // LInit specifies s.commit_index == 0
        }

        lemma_max_commit_index_zero_when_all_zero(ds);
        // MaxCommitIndex(ds) == 0
        // GetCommittedLog checks max_commit <= 0, returns Seq::empty()
    }

    // =========================================================================
    // Top-level refinement theorem
    // =========================================================================
    //
    // Given a valid Raft distributed behavior, there exists an abstract
    // sequential state machine behavior that refines it.
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
