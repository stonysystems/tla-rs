use crate::protocol::Raft::types::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::invariants::*;
use vstd::prelude::*;

verus! {
    pub open spec fn IsPrefix(s1: Seq<int>, s2: Seq<int>) -> bool {
        &&& s1.len() <= s2.len()
        &&& (forall |k: int| #![trigger s2[k]]
             0 <= k < s1.len() ==> s1[k] == s2[k])
    }

    /// Historical commitment cannot be erased by resetting volatile knowledge.
    /// Normal steps record actual committed prefixes. Their certificates agree
    /// with old history because an existing certificate is immutable.
    pub proof fn lemma_committed_history_monotone(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            CommitHistoryValid(ds),
            CommitHistoryValid(ds_),
            CommitIndexBounded(ds_),
            RaftDistributedNext(ds, ds_),
        ensures
            ds_.committed_history.len() >= ds.committed_history.len(),
            forall |k: int| #![trigger ds_.committed_history[k]]
                0 <= k < ds.committed_history.len() ==>
                    ds_.committed_history[k] == ds.committed_history[k],
    {
        if RaftDistributedNormalNext(ds, ds_) {
            let sid = choose |sid: int| {
                &&& 0 <= sid < ds.num_servers
                &&& (forall |j: int| #![trigger ds_.server_states[j]]
                    0 <= j < ds.num_servers && j != sid ==>
                        ds_.server_states[j] == ds.server_states[j])
                &&& RaftServerStepWithNetwork(ds, ds_, sid)
            };
            let (sp, rf) = choose |sp: Seq<LRaftMessage>, rf: Option<int>|
                RaftServerStepWitness(ds, ds_, sid, sp, rf);
            assert(ds_.committed_history.len() >= ds.committed_history.len());
            assert forall |k: int| #![trigger ds_.committed_history[k]]
                0 <= k < ds.committed_history.len() implies
                    ds_.committed_history[k] == ds.committed_history[k]
            by {
                assert(CommitHistoryValid(ds));
                assert(CommitHistoryValid(ds_));
                assert(ds.log_commit_certificates[k].entry == ds.committed_history[k]);
                assert(ds.log_commit_certificates.dom().contains(k));
                assert(ds_.log_commit_certificates[k].entry
                    == ds.log_commit_certificates[k].entry);
            };
        } else {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert(ds_.committed_history == ds.committed_history);
        }
    }

    pub proof fn lemma_committed_log_monotone(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            CommitHistoryValid(ds),
            CommitHistoryValid(ds_),
            CommitIndexBounded(ds_),
            RaftDistributedNext(ds, ds_),
        ensures IsPrefix(GetCommittedLog(ds), GetCommittedLog(ds_))
    {
        lemma_committed_history_monotone(ds, ds_);
    }

    /// A reboot is an abstract stutter, even if the node knew the greatest
    /// commit index or was the last node to remember that index locally.
    pub proof fn lemma_reboot_is_abstract_stutter(
        ds: RaftDistributedState, ds_: RaftDistributedState, sid: int,
    )
        requires RaftDistributedReboot(ds, ds_, sid)
        ensures GetCommittedLog(ds_) == GetCommittedLog(ds)
    {
    }

    pub proof fn lemma_abstract_step_valid(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        rs: RaftSystemState, rs_: RaftSystemState,
    )
        requires
            CommitHistoryValid(ds),
            CommitHistoryValid(ds_),
            CommitIndexBounded(ds_),
            RaftDistributedNext(ds, ds_),
            RaftSystemRefinement(ds, rs),
            RaftSystemRefinement(ds_, rs_),
        ensures RaftSystemNext(rs, rs_)
    {
        lemma_committed_log_monotone(ds, ds_);
        if !RaftDistributedNormalNext(ds, ds_) {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
        }
        if rs.committed_log.len() == rs_.committed_log.len() {
            assert(rs_.committed_log =~= rs.committed_log);
            assert(rs_.server_ids =~= rs.server_ids);
        }
    }
}
