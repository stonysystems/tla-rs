//! Raft safety with membership changes (joint consensus).
//!
//! The plan is in docs/raft-joint-consensus-proof-plan.md. This file starts
//! with the commit side: every commit certificate is held by a quorum of
//! the phase that governs its index in the committed history, and any two
//! commits of one index therefore use intersecting quorums.

use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::membership::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::invariants::*;
use crate::protocol::Raft::refinement_proof::message_invariants::*;
use crate::protocol::Raft::refinement_proof::reconfiguration::*;
use crate::protocol::Raft::refinement_proof::static_safety::*;
use vstd::prelude::*;

verus! {

    // =========================================================================
    // Phases along the committed history
    // =========================================================================

    /// The membership every server starts in.
    pub open spec fn initial_membership_phase(ds: RaftDistributedState) -> MembershipPhase {
        MembershipPhase::Stable { config: Set::<int>::range(0, ds.num_servers) }
    }

    /// The phase that governs committing history index `index`: the latest
    /// configuration strictly before it in the committed history.
    pub open spec fn history_phase_at(ds: RaftDistributedState, index: int) -> MembershipPhase {
        active_membership_phase_from_raft_log(
            ds.committed_history, index, initial_membership_phase(ds))
    }

    /// The certificate at `index` is held by a quorum of the phase that
    /// governs `index` in the committed history.
    #[verifier::opaque]
    pub open spec fn certificate_held_at(ds: RaftDistributedState, index: int) -> bool {
        let cert = ds.log_commit_certificates[index];
        &&& 0 <= index < ds.committed_history.len()
        &&& cert.log_index == index
        &&& cert.governing_phase == history_phase_at(ds, index)
        &&& is_quorum_for_phase(cert.quorum, cert.governing_phase)
        &&& forall |id: int| #![trigger cert.quorum.contains(id)]
            cert.quorum.contains(id) ==> {
                &&& 0 <= id < ds.num_servers
                &&& ds.server_states[id].log.len() > index
                &&& ds.server_states[id].log[index] == cert.entry
            }
    }

    /// Every certificate is held by a quorum of its governing phase.
    pub open spec fn CertificatesHeldByPhaseQuorum(ds: RaftDistributedState) -> bool {
        forall |index: int| #![trigger ds.log_commit_certificates.dom().contains(index)]
            ds.log_commit_certificates.dom().contains(index)
            ==> certificate_held_at(ds, index)
    }

    pub proof fn lemma_phase_quorum_certificates_indexed(ds: RaftDistributedState)
        requires
            CertificatesHeldByPhaseQuorum(ds),
        ensures
            CertificatesIndexed(ds),
    {
        assert forall |index: int| #![trigger ds.log_commit_certificates[index]]
            ds.log_commit_certificates.dom().contains(index)
            implies ds.log_commit_certificates[index].log_index == index by {
            assert(certificate_held_at(ds, index));
            reveal(certificate_held_at);
        }
    }

    // =========================================================================
    // A leader commit, in any membership phase
    // =========================================================================

    /// A local step that raises the commit index is a leader commit whose
    /// replicators form a quorum of the leader's active phase, agree with
    /// the leader below the new commit index, and the committed interval has
    /// no configuration entry before its last position.
    pub proof fn lemma_dynamic_local_commit_facts(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, sp: Seq<LRaftMessage>, rf: Option<int>,
    )
        requires
            CommitCore(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            0 <= server_id < ds.num_servers,
            RaftActionProduces(ds, server_id, ds.server_states[server_id],
                ds_.server_states[server_id], ds.server_constants[server_id], sp, rf),
            rf is None,
            ds_.server_states[server_id].commit_index > ds.server_states[server_id].commit_index,
        ensures ({
            let s = ds.server_states[server_id];
            let s_ = ds_.server_states[server_id];
            let c = ds.server_constants[server_id];
            let quorum = replicator_set(s, c, s_.commit_index);
            let phase = active_membership_phase_from_raft_log(
                s.log, s.commit_index, initial_membership_phase(ds));
            &&& s.role is Leader
            &&& s_.log == s.log
            &&& 0 <= s.commit_index < s_.commit_index <= s.log.len()
            &&& c.servers == Set::<int>::range(0, ds.num_servers)
            &&& is_quorum_for_phase(quorum, phase)
            &&& quorum.subset_of(Set::<int>::range(0, ds.num_servers))
            &&& forall |k: int| #![trigger s.log[k]]
                s.commit_index <= k < s_.commit_index - 1
                ==> !(s.log[k].payload is Configuration)
            &&& forall |id: int, k: int| #![trigger quorum.contains(id), s.log[k]]
                quorum.contains(id) && 0 <= k < s_.commit_index ==> {
                    &&& ds.server_states[id].log.len() > k
                    &&& ds.server_states[id].log[k] == s.log[k]
                }
        }),
    {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        let n = s_.commit_index;
        assert(exists |nci: int| LTryAdvanceCommitIndex(s, s_, c, nci, sp));
        let nci = choose |nci: int| LTryAdvanceCommitIndex(s, s_, c, nci, sp);
        assert(s.role is Leader && has_active_commit_quorum(s, c, nci) && nci == n);
        assert(c.servers =~= Set::<int>::range(0, ds.num_servers));
        assert(CommitIndexNonnegative(ds));
        let quorum = replicator_set(s, c, n);
        assert forall |id: int, k: int| #![trigger quorum.contains(id), s.log[k]]
            quorum.contains(id) && 0 <= k < n implies {
                &&& ds.server_states[id].log.len() > k
                &&& ds.server_states[id].log[k] == s.log[k]
            } by {
            if id != server_id {
                assert(s.match_index.contains_key(id as u64) && s.match_index[id as u64] as int >= n);
                assert(MatchIndexBounded(ds));
                assert(s.match_index[id as u64] as int <= ds.server_states[id].log.len());
                assert(s.log[k] == ds.server_states[id].log[k]);
            }
        }
    }

    /// One index of a leader's commit interval agrees with the history,
    /// given agreement below it. The replicators and the certificate are
    /// quorums of the same phase, so some server holds both entries.
    /// Every replicator agrees with `s` below `new_commit`.
    pub closed spec fn replicators_agree_below(
        ds: RaftDistributedState, s: LState, quorum: Set<int>, new_commit: int,
    ) -> bool {
        forall |id: int, k: int| #![trigger quorum.contains(id), s.log[k]]
            quorum.contains(id) && 0 <= k < new_commit ==> {
                &&& ds.server_states[id].log.len() > k
                &&& ds.server_states[id].log[k] == s.log[k]
            }
    }

    /// The interval being committed has no configuration before its end.
    pub closed spec fn commit_interval_configuration_free(s: LState, new_commit: int) -> bool {
        forall |k: int| #![trigger s.log[k]]
            s.commit_index <= k < new_commit - 1
            ==> !(s.log[k].payload is Configuration)
    }

    /// `log` agrees with the committed history below `upto`.
    pub closed spec fn history_agrees_below(
        ds: RaftDistributedState, log: Seq<LLogEntry>, upto: int,
    ) -> bool {
        forall |m: int| #![trigger ds.committed_history[m]]
            0 <= m < upto && m < ds.committed_history.len()
            ==> ds.committed_history[m] == log[m]
    }

    proof fn lemma_dynamic_leader_interval_step(
        ds: RaftDistributedState, s: LState, server_id: int,
        quorum: Set<int>, new_commit: int, j: int,
    )
        requires
            CommitHistoryValid(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CertificatesHeldByPhaseQuorum(ds),
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            0 <= s.commit_index < new_commit <= s.log.len(),
            is_quorum_for_phase(quorum, active_membership_phase_from_raft_log(
                s.log, s.commit_index, initial_membership_phase(ds))),
            commit_interval_configuration_free(s, new_commit),
            replicators_agree_below(ds, s, quorum, new_commit),
            0 <= j < new_commit,
            j < ds.committed_history.len(),
            history_agrees_below(ds, s.log, j),
        ensures
            ds.committed_history[j] == s.log[j],
    {
        let h = ds.committed_history;
        reveal(certificate_held_at);
        reveal(replicators_agree_below);
        reveal(commit_interval_configuration_free);
        reveal(history_agrees_below);
        assert(ds.log_commit_certificates.dom().contains(j));
        let cert = ds.log_commit_certificates[j];
        assert(cert.entry == h[j]);
        if j < s.commit_index {
            assert(ds.server_states[server_id].log[j] == s.log[j]);
            return;
        }
        let initial = initial_membership_phase(ds);
        assert forall |m: int| 0 <= m < j implies #[trigger] h[m] == s.log[m] by {}
        lemma_equal_committed_raft_prefixes_have_same_active_phase(h, s.log, j, initial);
        lemma_configuration_free_interval_preserves_active_phase(s.log, s.commit_index, j, initial);
        let phase = active_membership_phase_from_raft_log(s.log, s.commit_index, initial);
        assert(cert.governing_phase == phase);
        lemma_phase_quorums_intersect(quorum, cert.quorum, phase);
        let w = choose |w: int| #![trigger quorum.contains(w)] quorum.contains(w) && cert.quorum.contains(w);
        assert(ds.server_states[w].log[j] == s.log[j]);
        assert(ds.server_states[w].log[j] == cert.entry);
    }

    /// The leader's log agrees with the committed history below every index
    /// of the interval it commits.
    proof fn lemma_dynamic_leader_interval_agrees_upto(
        ds: RaftDistributedState, s: LState, server_id: int,
        quorum: Set<int>, new_commit: int, upto: int,
    )
        requires
            CommitHistoryValid(ds),
            CommittedEntriesHaveLogCertificates(ds),
            CertificatesHeldByPhaseQuorum(ds),
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            0 <= s.commit_index < new_commit <= s.log.len(),
            is_quorum_for_phase(quorum, active_membership_phase_from_raft_log(
                s.log, s.commit_index, initial_membership_phase(ds))),
            commit_interval_configuration_free(s, new_commit),
            replicators_agree_below(ds, s, quorum, new_commit),
            0 <= upto <= new_commit,
        ensures
            history_agrees_below(ds, s.log, upto),
        decreases upto,
    {
        reveal(history_agrees_below);
        if upto > 0 {
            lemma_dynamic_leader_interval_agrees_upto(ds, s, server_id, quorum, new_commit, upto - 1);
            if upto - 1 < ds.committed_history.len() {
                lemma_dynamic_leader_interval_step(ds, s, server_id, quorum, new_commit, upto - 1);
            }
        }
    }

    pub proof fn lemma_dynamic_leader_interval_agrees(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, sp: Seq<LRaftMessage>, rf: Option<int>, upto: int,
    )
        requires
            CommitCore(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            CertificatesHeldByPhaseQuorum(ds),
            0 <= server_id < ds.num_servers,
            RaftActionProduces(ds, server_id, ds.server_states[server_id],
                ds_.server_states[server_id], ds.server_constants[server_id], sp, rf),
            rf is None,
            ds_.server_states[server_id].commit_index > ds.server_states[server_id].commit_index,
            0 <= upto <= ds_.server_states[server_id].commit_index,
        ensures
            forall |j: int| #![trigger ds.committed_history[j]]
                0 <= j < upto && j < ds.committed_history.len()
                ==> ds.committed_history[j] == ds.server_states[server_id].log[j],
    {
        lemma_dynamic_local_commit_facts(ds, ds_, server_id, sp, rf);
        let s = ds.server_states[server_id];
        let n = ds_.server_states[server_id].commit_index;
        let quorum = replicator_set(s, ds.server_constants[server_id], n);
        reveal(replicators_agree_below);
        reveal(commit_interval_configuration_free);
        lemma_dynamic_leader_interval_agrees_upto(ds, s, server_id, quorum, n, upto);
        reveal(history_agrees_below);
    }

    /// A leader commit is covered: each committed index already has a
    /// certificate for the leader's entry, or receives one.
    pub proof fn lemma_dynamic_leader_commit_is_certified(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, sp: Seq<LRaftMessage>, rf: Option<int>,
    )
        requires
            CommitCore(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            CertificatesHeldByPhaseQuorum(ds),
            0 <= server_id < ds.num_servers,
            RaftActionProduces(ds, server_id, ds.server_states[server_id],
                ds_.server_states[server_id], ds.server_constants[server_id], sp, rf),
            rf is None,
            ds_.server_states[server_id].commit_index > ds.server_states[server_id].commit_index,
            ds_.log_commit_certificates == next_log_commit_certificates(ds, server_id,
                ds.server_states[server_id], ds_.server_states[server_id],
                ds.server_constants[server_id], rf),
        ensures
            ds_.server_states[server_id].log == ds.server_states[server_id].log,
            forall |k: int| #![trigger ds_.server_states[server_id].log[k]]
                ds.server_states[server_id].commit_index <= k
                && k < ds_.server_states[server_id].commit_index
                && k < ds_.server_states[server_id].log.len()
                ==> {
                    &&& ds_.log_commit_certificates.dom().contains(k)
                    &&& ds_.log_commit_certificates[k].entry == ds_.server_states[server_id].log[k]
                },
    {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        lemma_dynamic_local_commit_facts(ds, ds_, server_id, sp, rf);
        lemma_dynamic_leader_interval_agrees(ds, ds_, server_id, sp, rf, s_.commit_index);
        assert(CommitHistoryValid(ds));
        assert forall |k: int| #![trigger ds_.server_states[server_id].log[k]]
            s.commit_index <= k && k < s_.commit_index && k < s_.log.len()
            implies {
                &&& ds_.log_commit_certificates.dom().contains(k)
                &&& ds_.log_commit_certificates[k].entry == ds_.server_states[server_id].log[k]
            } by {
            if !ds.log_commit_certificates.dom().contains(k) {
                assert(ds_.log_commit_certificates[k]
                    == new_log_commit_certificate(server_id, s, s_, c, k));
            } else {
                reveal(certificate_held_at);
                assert(certificate_held_at(ds, k));
                assert(k < ds.committed_history.len());
                assert(ds.committed_history[k] == s.log[k]);
                assert(ds_.log_commit_certificates[k] == ds.log_commit_certificates[k]);
            }
        }
    }

    // =========================================================================
    // Certificate invariants are preserved by every step
    // =========================================================================

    /// The history only grows, and keeps its old prefix.
    pub proof fn lemma_history_extends(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            CommitHistoryValid(ds),
            CommitHistoryValid(ds_),
            ds_.committed_history.len() >= ds.committed_history.len(),
            forall |k: int| #![trigger ds.log_commit_certificates[k]]
                ds.log_commit_certificates.dom().contains(k)
                ==> ds_.log_commit_certificates.dom().contains(k)
                    && ds_.log_commit_certificates[k] == ds.log_commit_certificates[k],
        ensures
            forall |k: int| #![trigger ds_.committed_history[k]]
                0 <= k < ds.committed_history.len()
                ==> ds_.committed_history[k] == ds.committed_history[k],
    {
        assert forall |k: int| #![trigger ds_.committed_history[k]]
            0 <= k < ds.committed_history.len()
            implies ds_.committed_history[k] == ds.committed_history[k] by {
            assert(ds.log_commit_certificates.dom().contains(k));
            assert(ds.log_commit_certificates[k].entry == ds.committed_history[k]);
        }
    }

    /// The governing phase of an old history index does not change when the
    /// history grows.
    pub proof fn lemma_history_phase_stable(
        ds: RaftDistributedState, ds_: RaftDistributedState, index: int,
    )
        requires
            ds_.num_servers == ds.num_servers,
            0 <= index <= ds.committed_history.len() <= ds_.committed_history.len(),
            forall |k: int| #![trigger ds_.committed_history[k]]
                0 <= k < ds.committed_history.len()
                ==> ds_.committed_history[k] == ds.committed_history[k],
        ensures
            history_phase_at(ds_, index) == history_phase_at(ds, index),
    {
        lemma_equal_committed_raft_prefixes_have_same_active_phase(
            ds_.committed_history, ds.committed_history, index, initial_membership_phase(ds));
    }

    /// An existing certificate stays held: logs only grow and the history
    /// keeps its prefix.
    proof fn lemma_old_certificate_still_held(
        ds: RaftDistributedState, ds_: RaftDistributedState, index: int,
    )
        requires
            certificate_held_at(ds, index),
            ds_.num_servers == ds.num_servers,
            LogAppendOnly(ds, ds_),
            ds_.log_commit_certificates[index] == ds.log_commit_certificates[index],
            ds_.committed_history.len() >= ds.committed_history.len(),
            forall |k: int| #![trigger ds_.committed_history[k]]
                0 <= k < ds.committed_history.len()
                ==> ds_.committed_history[k] == ds.committed_history[k],
        ensures
            certificate_held_at(ds_, index),
    {
        reveal(certificate_held_at);
        let cert = ds.log_commit_certificates[index];
        lemma_history_phase_stable(ds, ds_, index);
        assert forall |id: int| #![trigger cert.quorum.contains(id)]
            cert.quorum.contains(id) implies {
                &&& 0 <= id < ds_.num_servers
                &&& ds_.server_states[id].log.len() > index
                &&& ds_.server_states[id].log[index] == cert.entry
            } by {
            assert(ds.server_states[id].log[index] == ds_.server_states[id].log[index]);
        }
    }

    /// A certificate created by a leader commit is held by the leader's
    /// replicators, a quorum of the phase governing its index.
    proof fn lemma_new_certificate_held(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants, index: int,
    )
        requires
            CommitHistoryValid(ds_),
            CommittedEntriesHaveLogCertificates(ds_),
            ds_.num_servers == ds.num_servers,
            LogAppendOnly(ds, ds_),
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            s_.log == s.log,
            c.servers == Set::<int>::range(0, ds.num_servers),
            0 <= s.commit_index <= index < s_.commit_index <= s.log.len(),
            ds_.log_commit_certificates[index] == new_log_commit_certificate(server_id, s, s_, c, index),
            is_quorum_for_phase(replicator_set(s, c, s_.commit_index),
                active_membership_phase_from_raft_log(s.log, s.commit_index, initial_membership_phase(ds))),
            commit_interval_configuration_free(s, s_.commit_index),
            replicators_agree_below(ds, s, replicator_set(s, c, s_.commit_index), s_.commit_index),
        ensures
            certificate_held_at(ds_, index),
    {
        reveal(certificate_held_at);
        reveal(commit_interval_configuration_free);
        reveal(replicators_agree_below);
        let n = s_.commit_index;
        let initial = initial_membership_phase(ds);
        let cert = ds_.log_commit_certificates[index];
        assert(n <= ds_.committed_history.len());
        assert forall |m: int| 0 <= m < index
            implies #[trigger] ds_.committed_history[m] == s.log[m] by {
            assert(ds_.log_commit_certificates[m].entry == ds_.committed_history[m]);
            assert(ds_.log_commit_certificates[m].entry == ds_.server_states[server_id].log[m]);
        }
        lemma_equal_committed_raft_prefixes_have_same_active_phase(
            ds_.committed_history, s.log, index, initial);
        lemma_configuration_free_interval_preserves_active_phase(
            s.log, s.commit_index, index, initial);
        let quorum = replicator_set(s, c, n);
        assert forall |id: int| #![trigger quorum.contains(id)]
            quorum.contains(id) implies {
                &&& 0 <= id < ds_.num_servers
                &&& ds_.server_states[id].log.len() > index
                &&& ds_.server_states[id].log[index] == cert.entry
            } by {
            assert(ds.server_states[id].log[index] == s.log[index]);
            assert(ds.server_states[id].log[index] == ds_.server_states[id].log[index]);
        }
    }

    proof fn lemma_dynamic_certificates_held_reboot(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            CertificatesHeldByPhaseQuorum(ds),
            RaftDistributedNext(ds, ds_),
            !RaftDistributedNormalNext(ds, ds_),
        ensures
            CertificatesHeldByPhaseQuorum(ds_),
    {
        let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
        assert(LogAppendOnly(ds, ds_)) by {
            assert forall |i: int| #![trigger ds_.server_states[i]] 0 <= i < ds_.num_servers
                implies ds_.server_states[i].log == ds.server_states[i].log by {};
        }
        assert forall |index: int| #![trigger ds_.log_commit_certificates.dom().contains(index)]
            ds_.log_commit_certificates.dom().contains(index)
            implies certificate_held_at(ds_, index) by {
            lemma_old_certificate_still_held(ds, ds_, index);
        }
    }

    proof fn lemma_dynamic_certificates_held_normal(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftSafetyInvariant(ds_),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            CertificatesHeldByPhaseQuorum(ds),
            RaftDistributedNormalNext(ds, ds_),
        ensures
            CertificatesHeldByPhaseQuorum(ds_),
    {
        lemma_log_append_only(ds, ds_);
        let (server_id, sp, rf) = lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        assert(ds_.log_commit_certificates
            == next_log_commit_certificates(ds, server_id, s, s_, c, rf));
        lemma_next_log_commit_certificates_extend(ds, server_id, s, s_, c, rf);
        assert(ds_.committed_history == RecordCommittedPrefix(ds.committed_history, s_));
        lemma_history_extends(ds, ds_);
        let fresh = rf is None && s_.commit_index > s.commit_index;
        if fresh {
            lemma_dynamic_local_commit_facts(ds, ds_, server_id, sp, rf);
            reveal(commit_interval_configuration_free);
            reveal(replicators_agree_below);
            assert(commit_interval_configuration_free(s, s_.commit_index));
            assert(replicators_agree_below(ds, s, replicator_set(s, c, s_.commit_index), s_.commit_index));
        }
        assert forall |index: int| #![trigger ds_.log_commit_certificates.dom().contains(index)]
            ds_.log_commit_certificates.dom().contains(index)
            implies certificate_held_at(ds_, index) by {
            if ds.log_commit_certificates.dom().contains(index) {
                lemma_old_certificate_still_held(ds, ds_, index);
            } else {
                assert(fresh);
                lemma_new_certificate_held(ds, ds_, server_id, s, s_, c, index);
            }
        }
    }

    pub proof fn lemma_dynamic_certificates_held_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            RaftSafetyInvariant(ds_),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            CertificatesHeldByPhaseQuorum(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            CertificatesHeldByPhaseQuorum(ds_),
    {
        if RaftDistributedNormalNext(ds, ds_) {
            lemma_dynamic_certificates_held_normal(ds, ds_);
        } else {
            lemma_dynamic_certificates_held_reboot(ds, ds_);
        }
    }

    /// Certificate coverage is preserved by every step.
    pub proof fn lemma_dynamic_log_certificates_cover_normal(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            CommitCore(ds),
            LogMatching(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            CertificatesHeldByPhaseQuorum(ds),
            AppendEntriesCommitCertified(ds),
            RaftDistributedNormalNext(ds, ds_),
        ensures
            CommittedEntriesHaveLogCertificates(ds_),
    {
        lemma_phase_quorum_certificates_indexed(ds);
        lemma_certificates_indexed_next(ds, ds_);
        let (server_id, sp, rf) = lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        assert(ds_.log_commit_certificates
            == next_log_commit_certificates(ds, server_id, s, s_, c, rf));
        lemma_next_log_commit_certificates_extend(ds, server_id, s, s_, c, rf);
        assert(s.commit_index <= s.log.len());
        lemma_lnext_log_preserved_or_extended(s, s_, c);
        if s_.commit_index > s.commit_index {
            if rf is None {
                lemma_dynamic_leader_commit_is_certified(ds, ds_, server_id, sp, rf);
            } else {
                assert(ds_.log_commit_certificates == ds.log_commit_certificates);
                lemma_follower_commit_is_certified(ds, ds_, server_id, sp, rf);
            }
        }
        lemma_log_certificates_cover_after_step(ds, ds_, server_id);
    }

    pub proof fn lemma_dynamic_log_certificates_cover_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            CommitCore(ds),
            LogMatching(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            CertificatesHeldByPhaseQuorum(ds),
            AppendEntriesCommitCertified(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            CommittedEntriesHaveLogCertificates(ds_),
    {
        if !RaftDistributedNormalNext(ds, ds_) {
            lemma_static_log_certificates_cover_reboot(ds, ds_);
        } else {
            lemma_dynamic_log_certificates_cover_normal(ds, ds_);
        }
    }

    // =========================================================================
    // Configuration certificates mirror the log certificates
    // =========================================================================

    /// A configuration certificate exists exactly for the certified log
    /// entries that are Configuration entries, and records the same entry.
    pub open spec fn ConfigurationCertificatesMatchLogCertificates(ds: RaftDistributedState) -> bool {
        &&& forall |k: int| #![trigger ds.configuration_commit_certificates[k]]
            ds.configuration_commit_certificates.dom().contains(k) ==> {
                &&& ds.log_commit_certificates.dom().contains(k)
                &&& ds.configuration_commit_certificates[k].log_index == k
                &&& ds.configuration_commit_certificates[k].entry
                    == ds.log_commit_certificates[k].entry
            }
        &&& forall |k: int| #![trigger ds.log_commit_certificates[k]]
            ds.log_commit_certificates.dom().contains(k)
            && ds.log_commit_certificates[k].entry.payload is Configuration
            ==> ds.configuration_commit_certificates.dom().contains(k)
    }

    pub proof fn lemma_configuration_coverage_from_log_coverage(ds: RaftDistributedState)
        requires
            CommittedEntriesHaveLogCertificates(ds),
            ConfigurationCertificatesMatchLogCertificates(ds),
        ensures
            CommittedConfigurationsHaveCertificates(ds),
    {
        assert forall |server_id: int, index: int|
            #![trigger ds.server_states[server_id].log[index]]
            0 <= server_id < ds.num_servers
            && 0 <= index < ds.server_states[server_id].commit_index
            && index < ds.server_states[server_id].log.len()
            && ds.server_states[server_id].log[index].payload is Configuration
            implies {
                &&& ds.configuration_commit_certificates.dom().contains(index)
                &&& ds.configuration_commit_certificates[index].log_index == index
                &&& ds.configuration_commit_certificates[index].entry
                    == ds.server_states[server_id].log[index]
            } by {
            assert(ds.log_commit_certificates.dom().contains(index));
            assert(ds.log_commit_certificates[index].entry == ds.server_states[server_id].log[index]);
        }
    }

    /// The fresh-commit case: only the last committed position may be a
    /// Configuration entry, and it gets both certificates in the same step.
    proof fn lemma_configuration_certificates_match_fresh(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants,
    )
        requires
            ConfigurationCertificatesMatchLogCertificates(ds),
            s_.log == s.log,
            0 <= s.commit_index < s_.commit_index <= s.log.len(),
            commit_interval_configuration_free(s, s_.commit_index),
            ds_.log_commit_certificates
                == next_log_commit_certificates(ds, server_id, s, s_, c, None),
            ds_.configuration_commit_certificates
                == next_configuration_commit_certificates(ds, server_id, s, s_, c, None),
            forall |k: int| #![trigger ds.log_commit_certificates[k]]
                ds.log_commit_certificates.dom().contains(k)
                ==> ds_.log_commit_certificates.dom().contains(k)
                    && ds_.log_commit_certificates[k] == ds.log_commit_certificates[k],
            forall |k: int| #![trigger s_.log[k]]
                s.commit_index <= k && k < s_.commit_index && k < s_.log.len()
                ==> {
                    &&& ds_.log_commit_certificates.dom().contains(k)
                    &&& ds_.log_commit_certificates[k].entry == s_.log[k]
                },
        ensures
            ConfigurationCertificatesMatchLogCertificates(ds_),
    {
        reveal(commit_interval_configuration_free);
        let n = s_.commit_index;
        assert forall |k: int| #![trigger ds_.configuration_commit_certificates[k]]
            ds_.configuration_commit_certificates.dom().contains(k) implies {
                &&& ds_.log_commit_certificates.dom().contains(k)
                &&& ds_.configuration_commit_certificates[k].log_index == k
                &&& ds_.configuration_commit_certificates[k].entry
                    == ds_.log_commit_certificates[k].entry
            } by {
            if ds.configuration_commit_certificates.dom().contains(k) {
                assert(ds.log_commit_certificates.dom().contains(k));
            } else {
                assert(k == n - 1);
                assert(ds_.log_commit_certificates[k].entry == s_.log[k]);
            }
        }
        assert forall |k: int| #![trigger ds_.log_commit_certificates[k]]
            ds_.log_commit_certificates.dom().contains(k)
            && ds_.log_commit_certificates[k].entry.payload is Configuration
            implies ds_.configuration_commit_certificates.dom().contains(k) by {
            if !ds.log_commit_certificates.dom().contains(k) {
                assert(s.commit_index <= k < n && k < s_.log.len());
                assert(ds_.log_commit_certificates[k] == new_log_commit_certificate(server_id, s, s_, c, k));
                if k < n - 1 {
                    assert(!(s.log[k].payload is Configuration));
                }
                if ds.configuration_commit_certificates.dom().contains(k) {
                    assert(ds.configuration_commit_certificates[k].log_index == k);
                    assert(ds.log_commit_certificates.dom().contains(k));
                }
            }
        }
    }

    pub proof fn lemma_configuration_certificates_match_inductive(
        ds: RaftDistributedState, ds_: RaftDistributedState,
    )
        requires
            RaftSafetyInvariant(ds),
            MatchIndexImpliesLogAgreement(ds),
            MatchIndexBounded(ds),
            CertificatesHeldByPhaseQuorum(ds),
            ConfigurationCertificatesMatchLogCertificates(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            ConfigurationCertificatesMatchLogCertificates(ds_),
    {
        if !RaftDistributedNormalNext(ds, ds_) {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            return;
        }
        let (server_id, sp, rf) = lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        assert(ds_.log_commit_certificates
            == next_log_commit_certificates(ds, server_id, s, s_, c, rf));
        assert(ds_.configuration_commit_certificates
            == next_configuration_commit_certificates(ds, server_id, s, s_, c, rf));
        if !(rf is None && s_.commit_index > s.commit_index) {
            assert(ds_.log_commit_certificates == ds.log_commit_certificates);
            assert(ds_.configuration_commit_certificates == ds.configuration_commit_certificates);
            return;
        }
        lemma_next_log_commit_certificates_extend(ds, server_id, s, s_, c, rf);
        lemma_dynamic_local_commit_facts(ds, ds_, server_id, sp, rf);
        lemma_dynamic_leader_commit_is_certified(ds, ds_, server_id, sp, rf);
        reveal(commit_interval_configuration_free);
        assert(commit_interval_configuration_free(s, s_.commit_index));
        lemma_configuration_certificates_match_fresh(ds, ds_, server_id, s, s_, c);
    }

} // verus!
