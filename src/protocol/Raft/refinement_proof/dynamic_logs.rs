//! Log structure under membership changes: where configuration entries can
//! sit relative to the committed history.
//!
//! See docs/raft-joint-consensus-proof-plan.md, section 2.

use crate::protocol::Raft::types::*;
use crate::protocol::Raft::raft::*;
use crate::protocol::Raft::membership::*;
use crate::protocol::Raft::refinement_proof::state_machine::*;
use crate::protocol::Raft::refinement_proof::invariants::*;
use crate::protocol::Raft::refinement_proof::message_invariants::*;
use crate::protocol::Raft::refinement_proof::reconfiguration::*;
use crate::protocol::Raft::refinement_proof::static_safety::*;
use crate::protocol::Raft::refinement_proof::dynamic_safety::*;
use vstd::prelude::*;

verus! {

    // =========================================================================
    // Where an appended entry comes from
    // =========================================================================

    /// One step appends at most one entry. A leader appends its own proposal
    /// (a configuration only when its log has no uncommitted configuration,
    /// and only as a legal successor of its active phase). Anyone else copies
    /// the entry from a log that shares the whole prefix before it.
    pub open spec fn appended_entry_source(
        ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int,
    ) -> bool {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        let at = s.log.len() as int;
        ||| {
            &&& s.role is Leader
            &&& s_.log[at].term == s.current_term
            &&& (s_.log[at].payload is Configuration ==> {
                &&& uncommitted_suffix_has_no_configuration(s.log, s.commit_index)
                &&& is_legal_phase_progression(
                    active_membership_phase_from_raft_log(
                        s.log, s.commit_index, initial_membership_phase(ds)),
                    membership_phase_view(s_.log[at].payload->phase))
            })
        }
        ||| exists |source: int| #![trigger ds.server_states[source]] {
            &&& 0 <= source < ds.num_servers
            &&& ds.server_states[source].log.len() > at
            &&& ds.server_states[source].log[at] == s_.log[at]
            &&& forall |m: int| #![trigger s.log[m]]
                0 <= m < at ==> ds.server_states[source].log[m] == s.log[m]
        }
    }

    pub proof fn lemma_appended_entry_source(
        ds: RaftDistributedState, ds_: RaftDistributedState, server_id: int,
    )
        requires
            RaftSafetyInvariant(ds),
            LogMatching(ds),
            RaftServerStepWithNetwork(ds, ds_, server_id),
            0 <= server_id < ds.num_servers,
            WellFormedRaftDistributed(ds_),
            ds_.num_servers == ds.num_servers,
            ds_.server_constants == ds.server_constants,
            ds_.server_states[server_id].log.len() == ds.server_states[server_id].log.len() + 1,
            forall |m: int| #![trigger ds_.server_states[server_id].log[m]]
                0 <= m < ds.server_states[server_id].log.len()
                ==> ds_.server_states[server_id].log[m] == ds.server_states[server_id].log[m],
        ensures
            appended_entry_source(ds, ds_, server_id),
    {
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        let at = s.log.len() as int;
        assert(c.servers =~= Set::<int>::range(0, ds.num_servers));
        if s_.role is Follower {
            lemma_follower_find_ae_source(ds, ds_, server_id, s, s_, c, at);
        }
    }

    /// The follower case: the entry and its prefix come from the
    /// AppendEntries sender's log.
    proof fn lemma_follower_find_ae_source(
        ds: RaftDistributedState, ds_: RaftDistributedState,
        server_id: int, s: LState, s_: LState, c: LConstants, at: int,
    )
        requires
            AppendEntriesIntegrity(ds),
            WellFormedRaftDistributed(ds),
            LogMatching(ds),
            0 <= server_id < ds.num_servers,
            s == ds.server_states[server_id],
            s_ == ds_.server_states[server_id],
            c == ds.server_constants[server_id],
            RaftServerStepWithNetwork(ds, ds_, server_id),
            s_.log.len() == s.log.len() + 1,
            s_.role is Follower,
            at == s.log.len() as int,
        ensures
            exists |source: int| #![trigger ds.server_states[source]] {
                &&& 0 <= source < ds.num_servers
                &&& ds.server_states[source].log.len() > at
                &&& ds.server_states[source].log[at] == s_.log[at]
                &&& forall |m: int| #![trigger s.log[m]]
                    0 <= m < at ==> ds.server_states[source].log[m] == s.log[m]
            },
    {
        lemma_follower_append_ae_in_network(ds, ds_, server_id, s, s_, c, at);
        let l = choose |l: int| #![trigger ds.server_states[l]] {
            &&& 0 <= l < ds.num_servers
            &&& ds.server_states[l].log.len() > at
            &&& ds.server_states[l].log[at].term == s_.log[at].term
            &&& ds.server_states[l].log[at].value == s_.log[at].value
            &&& ds.server_states[l].log[at].payload == s_.log[at].payload
            &&& (at > 0 ==> s.log[at - 1].term == ds.server_states[l].log[at - 1].term)
        };
        assert forall |m: int| #![trigger s.log[m]]
            0 <= m < at implies ds.server_states[l].log[m] == s.log[m] by {
            assert(ds.server_states[server_id].log[at - 1].term
                == ds.server_states[l].log[at - 1].term);
            assert(ds.server_states[server_id].log[m] == ds.server_states[l].log[m]);
        }
    }

    // =========================================================================
    // Some log holds the committed history
    // =========================================================================

    pub open spec fn log_holds_history(ds: RaftDistributedState, h: int) -> bool {
        &&& 0 <= h < ds.num_servers
        &&& ds.server_states[h].log.len() >= ds.committed_history.len()
        &&& forall |k: int| #![trigger ds.committed_history[k]]
            0 <= k < ds.committed_history.len()
            ==> ds.server_states[h].log[k] == ds.committed_history[k]
    }

    pub open spec fn HistoryHeld(ds: RaftDistributedState) -> bool {
        exists |h: int| #![trigger log_holds_history(ds, h)] log_holds_history(ds, h)
    }

    pub proof fn lemma_history_held_init(ds: RaftDistributedState)
        requires RaftDistributedInit(ds),
        ensures HistoryHeld(ds),
    {
        assert(log_holds_history(ds, 0));
    }

    pub proof fn lemma_history_held_inductive(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            HistoryHeld(ds),
            RaftSafetyInvariant(ds),
            RaftSafetyInvariant(ds_),
            RaftDistributedNext(ds, ds_),
        ensures
            HistoryHeld(ds_),
    {
        let h = choose |h: int| #![trigger log_holds_history(ds, h)] log_holds_history(ds, h);
        if !RaftDistributedNormalNext(ds, ds_) {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert(ds_.server_states[h].log == ds.server_states[h].log);
            assert(log_holds_history(ds_, h));
            return;
        }
        lemma_log_append_only(ds, ds_);
        let (server_id, sp, rf) = lemma_extract_step_with_network(ds, ds_);
        let s_ = ds_.server_states[server_id];
        assert(ds_.committed_history == RecordCommittedPrefix(ds.committed_history, s_));
        if s_.commit_index > ds.committed_history.len() {
            assert(CommitIndexBounded(ds_));
            assert(s_.commit_index <= s_.log.len());
            assert(log_holds_history(ds_, server_id));
        } else {
            assert forall |k: int| #![trigger ds_.committed_history[k]]
                0 <= k < ds_.committed_history.len()
                implies ds_.server_states[h].log[k] == ds_.committed_history[k] by {
                assert(ds_.server_states[h].log[k] == ds.server_states[h].log[k]);
            }
            assert(log_holds_history(ds_, h));
        }
    }

    /// A log that agrees with the history at one index agrees with it below.
    pub proof fn lemma_history_prefix_closed(ds: RaftDistributedState, i: int, k: int)
        requires
            LogMatching(ds),
            HistoryHeld(ds),
            0 <= i < ds.num_servers,
            0 <= k < ds.committed_history.len(),
            k < ds.server_states[i].log.len(),
            ds.server_states[i].log[k] == ds.committed_history[k],
        ensures
            forall |m: int| #![trigger ds.server_states[i].log[m]]
                0 <= m <= k ==> ds.server_states[i].log[m] == ds.committed_history[m],
    {
        let h = choose |h: int| #![trigger log_holds_history(ds, h)] log_holds_history(ds, h);
        assert(ds.server_states[h].log[k] == ds.committed_history[k]);
        assert forall |m: int| #![trigger ds.server_states[i].log[m]]
            0 <= m <= k implies ds.server_states[i].log[m] == ds.committed_history[m] by {
            assert(ds.server_states[i].log[k].term == ds.server_states[h].log[k].term);
            assert(ds.server_states[i].log[m] == ds.server_states[h].log[m]);
        }
    }

    // =========================================================================
    // I4: a configuration followed by another one is committed
    // =========================================================================

    pub open spec fn ConfigurationFollowedIsCommitted(ds: RaftDistributedState) -> bool {
        forall |i: int, k1: int, k2: int|
            #![trigger ds.server_states[i].log[k1], ds.server_states[i].log[k2]]
            0 <= i < ds.num_servers
            && 0 <= k1 < k2 < ds.server_states[i].log.len()
            && ds.server_states[i].log[k1].payload is Configuration
            && ds.server_states[i].log[k2].payload is Configuration
            ==> k1 < ds.committed_history.len()
                && ds.server_states[i].log[k1] == ds.committed_history[k1]
    }

    pub proof fn lemma_configuration_followed_init(ds: RaftDistributedState)
        requires RaftDistributedInit(ds),
        ensures ConfigurationFollowedIsCommitted(ds),
    {
        assert forall |i: int| #![trigger ds.server_states[i]] 0 <= i < ds.num_servers
            implies ds.server_states[i].log.len() == 0 by {
            assert(LInit(ds.server_states[i], ds.server_constants[i]));
        }
    }

    pub proof fn lemma_configuration_followed_inductive(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            ConfigurationFollowedIsCommitted(ds),
            RaftSafetyInvariant(ds),
            RaftSafetyInvariant(ds_),
            LogMatching(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            ConfigurationFollowedIsCommitted(ds_),
    {
        assert(CommitHistoryValid(ds) && CommitHistoryValid(ds_));
        if !RaftDistributedNormalNext(ds, ds_) {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert forall |i: int| #![trigger ds_.server_states[i]] 0 <= i < ds_.num_servers
                implies ds_.server_states[i].log == ds.server_states[i].log by {};
            return;
        }
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
        lemma_lnext_log_preserved_or_extended(s, s_, c);
        let grew = s_.log.len() == s.log.len() + 1;
        if grew {
            lemma_appended_entry_source(ds, ds_, server_id);
        }
        assert forall |i: int, k1: int, k2: int|
            #![trigger ds_.server_states[i].log[k1], ds_.server_states[i].log[k2]]
            0 <= i < ds_.num_servers
            && 0 <= k1 < k2 < ds_.server_states[i].log.len()
            && ds_.server_states[i].log[k1].payload is Configuration
            && ds_.server_states[i].log[k2].payload is Configuration
            implies k1 < ds_.committed_history.len()
                && ds_.server_states[i].log[k1] == ds_.committed_history[k1] by {
            let li = ds.server_states[i].log;
            if k2 < li.len() {
                assert(ds_.server_states[i].log[k1] == li[k1]);
                assert(ds_.server_states[i].log[k2] == li[k2]);
                assert(k1 < ds.committed_history.len() && li[k1] == ds.committed_history[k1]);
            } else {
                assert(i == server_id && grew && k2 == s.log.len());
                let at = s.log.len() as int;
                assert(s_.log[k1] == s.log[k1]);
                if s.role is Leader && s_.log[at].term == s.current_term
                    && (s_.log[at].payload is Configuration ==> uncommitted_suffix_has_no_configuration(s.log, s.commit_index)) {
                    assert(k1 < s.commit_index);
                    assert(CommittedEntriesHaveLogCertificates(ds));
                    assert(ds.log_commit_certificates[k1].entry == s.log[k1]);
                    assert(ds.log_commit_certificates[k1].entry == ds.committed_history[k1]);
                } else {
                    let source = choose |source: int| #![trigger ds.server_states[source]] {
                        &&& 0 <= source < ds.num_servers
                        &&& ds.server_states[source].log.len() > at
                        &&& ds.server_states[source].log[at] == s_.log[at]
                        &&& forall |m: int| #![trigger s.log[m]]
                            0 <= m < at ==> ds.server_states[source].log[m] == s.log[m]
                    };
                    let ls = ds.server_states[source].log;
                    assert(ls[k1] == s.log[k1]);
                    assert(ls[at] == s_.log[at]);
                    assert(k1 < ds.committed_history.len() && ls[k1] == ds.committed_history[k1]);
                }
            }
        }
    }

    // =========================================================================
    // Every configuration entry is a legal progression
    // =========================================================================

    pub open spec fn configuration_entry_legal(log: Seq<LLogEntry>, k: int, initial: MembershipPhase) -> bool {
        log[k].payload is Configuration ==> is_legal_phase_progression(
            active_membership_phase_from_raft_log(log, k, initial),
            membership_phase_view(log[k].payload->phase))
    }

    pub open spec fn ConfigurationEntriesLegal(ds: RaftDistributedState) -> bool {
        forall |i: int, k: int| #![trigger ds.server_states[i].log[k]]
            0 <= i < ds.num_servers && 0 <= k < ds.server_states[i].log.len()
            ==> configuration_entry_legal(ds.server_states[i].log, k, initial_membership_phase(ds))
    }

    pub proof fn lemma_configuration_entries_legal_init(ds: RaftDistributedState)
        requires RaftDistributedInit(ds),
        ensures ConfigurationEntriesLegal(ds),
    {
        assert forall |i: int| #![trigger ds.server_states[i]] 0 <= i < ds.num_servers
            implies ds.server_states[i].log.len() == 0 by {
            assert(LInit(ds.server_states[i], ds.server_constants[i]));
        }
    }

    pub proof fn lemma_configuration_entries_legal_inductive(ds: RaftDistributedState, ds_: RaftDistributedState)
        requires
            ConfigurationEntriesLegal(ds),
            RaftSafetyInvariant(ds),
            LogMatching(ds),
            RaftDistributedNext(ds, ds_),
        ensures
            ConfigurationEntriesLegal(ds_),
    {
        let initial = initial_membership_phase(ds);
        if !RaftDistributedNormalNext(ds, ds_) {
            let sid = choose |sid: int| RaftDistributedReboot(ds, ds_, sid);
            assert forall |i: int| #![trigger ds_.server_states[i]] 0 <= i < ds_.num_servers
                implies ds_.server_states[i].log == ds.server_states[i].log by {};
            return;
        }
        lemma_log_append_only(ds, ds_);
        let (server_id, sp, rf) = lemma_extract_step_with_network(ds, ds_);
        let s = ds.server_states[server_id];
        let s_ = ds_.server_states[server_id];
        let c = ds.server_constants[server_id];
        lemma_lnext_log_preserved_or_extended(s, s_, c);
        let grew = s_.log.len() == s.log.len() + 1;
        if grew {
            lemma_appended_entry_source(ds, ds_, server_id);
        }
        assert forall |i: int, k: int| #![trigger ds_.server_states[i].log[k]]
            0 <= i < ds_.num_servers && 0 <= k < ds_.server_states[i].log.len()
            implies configuration_entry_legal(ds_.server_states[i].log, k, initial_membership_phase(ds_)) by {
            let li = ds.server_states[i].log;
            let li_ = ds_.server_states[i].log;
            assert forall |m: int| #![trigger li_[m]] 0 <= m < k && m < li.len() implies li_[m] == li[m] by {
                assert(li_[m] == li[m]);
            }
            if k < li.len() {
                assert(li_[k] == li[k]);
                assert(configuration_entry_legal(li, k, initial));
                lemma_equal_committed_raft_prefixes_have_same_active_phase(li_, li, k, initial);
            } else {
                assert(i == server_id && grew && k == s.log.len());
                let at = k;
                lemma_equal_committed_raft_prefixes_have_same_active_phase(s_.log, s.log, at, initial);
                if s.role is Leader && s_.log[at].term == s.current_term
                    && (s_.log[at].payload is Configuration ==> {
                        &&& uncommitted_suffix_has_no_configuration(s.log, s.commit_index)
                        &&& is_legal_phase_progression(
                            active_membership_phase_from_raft_log(s.log, s.commit_index, initial),
                            membership_phase_view(s_.log[at].payload->phase))
                    }) {
                    if s_.log[at].payload is Configuration {
                        lemma_configuration_free_interval_preserves_active_phase(
                            s.log, s.commit_index, at, initial);
                    }
                } else {
                    let source = choose |source: int| #![trigger ds.server_states[source]] {
                        &&& 0 <= source < ds.num_servers
                        &&& ds.server_states[source].log.len() > at
                        &&& ds.server_states[source].log[at] == s_.log[at]
                        &&& forall |m: int| #![trigger s.log[m]]
                            0 <= m < at ==> ds.server_states[source].log[m] == s.log[m]
                    };
                    let ls = ds.server_states[source].log;
                    assert(configuration_entry_legal(ls, at, initial));
                    assert forall |m: int| #![trigger ls[m]] 0 <= m < at implies s.log[m] == ls[m] by {
                        assert(ls[m] == s.log[m]);
                    }
                    lemma_equal_committed_raft_prefixes_have_same_active_phase(s.log, ls, at, initial);
                }
            }
        }
    }

} // verus!
