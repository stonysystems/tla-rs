use crate::protocol::Raft::types::{
    LConstants,
    LLogEntry,
    LLogValue,
    LMembershipConfig,
    LMembershipPhase,
    LState,
};
use vstd::prelude::*;
pub use crate::protocol::Raft::types::{
    membership_config_view,
    membership_phase_view,
    stable_phase_from_config,
    MembershipPhase,
};


verus! {

    /// Proof-only evidence for one committed Configuration log entry.
    ///
    /// `log_index` is the zero-based physical Raft-log index of the
    /// Configuration entry. `governing_phase` is the active membership just
    /// before that entry became committed, and `quorum` is the set of replicas
    /// whose logs justified committing it.
    ///
    /// This is ghost proof information: it does not change the executable
    /// Raft messages, storage format, or host behavior.
    pub struct ConfigurationCommitCertificate {
        pub log_index: int,
        pub entry: LLogEntry,
        pub committer: int,
        pub governing_phase: MembershipPhase,
        pub quorum: Set<int>,
    }

    /// Proof-only evidence for any committed physical Raft-log entry.
    /// Unlike ConfigurationCommitCertificate, this also covers Data entries.
    pub struct LogCommitCertificate {
        pub log_index: int,
        pub entry: LLogEntry,
        pub committer: int,
        pub governing_phase: MembershipPhase,
        pub quorum: Set<int>,
    }

    /// A quorum is a majority of a particular finite configuration.
    pub open spec fn is_majority_of(
        quorum: Set<int>,
        config: Set<int>,
    ) -> bool {
        &&& config.finite()
        &&& config.len() > 0
        &&& quorum.subset_of(config)
        &&& quorum.len() >= config.len() / 2 + 1
    }

    /// During joint consensus, a quorum must contain a majority
    /// of both the old and new configurations.
    pub open spec fn is_joint_quorum(
        quorum: Set<int>,
        old_config: Set<int>,
        new_config: Set<int>,
    ) -> bool {
        &&& quorum.subset_of(old_config + new_config)
        &&& is_majority_of(quorum.intersect(old_config), old_config)
        &&& is_majority_of(quorum.intersect(new_config), new_config)
    }

    /// Derive the active membership phase directly from the committed
    /// prefix of Raft's actual log.
    ///
    /// Data payloads are skipped. The latest committed Configuration
    /// payload determines the active membership phase.
    pub open spec fn active_membership_phase_from_raft_log(
        log: Seq<LLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    ) -> MembershipPhase
        decreases committed_len
    {
        if committed_len <= 0 || committed_len > log.len() {
            initial_phase
        } else {
            match log[committed_len - 1].payload {
                LLogValue::Data {
                    value: _,
                } => {
                    active_membership_phase_from_raft_log(
                        log,
                        committed_len - 1,
                        initial_phase,
                    )
                },
                LLogValue::Configuration {
                    phase,
                } => {
                    membership_phase_view(phase)
                },
            }
        }
    }

    /// A valid quorum depends on the current membership phase.
    pub open spec fn is_quorum_for_phase(
        quorum: Set<int>,
        phase: MembershipPhase,
    ) -> bool {
        match phase {
            MembershipPhase::Stable { config } => {
                is_majority_of(quorum, config)
            },
            MembershipPhase::Joint {
                old_config,
                new_config,
            } => {
                is_joint_quorum(
                    quorum,
                    old_config,
                    new_config,
                )
            },
        }
    }

    /// The membership phase that governs one server's next protocol
    /// decision is derived from that server's committed Raft-log prefix.
    pub open spec fn active_membership_phase_for_state(
        s: LState,
        c: LConstants,
    ) -> MembershipPhase {
        active_membership_phase_from_raft_log(
            s.log,
            s.commit_index,
            MembershipPhase::Stable {
                config: c.servers,
            },
        )
    }

    /// A candidate has enough votes exactly when its collected voter set
    /// is a quorum for the membership phase in its committed log.
    pub open spec fn has_active_election_quorum(
        s: LState,
        c: LConstants,
    ) -> bool {
        is_quorum_for_phase(
            s.votes_granted,
            active_membership_phase_for_state(s, c),
        )
    }

    /// The candidate's vote set after accepting one additional vote is
    /// a quorum for the membership phase in its committed log.
    pub open spec fn has_active_election_quorum_after_vote(
        s: LState,
        c: LConstants,
        voter: int,
    ) -> bool {
        is_quorum_for_phase(
            s.votes_granted.insert(voter),
            active_membership_phase_for_state(s, c),
        )
    }

    /// A leader's saved election certificate is valid when the votes it
    /// collected form a quorum for the exact membership phase saved at
    /// election time.
    pub open spec fn has_recorded_election_quorum(
        s: LState,
    ) -> bool {
        if s.role is Leader {
            match s.election_membership_phase {
                Some(phase) => is_quorum_for_phase(
                    s.votes_granted,
                    phase,
                ),
                None => false,
            }
        } else {
            true
        }
    }

    /// The set whose cardinality is currently returned by
    /// the fixed-membership replicator_count helper.
    pub open spec fn replicator_set(
        s: LState,
        c: LConstants,
        idx: int,
    ) -> Set<int> {
        c.servers.filter(|server: int|
            server == c.my_id
            || (s.match_index.contains_key(server as u64)
                && s.match_index[server as u64] as int >= idx)
        )
    }

    /// A leader has enough replicas to commit an index exactly when
    /// those replicas form a quorum for its active committed membership.
    pub open spec fn has_active_commit_quorum(
        s: LState,
        c: LConstants,
        idx: int,
    ) -> bool {
        is_quorum_for_phase(
            replicator_set(s, c, idx),
            active_membership_phase_for_state(s, c),
        )
    }

    /// Legal membership-phase progression for joint consensus.
    ///
    /// A stable configuration may remain stable or enter a joint phase
    /// whose old configuration matches it. A joint phase may remain
    /// unchanged or finish at its new configuration.
    pub open spec fn is_legal_phase_progression(
        phase: MembershipPhase,
        phase_: MembershipPhase,
    ) -> bool {
        match phase {
            MembershipPhase::Stable { config } => {
                match phase_ {
                    MembershipPhase::Stable { config: config_ } => {
                        config_ == config
                    },
                    MembershipPhase::Joint {
                        old_config,
                        new_config: _,
                    } => {
                        old_config == config
                    },
                }
            },
            MembershipPhase::Joint {
                old_config,
                new_config,
            } => {
                match phase_ {
                    MembershipPhase::Joint {
                        old_config: old_config_,
                        new_config: new_config_,
                    } => {
                        old_config_ == old_config
                            && new_config_ == new_config
                    },
                    MembershipPhase::Stable { config } => {
                        config == new_config
                    },
                }
            },
        }
    }

    /// Local mathematical validity of a configuration-commit certificate.
    ///
    /// The certificate points at an actual Configuration entry, records the
    /// phase derived from the prefix immediately before that entry, carries a
    /// valid quorum for that phase, and records a legal next membership phase.
    pub open spec fn configuration_commit_certificate_matches_log(
        certificate: ConfigurationCommitCertificate,
        log: Seq<LLogEntry>,
        initial_phase: MembershipPhase,
    ) -> bool {
        &&& 0 <= certificate.log_index < log.len()
        &&& log[certificate.log_index] == certificate.entry
        &&& certificate.governing_phase
            == active_membership_phase_from_raft_log(
                log,
                certificate.log_index,
                initial_phase,
            )
        &&& is_quorum_for_phase(
            certificate.quorum,
            certificate.governing_phase,
        )
        &&& match certificate.entry.payload {
            LLogValue::Configuration { phase } => {
                is_legal_phase_progression(
                    certificate.governing_phase,
                    membership_phase_view(phase),
                )
            },
            LLogValue::Data { value: _ } => false,
        }
    }

    /// A valid certificate's log position is exactly a Configuration entry.
    pub proof fn lemma_configuration_commit_certificate_is_configuration(
        certificate: ConfigurationCommitCertificate,
        log: Seq<LLogEntry>,
        initial_phase: MembershipPhase,
    )
        requires configuration_commit_certificate_matches_log(
            certificate,
            log,
            initial_phase,
        )
        ensures log[certificate.log_index].payload is Configuration
    {
    }

    /// No configuration change is already waiting in the uncommitted
    /// suffix. This enforces one membership transition at a time.
    pub open spec fn uncommitted_suffix_has_no_configuration(
        log: Seq<LLogEntry>,
        committed_len: int,
    ) -> bool {
        &&& 0 <= committed_len <= log.len()
        &&& forall |index: int|
            committed_len <= index < log.len()
            ==> !(log[index].payload is Configuration)
    }

    /// One commit-index advancement may cross ordinary Data entries, but
    /// it must stop when it reaches the first Configuration entry.
    ///
    /// `new_committed_len` is a prefix length, so its final newly committed
    /// entry is at `new_committed_len - 1`. That final entry may itself be a
    /// Configuration entry; every earlier entry in the newly committed
    /// interval must be Data.
    pub open spec fn commit_interval_stops_at_first_configuration(
        log: Seq<LLogEntry>,
        old_committed_len: int,
        new_committed_len: int,
    ) -> bool {
        &&& 0 <= old_committed_len
        &&& old_committed_len < new_committed_len
        &&& new_committed_len <= log.len()
        &&& forall |index: int|
            old_committed_len <= index < new_committed_len - 1
            ==> !(log[index].payload is Configuration)
    }
}
