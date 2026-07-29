use crate::protocol::Raft::types::{
    LConstants,
    LLogEntry,
    LLogValue,
    LMembershipConfig,
    LMembershipPhase,
    LState,
};
use vstd::prelude::*;

verus! {

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

    /// The cluster is either using one stable configuration or
    /// temporarily requiring approval from old and new configurations.
    pub enum MembershipPhase {
        Stable {
            config: Set<int>,
        },
        Joint {
            old_config: Set<int>,
            new_config: Set<int>,
        },
    }

    /// Mathematical view of an executable membership configuration.
    ///
    /// The concrete representation is a sequence because it can be
    /// transpiled to executable Rust. Quorum proofs use its set view.
    pub open spec fn membership_config_view(
        config: LMembershipConfig,
    ) -> Set<int> {
        config.servers.to_set()
    }

    /// Interpret an executable configuration as a stable proof phase.
    pub open spec fn stable_phase_from_config(
        config: LMembershipConfig,
    ) -> MembershipPhase {
        MembershipPhase::Stable {
            config: membership_config_view(config),
        }
    }

    /// Convert an executable membership phase into the mathematical
    /// phase used by the quorum proofs.
    pub open spec fn membership_phase_view(
        phase: LMembershipPhase,
    ) -> MembershipPhase {
        match phase {
            LMembershipPhase::Stable {
                config,
            } => {
                MembershipPhase::Stable {
                    config: membership_config_view(config),
                }
            },
            LMembershipPhase::Joint {
                old_config,
                new_config,
            } => {
                MembershipPhase::Joint {
                    old_config: membership_config_view(old_config),
                    new_config: membership_config_view(new_config),
                }
            },
        }
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
}
