use crate::common::collections::sets::lemma_quorum_intersection;
use crate::protocol::Raft::raft::replicator_count;
use crate::protocol::Raft::types::{LConstants, LState};
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

    /// Specification-level representation of entries that may affect
    /// membership. This remains separate from the concrete Raft log
    /// while the committed-log design is developed and verified.
    pub enum MembershipLogEntry {
        /// An ordinary replicated command that does not change membership.
        Data {
            value: int,
        },

        /// A complete membership phase recorded in the replicated log.
        Configuration {
            phase: MembershipPhase,
        },
    }

    /// Derive the active membership phase from the committed log prefix.
    ///
    /// Only entries with indices below committed_len are considered.
    /// The latest committed Configuration entry determines the active phase.
    /// If no such entry exists, the initial phase remains active.
    pub open spec fn active_membership_phase(
        log: Seq<MembershipLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    ) -> MembershipPhase
        decreases committed_len
    {
        if committed_len <= 0 || committed_len > log.len() {
            initial_phase
        } else {
            match log[committed_len - 1] {
                MembershipLogEntry::Data { value: _ } => {
                    active_membership_phase(
                        log,
                        committed_len - 1,
                        initial_phase,
                    )
                },
                MembershipLogEntry::Configuration { phase } => {
                    phase
                },
            }
        }
    }

    /// With no committed entries, the initial membership remains active.
    pub proof fn lemma_no_committed_entries_use_initial_phase(
        log: Seq<MembershipLogEntry>,
        initial_phase: MembershipPhase,
    )
        ensures
            active_membership_phase(
                log,
                0,
                initial_phase,
            ) == initial_phase,
    {
    }

    /// If a configuration entry is appended and immediately committed,
    /// the phase contained in that entry becomes active.
    pub proof fn lemma_committed_configuration_becomes_active(
        log: Seq<MembershipLogEntry>,
        initial_phase: MembershipPhase,
        phase: MembershipPhase,
    )
        ensures
            active_membership_phase(
                log.push(
                    MembershipLogEntry::Configuration {
                        phase,
                    },
                ),
                    (log.len() + 1) as int,
                initial_phase,
            ) == phase,
    {
    }

    /// Appending an entry beyond the committed prefix cannot affect
    /// the active membership phase.
    pub proof fn lemma_uncommitted_entry_does_not_affect_active_phase(
        log: Seq<MembershipLogEntry>,
        uncommitted_entry: MembershipLogEntry,
        committed_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            0 <= committed_len,
            committed_len <= log.len(),
        ensures
            active_membership_phase(
                log.push(uncommitted_entry),
                committed_len,
                initial_phase,
            ) == active_membership_phase(
                log,
                committed_len,
                initial_phase,
            ),
        decreases committed_len
    {
        if committed_len <= 0 {
        } else {
            assert(0 <= committed_len - 1);
            assert(committed_len - 1 < log.len());

            assert(
                log.push(uncommitted_entry)[committed_len - 1]
                    == log[committed_len - 1]
            );

            match log[committed_len - 1] {
                MembershipLogEntry::Data { value: _ } => {
                    lemma_uncommitted_entry_does_not_affect_active_phase(
                        log,
                        uncommitted_entry,
                        committed_len - 1,
                        initial_phase,
                    );
                },
                MembershipLogEntry::Configuration { phase: _ } => {
                },
            }
        }
    }

    /// Committing an ordinary data entry does not change membership.
    pub proof fn lemma_committed_data_preserves_active_phase(
        log: Seq<MembershipLogEntry>,
        initial_phase: MembershipPhase,
        value: int,
    )
        ensures
            active_membership_phase(
                log.push(
                    MembershipLogEntry::Data {
                        value,
                    },
                ),
                (log.len() + 1) as int,
                initial_phase,
            ) == active_membership_phase(
                log,
                log.len() as int,
                initial_phase,
            ),
    {
        let data_entry = MembershipLogEntry::Data {
            value,
        };

        assert(
            active_membership_phase(
                log.push(data_entry),
                (log.len() + 1) as int,
                initial_phase,
            ) == active_membership_phase(
                log.push(data_entry),
                log.len() as int,
                initial_phase,
            )
        );

        lemma_uncommitted_entry_does_not_affect_active_phase(
            log,
            data_entry,
            log.len() as int,
            initial_phase,
        );
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

    /// Any two majorities of the same configuration overlap.
    pub proof fn lemma_majorities_intersect(
        quorum1: Set<int>,
        quorum2: Set<int>,
        config: Set<int>,
    )
        requires
            is_majority_of(quorum1, config),
            is_majority_of(quorum2, config),
        ensures
            exists |server: int|
                quorum1.contains(server) && quorum2.contains(server),
    {
        let majority_size = config.len() / 2 + 1;

        assert(quorum1.len() >= majority_size);
        assert(quorum2.len() >= majority_size);
        assert(majority_size + majority_size > config.len());
        assert(quorum1.len() + quorum2.len() > config.len());

        lemma_quorum_intersection(quorum1, quorum2, config);
    }

    /// An old-configuration majority overlaps every joint quorum.
    pub proof fn lemma_old_majority_intersects_joint(
        old_quorum: Set<int>,
        joint_quorum: Set<int>,
        old_config: Set<int>,
        new_config: Set<int>,
    )
        requires
            is_majority_of(old_quorum, old_config),
            is_joint_quorum(joint_quorum, old_config, new_config),
        ensures
            exists |server: int|
                old_quorum.contains(server)
                && joint_quorum.contains(server),
    {
        let joint_old = joint_quorum.intersect(old_config);

        lemma_majorities_intersect(
            old_quorum,
            joint_old,
            old_config,
        );

        let server = choose |server: int|
            old_quorum.contains(server)
            && joint_old.contains(server);

        assert(old_quorum.contains(server));
        assert(joint_old.contains(server));
        assert(joint_quorum.contains(server));
    }

    /// A new-configuration majority overlaps every joint quorum.
    pub proof fn lemma_new_majority_intersects_joint(
        new_quorum: Set<int>,
        joint_quorum: Set<int>,
        old_config: Set<int>,
        new_config: Set<int>,
    )
        requires
            is_majority_of(new_quorum, new_config),
            is_joint_quorum(joint_quorum, old_config, new_config),
        ensures
            exists |server: int|
                new_quorum.contains(server)
                && joint_quorum.contains(server),
    {
        let joint_new = joint_quorum.intersect(new_config);

        lemma_majorities_intersect(
            new_quorum,
            joint_new,
            new_config,
        );

        let server = choose |server: int|
            new_quorum.contains(server)
            && joint_new.contains(server);

        assert(new_quorum.contains(server));
        assert(joint_new.contains(server));
        assert(joint_quorum.contains(server));
    }

    /// Any two joint-consensus quorums overlap.
    pub proof fn lemma_joint_quorums_intersect(
        joint_quorum1: Set<int>,
        joint_quorum2: Set<int>,
        old_config: Set<int>,
        new_config: Set<int>,
    )
        requires
            is_joint_quorum(
                joint_quorum1,
                old_config,
                new_config,
            ),
            is_joint_quorum(
                joint_quorum2,
                old_config,
                new_config,
            ),
        ensures
            exists |server: int|
                joint_quorum1.contains(server)
                && joint_quorum2.contains(server),
    {
        let joint1_old = joint_quorum1.intersect(old_config);
        let joint2_old = joint_quorum2.intersect(old_config);

        lemma_majorities_intersect(
            joint1_old,
            joint2_old,
            old_config,
        );

        let server = choose |server: int|
            joint1_old.contains(server)
            && joint2_old.contains(server);

        assert(joint_quorum1.contains(server));
        assert(joint_quorum2.contains(server));
    }

    /// Any two quorums valid for the same membership phase overlap.
    pub proof fn lemma_phase_quorums_intersect(
        quorum1: Set<int>,
        quorum2: Set<int>,
        phase: MembershipPhase,
    )
        requires
            is_quorum_for_phase(quorum1, phase),
            is_quorum_for_phase(quorum2, phase),
        ensures
            exists |server: int|
                quorum1.contains(server)
                && quorum2.contains(server),
    {
        match phase {
            MembershipPhase::Stable { config } => {
                lemma_majorities_intersect(
                    quorum1,
                    quorum2,
                    config,
                );
            },
            MembershipPhase::Joint {
                old_config,
                new_config,
            } => {
                lemma_joint_quorums_intersect(
                    quorum1,
                    quorum2,
                    old_config,
                    new_config,
                );
            },
        }
    }

    /// A quorum from the old stable phase overlaps a quorum from
    /// the following joint-consensus phase.
    pub proof fn lemma_stable_to_joint_quorums_intersect(
        stable_quorum: Set<int>,
        joint_quorum: Set<int>,
        old_config: Set<int>,
        new_config: Set<int>,
    )
        requires
            is_quorum_for_phase(
                stable_quorum,
                MembershipPhase::Stable {
                    config: old_config,
                },
            ),
            is_quorum_for_phase(
                joint_quorum,
                MembershipPhase::Joint {
                    old_config,
                    new_config,
                },
            ),
        ensures
            exists |server: int|
                stable_quorum.contains(server)
                && joint_quorum.contains(server),
    {
        lemma_old_majority_intersects_joint(
            stable_quorum,
            joint_quorum,
            old_config,
            new_config,
        );
    }

    /// A quorum from the joint-consensus phase overlaps a quorum
    /// from the following new stable phase.
    pub proof fn lemma_joint_to_stable_quorums_intersect(
        joint_quorum: Set<int>,
        stable_quorum: Set<int>,
        old_config: Set<int>,
        new_config: Set<int>,
    )
        requires
            is_quorum_for_phase(
                joint_quorum,
                MembershipPhase::Joint {
                    old_config,
                    new_config,
                },
            ),
            is_quorum_for_phase(
                stable_quorum,
                MembershipPhase::Stable {
                    config: new_config,
                },
            ),
        ensures
            exists |server: int|
                joint_quorum.contains(server)
                && stable_quorum.contains(server),
    {
        lemma_new_majority_intersects_joint(
            stable_quorum,
            joint_quorum,
            old_config,
            new_config,
        );

        let server = choose |server: int|
            stable_quorum.contains(server)
            && joint_quorum.contains(server);

        assert(joint_quorum.contains(server));
        assert(stable_quorum.contains(server));
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

    /// Every membership phase legally progresses to itself.
    /// This covers ordinary data entries, which do not change membership.
    pub proof fn lemma_phase_progression_reflexive(
        phase: MembershipPhase,
    )
        ensures
            is_legal_phase_progression(
                phase,
                phase,
            ),
    {
        match phase {
            MembershipPhase::Stable { config: _ } => {
            },
            MembershipPhase::Joint {
                old_config: _,
                new_config: _,
            } => {
            },
        }
    }

    /// Determine whether the next committed log entry is legal.
    ///
    /// Data entries are always legal because they preserve membership.
    /// Configuration entries must follow the joint-consensus phase order.
    pub open spec fn is_legal_next_membership_log_entry(
        log: Seq<MembershipLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
        entry: MembershipLogEntry,
    ) -> bool {
        &&& 0 <= committed_len
        &&& committed_len <= log.len()
        &&& match entry {
            MembershipLogEntry::Data { value: _ } => {
                true
            },
            MembershipLogEntry::Configuration { phase } => {
                is_legal_phase_progression(
                    active_membership_phase(
                        log,
                        committed_len,
                        initial_phase,
                    ),
                    phase,
                )
            },
        }
    }

    /// Every entry in the committed prefix follows the legal
    /// joint-consensus membership-phase progression.
    pub open spec fn committed_membership_log_is_well_formed(
        log: Seq<MembershipLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    ) -> bool
        decreases committed_len
    {
        if committed_len < 0 || committed_len > log.len() {
            false
        } else if committed_len == 0 {
            true
        } else {
            &&& committed_membership_log_is_well_formed(
                log,
                committed_len - 1,
                initial_phase,
            )
            &&& is_legal_next_membership_log_entry(
                log,
                committed_len - 1,
                initial_phase,
                log[committed_len - 1],
            )
        }
    }

    /// An empty committed prefix is a well-formed membership history.
    pub proof fn lemma_empty_committed_membership_log_is_well_formed(
        log: Seq<MembershipLogEntry>,
        initial_phase: MembershipPhase,
    )
        ensures
            committed_membership_log_is_well_formed(
                log,
                0,
                initial_phase,
            ),
    {
    }

    /// A nonempty well-formed committed prefix consists of a
    /// well-formed shorter prefix followed by one legal entry.
    pub proof fn lemma_well_formed_committed_log_decomposes(
        log: Seq<MembershipLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            committed_membership_log_is_well_formed(
                log,
                committed_len,
                initial_phase,
            ),
            committed_len > 0,
        ensures
            committed_membership_log_is_well_formed(
                log,
                committed_len - 1,
                initial_phase,
            ),
            is_legal_next_membership_log_entry(
                log,
                committed_len - 1,
                initial_phase,
                log[committed_len - 1],
            ),
    {
    }

    /// In every nonempty well-formed committed history, the final
    /// committed entry produces a legal membership-phase progression.
    pub proof fn lemma_well_formed_committed_log_last_step_is_legal(
        log: Seq<MembershipLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            committed_membership_log_is_well_formed(
                log,
                committed_len,
                initial_phase,
            ),
            committed_len > 0,
        ensures
            is_legal_phase_progression(
                active_membership_phase(
                    log,
                    committed_len - 1,
                    initial_phase,
                ),
                active_membership_phase(
                    log,
                    committed_len,
                    initial_phase,
                ),
            ),
    {
        lemma_well_formed_committed_log_decomposes(
            log,
            committed_len,
            initial_phase,
        );

        let previous_phase = active_membership_phase(
            log,
            committed_len - 1,
            initial_phase,
        );

        match log[committed_len - 1] {
            MembershipLogEntry::Data { value: _ } => {
                lemma_phase_progression_reflexive(
                    previous_phase,
                );
            },
            MembershipLogEntry::Configuration { phase } => {
                assert(is_legal_phase_progression(
                    previous_phase,
                    phase,
                ));
            },
        }
    }

    /// Committing a legal next entry preserves the legal membership-phase
    /// progression required by joint consensus.
    pub proof fn lemma_legal_committed_entry_preserves_phase_progression(
        log: Seq<MembershipLogEntry>,
        initial_phase: MembershipPhase,
        entry: MembershipLogEntry,
    )
        requires
            is_legal_next_membership_log_entry(
                log,
                log.len() as int,
                initial_phase,
                entry,
            ),
        ensures
            is_legal_phase_progression(
                active_membership_phase(
                    log,
                    log.len() as int,
                    initial_phase,
                ),
                active_membership_phase(
                    log.push(entry),
                    (log.len() + 1) as int,
                    initial_phase,
                ),
            ),
    {
        let previous_phase = active_membership_phase(
            log,
            log.len() as int,
            initial_phase,
        );

        match entry {
            MembershipLogEntry::Data { value } => {
                lemma_committed_data_preserves_active_phase(
                    log,
                    initial_phase,
                    value,
                );

                lemma_phase_progression_reflexive(
                    previous_phase,
                );
            },
            MembershipLogEntry::Configuration { phase } => {
                assert(is_legal_phase_progression(
                    previous_phase,
                    phase,
                ));

                lemma_committed_configuration_becomes_active(
                    log,
                    initial_phase,
                    phase,
                );
            },
        }
    }

    /// Quorums before and after every legal membership-phase
    /// progression share at least one server.
    pub proof fn lemma_legal_phase_progression_quorums_intersect(
        quorum: Set<int>,
        quorum_: Set<int>,
        phase: MembershipPhase,
        phase_: MembershipPhase,
    )
        requires
            is_legal_phase_progression(phase, phase_),
            is_quorum_for_phase(quorum, phase),
            is_quorum_for_phase(quorum_, phase_),
        ensures
            exists |server: int|
                quorum.contains(server)
                && quorum_.contains(server),
    {
        match phase {
            MembershipPhase::Stable { config } => {
                match phase_ {
                    MembershipPhase::Stable { config: config_ } => {
                        assert(config_ == config);
                        lemma_majorities_intersect(
                            quorum,
                            quorum_,
                            config,
                        );
                    },
                    MembershipPhase::Joint {
                        old_config,
                        new_config,
                    } => {
                        assert(old_config == config);
                        lemma_stable_to_joint_quorums_intersect(
                            quorum,
                            quorum_,
                            config,
                            new_config,
                        );
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
                        assert(old_config_ == old_config);
                        assert(new_config_ == new_config);
                        lemma_joint_quorums_intersect(
                            quorum,
                            quorum_,
                            old_config,
                            new_config,
                        );
                    },
                    MembershipPhase::Stable { config } => {
                        assert(config == new_config);
                        lemma_joint_to_stable_quorums_intersect(
                            quorum,
                            quorum_,
                            old_config,
                            new_config,
                        );
                    },
                }
            },
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

    /// Exposing the underlying set does not change the meaning
    /// of the existing count-based helper.
    pub proof fn lemma_replicator_count_matches_set(
        s: LState,
        c: LConstants,
        idx: int,
    )
        ensures
            replicator_count(s, c, idx)
                == replicator_set(s, c, idx).len() as int,
    {
    }

    /// The existing fixed-membership commit guard implies that
    /// the replicating servers form a valid stable-phase quorum.
    pub proof fn lemma_fixed_commit_guard_implies_stable_phase_quorum(
        s: LState,
        c: LConstants,
        idx: int,
    )
        requires
            c.servers.finite(),
            c.servers.len() > 0,
            c.quorum_size == c.servers.len() / 2 + 1,
            replicator_count(s, c, idx) >= c.quorum_size,
        ensures
            is_quorum_for_phase(
                replicator_set(s, c, idx),
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
    {
        let replicators = replicator_set(s, c, idx);

        assert(replicators.subset_of(c.servers)) by {
            assert forall |server: int|
                replicators.contains(server)
                implies c.servers.contains(server)
            by {
            };
        };

        lemma_replicator_count_matches_set(s, c, idx);

        assert(replicators.len() as int >= c.quorum_size);
        assert(replicators.len() >= c.servers.len() / 2 + 1);
        assert(is_majority_of(replicators, c.servers));
        assert(is_quorum_for_phase(
            replicators,
            MembershipPhase::Stable {
                config: c.servers,
            },
        ));
    }
}
