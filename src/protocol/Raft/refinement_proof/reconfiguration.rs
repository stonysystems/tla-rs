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
