use crate::common::collections::sets::lemma_quorum_intersection;
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
}
