use crate::common::collections::hashsets::{
    clone_hashset_u64,
    hashset_to_vec,
    lemma_set_u64_to_int_len,
};
use crate::generated::Raft::types_gen::{
    CConstants,
    CLogEntry,
    CLogValue,
    CMembershipConfig,
    CMembershipPhase,
    CState,
    clone_membership_phase,
};
use crate::protocol::Raft::membership::{
    active_membership_phase_from_raft_log,
    active_membership_phase_for_state,
    election_membership_phase_for_state,
    has_active_commit_quorum,
    commit_interval_stops_at_first_configuration,
    has_active_election_quorum,
    has_active_election_quorum_after_vote,
    is_joint_quorum,
    is_majority_of,
    is_quorum_for_phase,
    membership_phase_view,
    replicator_set,
    MembershipPhase,
};
use std::collections::HashSet;
use std::sync::Arc;
use vstd::assert_sets_equal;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::std_specs::hash::*;

verus! {

/// Concrete-set form of the stable-configuration majority predicate.
///
/// Keeping this helper over u64 sets lets executable code reason about
/// HashSet views before a separate bridge converts server IDs to int.
pub open spec fn is_u64_majority_of(
    quorum: Set<u64>,
    config: Set<u64>,
) -> bool {
    &&& config.len() > 0
    &&& quorum.subset_of(config)
    &&& quorum.len() >= config.len() / 2 + 1
}

/// Convert the sequence-backed executable membership representation into
/// a HashSet. Duplicate IDs, if present, are deliberately counted once.
pub fn membership_servers_set(
    servers: &Vec<u64>,
) -> (result: HashSet<u64>)
    ensures
        result@ == servers@.to_set(),
{
    broadcast use group_hash_axioms;

    let mut result = HashSet::<u64>::new();
    let mut i: usize = 0;

    while i < servers.len()
        invariant
            0 <= i <= servers.len(),
            result@ == servers@.subrange(0, i as int).to_set(),
        decreases
            servers.len() - i,
    {
        let server = servers[i];
        let ghost previous = result@;
        result.insert(server);

        proof {
            assert(result@ == previous.insert(server));
            assert(
                servers@.subrange(0, i as int + 1)
                    == servers@.subrange(0, i as int).push(server)
            );
            servers@.subrange(0, i as int)
                .lemma_push_to_set_commute(server);
        }

        i = i + 1;
    }

    assert(servers@.subrange(0, servers@.len() as int) == servers@);
    result
}

/// Executably decide mathematical HashSet inclusion.
pub fn hashset_is_subset(
    subset: &HashSet<u64>,
    superset: &HashSet<u64>,
) -> (result: bool)
    ensures
        result == subset@.subset_of(superset@),
{
    broadcast use group_hash_axioms;

    let elements = hashset_to_vec(subset);
    let mut i: usize = 0;

    while i < elements.len()
        invariant
            0 <= i <= elements.len(),
            forall |k: int|
                0 <= k < i
                ==> superset@.contains(#[trigger] elements@[k]),
            forall |k: int|
                0 <= k < elements@.len()
                ==> subset@.contains(#[trigger] elements@[k]),
            forall |server: u64|
                subset@.contains(server)
                ==> exists |k: int| 0 <= k < elements@.len()
                    && elements@[k] == server,
        decreases
            elements.len() - i,
    {
        if !superset.contains(&elements[i]) {
            assert(subset@.contains(elements@[i as int]));
            assert(!subset@.subset_of(superset@));
            return false;
        }
        i = i + 1;
    }

    assert(subset@.subset_of(superset@)) by {
        assert forall |server: u64|
            subset@.contains(server)
            implies superset@.contains(server)
        by {
            let index = choose |index: int|
                0 <= index < elements@.len()
                && elements@[index] == server;
            assert(superset@.contains(elements@[index]));
        };
    };

    true
}

/// Executably check whether a vote set is a majority of a sequence-backed
/// configuration, using set cardinality rather than vector length.
pub fn is_majority_of_servers(
    quorum: &HashSet<u64>,
    servers: &Vec<u64>,
) -> (result: bool)
    ensures
        result == is_u64_majority_of(
            quorum@,
            servers@.to_set(),
        ),
{
    broadcast use group_hash_axioms;

    let config = membership_servers_set(servers);
    let is_subset = hashset_is_subset(quorum, &config);

    if config.len() == 0 {
        assert(config@.len() == 0);
        false
    } else if !is_subset {
        false
    } else {
        let quorum_size = quorum.len();
        let config_size = config.len();

        if quorum_size >= config_size / 2 + 1 {
            assert(quorum@.len() >= config@.len() / 2 + 1);
            true
        } else {
            assert(quorum@.len() < config@.len() / 2 + 1);
            false
        }
    }
}

/// Casting executable u64 server IDs to logical int IDs preserves the
/// stable-majority predicate.
pub proof fn lemma_u64_majority_matches_logical(
    quorum: Set<u64>,
    servers: Seq<u64>,
)
    ensures
        is_u64_majority_of(
            quorum,
            servers.to_set(),
        ) == is_majority_of(
            quorum.map(|server: u64| server as int),
            servers.map(
                |i: int, server: u64| server as int,
            ).to_set(),
        ),
{
    let config = servers.to_set();
    let cast = |server: u64| server as int;
    let mapped_servers = servers.map_values(cast);

    servers.lemma_to_set_map_commutes(cast);
    lemma_set_u64_to_int_len(quorum);
    lemma_set_u64_to_int_len(config);

    assert(servers.map(
        |i: int, server: u64| server as int,
    ) == mapped_servers) by {
        assert_seqs_equal!(
            servers.map(
                |i: int, server: u64| server as int,
            ),
            mapped_servers
        );
    };

    assert(
        quorum.map(cast).subset_of(config.map(cast))
        == quorum.subset_of(config)
    ) by {
        if quorum.subset_of(config) {
            assert(quorum.map(cast).subset_of(config.map(cast))) by {
                assert forall |logical_server: int|
                    quorum.map(cast).contains(logical_server)
                    implies config.map(cast).contains(logical_server)
                by {
                    let concrete_server = choose |concrete_server: u64|
                        quorum.contains(concrete_server)
                        && cast(concrete_server) == logical_server;
                    assert(config.contains(concrete_server));
                };
            };
        } else {
            let concrete_server = choose |concrete_server: u64|
                quorum.contains(concrete_server)
                && !config.contains(concrete_server);

            assert(quorum.map(cast).contains(cast(concrete_server)));
            assert(!config.map(cast).contains(cast(concrete_server))) by {
                if config.map(cast).contains(cast(concrete_server)) {
                    let other = choose |other: u64|
                        config.contains(other)
                        && cast(other) == cast(concrete_server);
                    assert(other == concrete_server);
                    assert(false);
                }
            };
            assert(!quorum.map(cast).subset_of(config.map(cast)));
        }
    };
}

/// Executable stable-majority check with an ensures clause stated directly
/// in the logical membership model used by Raft's proof.
pub fn is_majority_of_membership_view(
    quorum: &HashSet<u64>,
    servers: &Vec<u64>,
) -> (result: bool)
    ensures
        result == is_majority_of(
            quorum@.map(|server: u64| server as int),
            servers@.map(
                |i: int, server: u64| server as int,
            ).to_set(),
        ),
{
    let result = is_majority_of_servers(quorum, servers);
    proof {
        lemma_u64_majority_matches_logical(
            quorum@,
            servers@,
        );
    }
    result
}

/// Concrete-set form of the joint-consensus quorum predicate.
pub open spec fn is_u64_joint_quorum(
    quorum: Set<u64>,
    old_config: Set<u64>,
    new_config: Set<u64>,
) -> bool {
    &&& quorum.subset_of(old_config + new_config)
    &&& is_u64_majority_of(
        quorum.intersect(old_config),
        old_config,
    )
    &&& is_u64_majority_of(
        quorum.intersect(new_config),
        new_config,
    )
}

/// Build the union of two sequence-backed membership configurations.
pub fn membership_union_set(
    old_servers: &Vec<u64>,
    new_servers: &Vec<u64>,
) -> (result: HashSet<u64>)
    ensures
        result@ == old_servers@.to_set() + new_servers@.to_set(),
{
    broadcast use group_hash_axioms;

    let mut result = membership_servers_set(old_servers);
    let mut i: usize = 0;

    while i < new_servers.len()
        invariant
            0 <= i <= new_servers.len(),
            result@ == old_servers@.to_set()
                + new_servers@.subrange(0, i as int).to_set(),
        decreases
            new_servers.len() - i,
    {
        let server = new_servers[i];
        let ghost previous = result@;
        result.insert(server);

        proof {
            assert(result@ == previous.insert(server));
            assert(
                new_servers@.subrange(0, i as int + 1)
                    == new_servers@.subrange(0, i as int).push(server)
            );
            new_servers@.subrange(0, i as int)
                .lemma_push_to_set_commute(server);
        }

        i = i + 1;
    }

    assert(
        new_servers@.subrange(
            0,
            new_servers@.len() as int,
        ) == new_servers@
    );
    result
}

/// Intersect a vote set with a sequence-backed membership configuration.
pub fn quorum_intersection_with_servers(
    quorum: &HashSet<u64>,
    servers: &Vec<u64>,
) -> (result: HashSet<u64>)
    ensures
        result@ == quorum@.intersect(servers@.to_set()),
{
    broadcast use group_hash_axioms;

    let mut result = HashSet::<u64>::new();
    let mut i: usize = 0;

    while i < servers.len()
        invariant
            0 <= i <= servers.len(),
            result@ == quorum@.intersect(
                servers@.subrange(0, i as int).to_set(),
            ),
        decreases
            servers.len() - i,
    {
        let server = servers[i];
        let ghost previous = result@;

        if quorum.contains(&server) {
            result.insert(server);
            assert(result@ == previous.insert(server));
        }

        proof {
            assert(
                servers@.subrange(0, i as int + 1)
                    == servers@.subrange(0, i as int).push(server)
            );
            servers@.subrange(0, i as int)
                .lemma_push_to_set_commute(server);

            assert_sets_equal!(
                result@,
                quorum@.intersect(
                    servers@.subrange(
                        0,
                        i as int + 1,
                    ).to_set(),
                )
            );
        }

        i = i + 1;
    }

    assert(
        servers@.subrange(
            0,
            servers@.len() as int,
        ) == servers@
    );
    result
}

/// Executably decide the concrete joint-consensus quorum condition.
pub fn is_joint_quorum_servers(
    quorum: &HashSet<u64>,
    old_servers: &Vec<u64>,
    new_servers: &Vec<u64>,
) -> (result: bool)
    ensures
        result == is_u64_joint_quorum(
            quorum@,
            old_servers@.to_set(),
            new_servers@.to_set(),
        ),
{
    let union = membership_union_set(
        old_servers,
        new_servers,
    );
    let within_union = hashset_is_subset(quorum, &union);

    let old_votes = quorum_intersection_with_servers(
        quorum,
        old_servers,
    );
    let new_votes = quorum_intersection_with_servers(
        quorum,
        new_servers,
    );

    let old_majority = is_majority_of_servers(
        &old_votes,
        old_servers,
    );
    let new_majority = is_majority_of_servers(
        &new_votes,
        new_servers,
    );

    within_union && old_majority && new_majority
}

/// Mapping injective u64 server IDs to int preserves set inclusion.
pub proof fn lemma_u64_cast_map_subset_iff(
    subset: Set<u64>,
    superset: Set<u64>,
)
    ensures
        subset.map(|server: u64| server as int).subset_of(
            superset.map(|server: u64| server as int),
        ) == subset.subset_of(superset),
{
    let cast = |server: u64| server as int;

    if subset.subset_of(superset) {
        assert(subset.map(cast).subset_of(superset.map(cast))) by {
            assert forall |logical_server: int|
                subset.map(cast).contains(logical_server)
                implies superset.map(cast).contains(logical_server)
            by {
                let concrete_server = choose |concrete_server: u64|
                    subset.contains(concrete_server)
                    && cast(concrete_server) == logical_server;
                assert(superset.contains(concrete_server));
            };
        };
    } else {
        let concrete_server = choose |concrete_server: u64|
            subset.contains(concrete_server)
            && !superset.contains(concrete_server);

        assert(subset.map(cast).contains(cast(concrete_server)));
        assert(!superset.map(cast).contains(cast(concrete_server))) by {
            if superset.map(cast).contains(cast(concrete_server)) {
                let other = choose |other: u64|
                    superset.contains(other)
                    && cast(other) == cast(concrete_server);
                assert(other == concrete_server);
                assert(false);
            }
        };
        assert(!subset.map(cast).subset_of(superset.map(cast)));
    }
}

/// Mapping u64 server IDs to int commutes with set union.
pub proof fn lemma_u64_cast_map_union(
    left: Set<u64>,
    right: Set<u64>,
)
    ensures
        (left + right).map(
            |server: u64| server as int,
        ) == left.map(
            |server: u64| server as int,
        ) + right.map(
            |server: u64| server as int,
        ),
{
    let cast = |server: u64| server as int;

    let mapped_union = (left + right).map(cast);
    let union_of_maps = left.map(cast) + right.map(cast);

    assert(mapped_union.subset_of(union_of_maps)) by {
        assert forall |logical_server: int|
            mapped_union.contains(logical_server)
            implies union_of_maps.contains(logical_server)
        by {
            let concrete_server = choose |concrete_server: u64|
                (left + right).contains(concrete_server)
                && cast(concrete_server) == logical_server;

            if left.contains(concrete_server) {
                assert(left.map(cast).contains(logical_server));
            } else {
                assert(right.contains(concrete_server));
                assert(right.map(cast).contains(logical_server));
            }
        };
    };

    assert(union_of_maps.subset_of(mapped_union)) by {
        assert forall |logical_server: int|
            union_of_maps.contains(logical_server)
            implies mapped_union.contains(logical_server)
        by {
            if left.map(cast).contains(logical_server) {
                let concrete_server = choose |concrete_server: u64|
                    left.contains(concrete_server)
                    && cast(concrete_server) == logical_server;
                assert((left + right).contains(concrete_server));
            } else {
                let concrete_server = choose |concrete_server: u64|
                    right.contains(concrete_server)
                    && cast(concrete_server) == logical_server;
                assert((left + right).contains(concrete_server));
            }
        };
    };

    assert_sets_equal!(
        mapped_union,
        union_of_maps
    );
}

/// Because the u64-to-int cast is injective, mapping also commutes with
/// intersection.
pub proof fn lemma_u64_cast_map_intersection(
    left: Set<u64>,
    right: Set<u64>,
)
    ensures
        left.intersect(right).map(
            |server: u64| server as int,
        ) == left.map(
            |server: u64| server as int,
        ).intersect(
            right.map(|server: u64| server as int),
        ),
{
    let cast = |server: u64| server as int;
    let mapped_intersection = left.intersect(right).map(cast);
    let intersection_of_maps =
        left.map(cast).intersect(right.map(cast));

    assert(mapped_intersection.subset_of(intersection_of_maps)) by {
        assert forall |logical_server: int|
            mapped_intersection.contains(logical_server)
            implies intersection_of_maps.contains(logical_server)
        by {
            let concrete_server = choose |concrete_server: u64|
                left.intersect(right).contains(concrete_server)
                && cast(concrete_server) == logical_server;
        };
    };

    assert(intersection_of_maps.subset_of(mapped_intersection)) by {
        assert forall |logical_server: int|
            intersection_of_maps.contains(logical_server)
            implies mapped_intersection.contains(logical_server)
        by {
            let left_server = choose |left_server: u64|
                left.contains(left_server)
                && cast(left_server) == logical_server;
            let right_server = choose |right_server: u64|
                right.contains(right_server)
                && cast(right_server) == logical_server;
            assert(left_server == right_server);
            assert(left.intersect(right).contains(left_server));
        };
    };

    assert_sets_equal!(
        mapped_intersection,
        intersection_of_maps
    );
}

/// Casting executable server IDs to logical IDs preserves the full
/// joint-consensus quorum predicate.
pub proof fn lemma_u64_joint_quorum_matches_logical(
    quorum: Set<u64>,
    old_servers: Seq<u64>,
    new_servers: Seq<u64>,
)
    ensures
        is_u64_joint_quorum(
            quorum,
            old_servers.to_set(),
            new_servers.to_set(),
        ) == is_joint_quorum(
            quorum.map(|server: u64| server as int),
            old_servers.map(
                |i: int, server: u64| server as int,
            ).to_set(),
            new_servers.map(
                |i: int, server: u64| server as int,
            ).to_set(),
        ),
{
    let old_config = old_servers.to_set();
    let new_config = new_servers.to_set();
    let cast = |server: u64| server as int;

    broadcast use vstd::set::group_set_lemmas;

    old_servers.lemma_to_set_map_commutes(cast);
    new_servers.lemma_to_set_map_commutes(cast);

    assert(old_servers.map(
        |i: int, server: u64| server as int,
    ) == old_servers.map_values(cast)) by {
        assert_seqs_equal!(
            old_servers.map(
                |i: int, server: u64| server as int,
            ),
            old_servers.map_values(cast)
        );
    };
    assert(new_servers.map(
        |i: int, server: u64| server as int,
    ) == new_servers.map_values(cast)) by {
        assert_seqs_equal!(
            new_servers.map(
                |i: int, server: u64| server as int,
            ),
            new_servers.map_values(cast)
        );
    };

    lemma_u64_cast_map_union(old_config, new_config);
    lemma_u64_cast_map_subset_iff(
        quorum,
        old_config + new_config,
    );

    lemma_u64_cast_map_intersection(quorum, old_config);
    lemma_u64_cast_map_intersection(quorum, new_config);

    lemma_u64_majority_matches_logical(
        quorum.intersect(old_config),
        old_servers,
    );
    lemma_u64_majority_matches_logical(
        quorum.intersect(new_config),
        new_servers,
    );
}

/// Executable joint-quorum check stated directly in Raft's logical
/// membership model.
pub fn is_joint_quorum_membership_view(
    quorum: &HashSet<u64>,
    old_servers: &Vec<u64>,
    new_servers: &Vec<u64>,
) -> (result: bool)
    ensures
        result == is_joint_quorum(
            quorum@.map(|server: u64| server as int),
            old_servers@.map(
                |i: int, server: u64| server as int,
            ).to_set(),
            new_servers@.map(
                |i: int, server: u64| server as int,
            ).to_set(),
        ),
{
    let result = is_joint_quorum_servers(
        quorum,
        old_servers,
        new_servers,
    );
    proof {
        lemma_u64_joint_quorum_matches_logical(
            quorum@,
            old_servers@,
            new_servers@,
        );
    }
    result
}

/// Check a majority when both the quorum and configuration already use
/// executable HashSet storage.
pub fn is_majority_of_hashset_membership_view(
    quorum: &HashSet<u64>,
    config: &HashSet<u64>,
) -> (result: bool)
    ensures
        result == is_majority_of(
            quorum@.map(|server: u64| server as int),
            config@.map(|server: u64| server as int),
        ),
{
    broadcast use group_hash_axioms;

    let is_subset = hashset_is_subset(quorum, config);

    proof {
        lemma_set_u64_to_int_len(quorum@);
        lemma_set_u64_to_int_len(config@);
        lemma_u64_cast_map_subset_iff(
            quorum@,
            config@,
        );
    }

    if config.len() == 0 {
        assert(config@.len() == 0);
        false
    } else if !is_subset {
        false
    } else {
        let quorum_size = quorum.len();
        let config_size = config.len();

        if quorum_size >= config_size / 2 + 1 {
            assert(
                quorum@.map(
                    |server: u64| server as int,
                ).len()
                >= config@.map(
                    |server: u64| server as int,
                ).len() / 2 + 1
            );
            true
        } else {
            assert(
                quorum@.map(
                    |server: u64| server as int,
                ).len()
                < config@.map(
                    |server: u64| server as int,
                ).len() / 2 + 1
            );
            false
        }
    }
}

/// Dispatch an executable election-quorum check according to a concrete
/// stable or joint membership phase.
pub fn is_quorum_for_membership_phase(
    quorum: &HashSet<u64>,
    phase: &CMembershipPhase,
) -> (result: bool)
    ensures
        result == is_quorum_for_phase(
            quorum@.map(|server: u64| server as int),
            membership_phase_view(phase@),
        ),
{
    match phase {
        CMembershipPhase::Stable { config } => {
            is_majority_of_membership_view(
                quorum,
                &config.servers,
            )
        },
        CMembershipPhase::Joint {
            old_config,
            new_config,
        } => {
            is_joint_quorum_membership_view(
                quorum,
                &old_config.servers,
                &new_config.servers,
            )
        },
    }
}

pub proof fn lemma_membership_vector_view_matches_set(
    servers: Seq<u64>,
    concrete: Set<u64>,
)
    requires
        servers.to_set() == concrete,
    ensures
        servers.map(
            |i: int, server: u64| server as int,
        ).to_set() == concrete.map(
            |server: u64| server as int,
        ),
{
    let cast = |server: u64| server as int;
    servers.lemma_to_set_map_commutes(cast);
    assert(
        servers.map(
            |i: int, server: u64| server as int,
        ) == servers.map_values(cast)
    ) by {
        assert_seqs_equal!(
            servers.map(
                |i: int, server: u64| server as int,
            ),
            servers.map_values(cast)
        );
    };
}

/// Return the concrete membership phase selected by the latest
/// configuration entry in the committed log prefix.
pub fn active_membership_phase_exec(
    s: &CState,
    c: &CConstants,
) -> (result: CMembershipPhase)
    ensures
        membership_phase_view(result@)
        == active_membership_phase_for_state(s@, c@),
{
    if s.commit_index == 0
        || s.commit_index > s.log.len() as u64
    {
        let servers = hashset_to_vec(&c.servers);
        proof {
            assert_sets_equal!(servers@.to_set(), c.servers@);
            lemma_membership_vector_view_matches_set(
                servers@,
                c.servers@,
            );
        }
        let result = CMembershipPhase::Stable {
            config: CMembershipConfig { servers },
        };
        proof {
            assert(
                membership_phase_view(result@)
                == (MembershipPhase::Stable {
                    config: c@.servers,
                })
            );
            assert(
                active_membership_phase_for_state(s@, c@)
                == (MembershipPhase::Stable {
                    config: c@.servers,
                })
            );
        }
        return result;
    }

    let mut remaining = s.commit_index;

    while remaining > 0
        invariant
            0 <= remaining <= s.commit_index,
            remaining <= s.log.len() as u64,
            active_membership_phase_from_raft_log(
                s@.log,
                s@.commit_index,
                MembershipPhase::Stable {
                    config: c@.servers,
                },
            ) == active_membership_phase_from_raft_log(
                s@.log,
                remaining as int,
                MembershipPhase::Stable {
                    config: c@.servers,
                },
            ),
        decreases
            remaining,
    {
        let log: &Vec<crate::generated::Raft::types_gen::CLogEntry> = &*s.log;
        let entry = &log[(remaining - 1) as usize];

        match &entry.payload {
            CLogValue::Configuration { phase } => {
                let result = clone_membership_phase(phase);
                proof {
                    assert(
                        s@.log[remaining as int - 1].payload
                        == crate::protocol::Raft::types::LLogValue::Configuration {
                            phase: phase@,
                        }
                    );
                    assert(
                        active_membership_phase_from_raft_log(
                            s@.log,
                            remaining as int,
                            MembershipPhase::Stable {
                                config: c@.servers,
                            },
                        ) == membership_phase_view(phase@)
                    );
                    assert(
                        active_membership_phase_from_raft_log(
                            s@.log,
                            s@.commit_index,
                            MembershipPhase::Stable {
                                config: c@.servers,
                            },
                        ) == membership_phase_view(phase@)
                    );
                }
                return result;
            },
            CLogValue::Data { value } => {
                proof {
                    assert(
                        s@.log[remaining as int - 1].payload
                        == crate::protocol::Raft::types::LLogValue::Data {
                            value: *value as int,
                        }
                    );
                    assert(
                        active_membership_phase_from_raft_log(
                            s@.log,
                            remaining as int,
                            MembershipPhase::Stable {
                                config: c@.servers,
                            },
                        ) == active_membership_phase_from_raft_log(
                            s@.log,
                            remaining as int - 1,
                            MembershipPhase::Stable {
                                config: c@.servers,
                            },
                        )
                    );
                }
                remaining = remaining - 1;
            },
        }
    }

    let servers = hashset_to_vec(&c.servers);
    proof {
        assert_sets_equal!(servers@.to_set(), c.servers@);
        lemma_membership_vector_view_matches_set(
            servers@,
            c.servers@,
        );
    }
    let result = CMembershipPhase::Stable {
        config: CMembershipConfig { servers },
    };
    proof {
        assert(
            active_membership_phase_from_raft_log(
                s@.log,
                s@.commit_index,
                MembershipPhase::Stable {
                    config: c@.servers,
                },
            ) == (MembershipPhase::Stable {
                config: c@.servers,
            })
        );
        assert(
            active_membership_phase_for_state(
                s@,
                c@,
            ) == active_membership_phase_from_raft_log(
                s@.log,
                s@.commit_index,
                MembershipPhase::Stable {
                    config: c@.servers,
                },
            )
        );
    }
    result
}

/// Return the concrete membership phase selected by the latest
/// configuration entry present anywhere in the candidate's log.
pub fn election_membership_phase_exec(
    s: &CState,
    c: &CConstants,
) -> (result: CMembershipPhase)
    requires
        s.valid(),
        c.valid(),
    ensures
        membership_phase_view(result@)
            == election_membership_phase_for_state(s@, c@),
{
    let mut s_with_full_log = s.clone();
    s_with_full_log.commit_index = s.log.len() as u64;

    proof {
        assert(s_with_full_log@.log == s@.log);
        assert(s_with_full_log@.commit_index == s@.log.len());
        assert(s_with_full_log.valid());
        assert(
            active_membership_phase_for_state(s_with_full_log@, c@)
                == election_membership_phase_for_state(s@, c@)
        );
    }

    active_membership_phase_exec(&s_with_full_log, c)
}

/// Executably derive the election quorum from the latest configuration
/// present anywhere in the candidate's current log.
pub fn has_active_election_quorum_exec(
    s: &CState,
    c: &CConstants,
) -> (result: bool)
    ensures
        result == has_active_election_quorum(s@, c@),
{
    if s.log.len() == 0
    {
        let result = is_majority_of_hashset_membership_view(
            &s.votes_granted,
            &c.servers,
        );
        proof {
            assert(
                active_membership_phase_from_raft_log(
                    s@.log,
                    s@.log.len() as int,
                    MembershipPhase::Stable {
                        config: c@.servers,
                    },
                ) == (MembershipPhase::Stable {
                    config: c@.servers,
                })
            );
        }
        return result;
    }

    let mut remaining = s.log.len() as u64;

    while remaining > 0
        invariant
            0 <= remaining <= s.log.len() as u64,
            remaining <= s.log.len() as u64,
            active_membership_phase_from_raft_log(
                s@.log,
                s@.log.len() as int,
                MembershipPhase::Stable {
                    config: c@.servers,
                },
            ) == active_membership_phase_from_raft_log(
                s@.log,
                remaining as int,
                MembershipPhase::Stable {
                    config: c@.servers,
                },
            ),
        decreases
            remaining,
    {
        let log: &Vec<crate::generated::Raft::types_gen::CLogEntry> = &*s.log;
        let entry = &log[(remaining - 1) as usize];

        match &entry.payload {
            CLogValue::Configuration { phase } => {
                let result = is_quorum_for_membership_phase(
                    &s.votes_granted,
                    phase,
                );
                proof {
                    assert(
                        s@.log[remaining as int - 1].payload
                        == crate::protocol::Raft::types::LLogValue::Configuration {
                            phase: phase@,
                        }
                    );
                    assert(
                        active_membership_phase_from_raft_log(
                            s@.log,
                            remaining as int,
                            MembershipPhase::Stable {
                                config: c@.servers,
                            },
                        ) == membership_phase_view(phase@)
                    );
                    assert(
                        active_membership_phase_from_raft_log(
                            s@.log,
                            s@.log.len() as int,
                            MembershipPhase::Stable {
                                config: c@.servers,
                            },
                        ) == membership_phase_view(phase@)
                    );
                    assert(
                        election_membership_phase_for_state(
                            s@,
                            c@,
                        ) == active_membership_phase_from_raft_log(
                            s@.log,
                            s@.log.len() as int,
                            MembershipPhase::Stable {
                                config: c@.servers,
                            },
                        )
                    );
                    assert(
                        election_membership_phase_for_state(
                            s@,
                            c@,
                        ) == membership_phase_view(phase@)
                    );
                    assert(
                        has_active_election_quorum(s@, c@)
                        == is_quorum_for_phase(
                            s@.votes_granted,
                            membership_phase_view(phase@),
                        )
                    );
                }
                return result;
            },
            CLogValue::Data { value } => {
                proof {
                    assert(
                        s@.log[remaining as int - 1].payload
                        == crate::protocol::Raft::types::LLogValue::Data {
                            value: *value as int,
                        }
                    );
                    assert(
                        active_membership_phase_from_raft_log(
                            s@.log,
                            remaining as int,
                            MembershipPhase::Stable {
                                config: c@.servers,
                            },
                        ) == active_membership_phase_from_raft_log(
                            s@.log,
                            remaining as int - 1,
                            MembershipPhase::Stable {
                                config: c@.servers,
                            },
                        )
                    );
                }
                remaining = remaining - 1;
            },
        }
    }

    let result = is_majority_of_hashset_membership_view(
        &s.votes_granted,
        &c.servers,
    );
    proof {
        assert(
            active_membership_phase_from_raft_log(
                s@.log,
                s@.log.len() as int,
                MembershipPhase::Stable {
                    config: c@.servers,
                },
            ) == (MembershipPhase::Stable {
                config: c@.servers,
            })
        );
        assert(
            election_membership_phase_for_state(
                s@,
                c@,
            ) == active_membership_phase_from_raft_log(
                s@.log,
                s@.log.len() as int,
                MembershipPhase::Stable {
                    config: c@.servers,
                },
            )
        );
        assert(
            election_membership_phase_for_state(
                s@,
                c@,
            ) == (MembershipPhase::Stable {
                config: c@.servers,
            })
        );
        assert(
            has_active_election_quorum(s@, c@)
            == is_quorum_for_phase(
                s@.votes_granted,
                MembershipPhase::Stable {
                    config: c@.servers,
                },
            )
        );
    }
    result
}

/// Evaluate the active election quorum after accepting one additional vote.
pub fn has_active_election_quorum_after_vote_exec(
    s: &CState,
    c: &CConstants,
    voter: &u64,
) -> (result: bool)
    ensures
        result == has_active_election_quorum_after_vote(
            s@,
            c@,
            *voter as int,
        ),
{
    broadcast use group_hash_axioms;

    let ghost old_votes = s.votes_granted@;
    let mut votes = clone_hashset_u64(&s.votes_granted);
    votes.insert(*voter);

    proof {
        assert(votes@ == old_votes.insert(*voter));
        old_votes.lemma_set_map_insert_commute(
            *voter,
            |server: u64| server as int,
        );
    }

    let mut s_with_vote = s.clone();
    s_with_vote.votes_granted = Arc::new(votes);

    let result = has_active_election_quorum_exec(
        &s_with_vote,
        c,
    );

    proof {
        assert(
            s_with_vote@.votes_granted
            == old_votes.insert(*voter).map(
                |server: u64| server as int,
            )
        );
        assert(
            s_with_vote@.votes_granted
            == s@.votes_granted.insert(*voter as int)
        );
        assert(
            election_membership_phase_for_state(s_with_vote@, c@)
            == election_membership_phase_for_state(s@, c@)
        );
    }
    result
}

/// Transpiler-facing name for the verified after-vote election guard.
#[allow(non_snake_case)]
pub fn Chas_active_election_quorum_after_vote(
    s: &CState,
    c: &CConstants,
    voter: &u64,
) -> (result: bool)
    ensures
        result == has_active_election_quorum_after_vote(
            s@,
            c@,
            *voter as int,
        ),
{
    has_active_election_quorum_after_vote_exec(
        s,
        c,
        voter,
    )
}

/// Concrete predicate for whether one server has replicated an index.
pub open spec fn is_u64_replicator(
    match_index: Map<u64, u64>,
    my_id: u64,
    server: u64,
    idx: u64,
) -> bool {
    server == my_id
    || (match_index.contains_key(server)
        && match_index[server] >= idx)
}

/// Concrete set of servers that have replicated a candidate index.
pub open spec fn u64_replicator_set(
    servers: Set<u64>,
    match_index: Map<u64, u64>,
    my_id: u64,
    idx: u64,
) -> Set<u64> {
    servers.filter(|server: u64|
        is_u64_replicator(
            match_index,
            my_id,
            server,
            idx,
        )
    )
}

/// Converting concrete server IDs to logical IDs preserves the exact
/// replication set used by the membership-level commit predicate.
pub proof fn lemma_u64_replicator_set_matches_logical(
    s: &CState,
    c: &CConstants,
    idx: &u64,
)
    ensures
        u64_replicator_set(
            c.servers@,
            s.match_index@,
            c.my_id,
            *idx,
        ).map(
            |server: u64| server as int,
        ) == replicator_set(s@, c@, *idx as int),
{
    let cast = |server: u64| server as int;
    let concrete = u64_replicator_set(
        c.servers@,
        s.match_index@,
        c.my_id,
        *idx,
    );
    let logical = replicator_set(s@, c@, *idx as int);

    assert_sets_equal!(
        concrete.map(cast),
        logical,
        logical_server => {
            if concrete.map(cast).contains(logical_server) {
                let concrete_server = choose |server: u64|
                    concrete.contains(server)
                    && cast(server) == logical_server;

                assert(c.servers@.contains(concrete_server));
                assert(c@.servers.contains(logical_server));
                assert(
                    is_u64_replicator(
                        s.match_index@,
                        c.my_id,
                        concrete_server,
                        *idx,
                    )
                );
                assert(
                    logical_server == c@.my_id
                    || (s@.match_index.contains_key(
                            logical_server as u64,
                        )
                        && s@.match_index[
                            logical_server as u64
                        ] as int >= *idx as int)
                );
            } else if logical.contains(logical_server) {
                assert(c@.servers.contains(logical_server));
                let concrete_server = choose |server: u64|
                    c.servers@.contains(server)
                    && cast(server) == logical_server;
                assert(c.servers@.contains(concrete_server));
                assert(
                    logical_server == c@.my_id
                    || (s@.match_index.contains_key(
                            logical_server as u64,
                        )
                        && s@.match_index[
                            logical_server as u64
                        ] as int >= *idx as int)
                );
                assert(concrete_server as int == logical_server);
                assert(
                    concrete_server == c.my_id
                    || (s.match_index@.contains_key(
                            concrete_server,
                        )
                        && s.match_index@[concrete_server] >= *idx)
                );
                assert(
                    is_u64_replicator(
                        s.match_index@,
                        c.my_id,
                        concrete_server,
                        *idx,
                    )
                );
                assert(concrete.contains(concrete_server));
            }
        }
    );
}

/// Build the executable replication set for a candidate commit index.
pub fn replicator_set_exec(
    s: &CState,
    c: &CConstants,
    idx: &u64,
) -> (result: HashSet<u64>)
    ensures
        result@ == u64_replicator_set(
            c.servers@,
            s.match_index@,
            c.my_id,
            *idx,
        ),
        result@.map(
            |server: u64| server as int,
        ) == replicator_set(
            s@,
            c@,
            *idx as int,
        ),
{
    broadcast use group_hash_axioms;

    let servers = hashset_to_vec(&c.servers);
    let mut result = HashSet::<u64>::new();
    let mut i: usize = 0;

    while i < servers.len()
        invariant
            0 <= i <= servers.len(),
            result@ == servers@.subrange(
                0,
                i as int,
            ).to_set().filter(|server: u64|
                is_u64_replicator(
                    s.match_index@,
                    c.my_id,
                    server,
                    *idx,
                )
            ),
            forall |k: int|
                0 <= k < servers@.len()
                ==> c.servers@.contains(#[trigger] servers@[k]),
            forall |server: u64|
                c.servers@.contains(server)
                ==> exists |k: int|
                    0 <= k < servers@.len()
                    && servers@[k] == server,
        decreases
            servers.len() - i,
    {
        let server = servers[i];
        let replicated = if server == c.my_id {
            true
        } else {
            match s.match_index.get(&server) {
                Some(matched) => *matched >= *idx,
                None => false,
            }
        };

        if replicated {
            result.insert(server);
        }

        proof {
            assert(
                replicated == is_u64_replicator(
                    s.match_index@,
                    c.my_id,
                    server,
                    *idx,
                )
            );
            assert(
                servers@.subrange(0, i as int + 1)
                == servers@.subrange(0, i as int).push(server)
            );
            servers@.subrange(0, i as int)
                .lemma_push_to_set_commute(server);
            assert_sets_equal!(
                result@,
                servers@.subrange(
                    0,
                    i as int + 1,
                ).to_set().filter(|candidate: u64|
                    is_u64_replicator(
                        s.match_index@,
                        c.my_id,
                        candidate,
                        *idx,
                    )
                )
            );
        }

        i = i + 1;
    }

    proof {
        assert(
            servers@.subrange(0, servers@.len() as int)
            == servers@
        );
        assert_sets_equal!(
            servers@.to_set(),
            c.servers@
        );
        assert(
            result@ == c.servers@.filter(|server: u64|
                is_u64_replicator(
                    s.match_index@,
                    c.my_id,
                    server,
                    *idx,
                )
            )
        );
        assert(
            result@ == u64_replicator_set(
                c.servers@,
                s.match_index@,
                c.my_id,
                *idx,
            )
        );
        lemma_u64_replicator_set_matches_logical(
            s,
            c,
            idx,
        );
    }
    result
}

/// Executably check that one commit-index advancement stops at the first
/// Configuration entry in the newly committed interval.
pub fn commit_interval_stops_at_first_configuration_exec(
    s: &CState,
    new_commit_index: &u64,
) -> (result: bool)
    requires
        s.valid(),
        s.commit_index < *new_commit_index,
        *new_commit_index as int <= s@.log.len(),
        *new_commit_index <= s.log.len() as u64,
    ensures
        result == commit_interval_stops_at_first_configuration(
            s@.log,
            s@.commit_index,
            *new_commit_index as int,
        ),
{
    let mut cursor = s.commit_index + 1;

    while cursor < *new_commit_index
        invariant
            0 < cursor,
            s.commit_index < cursor,
            cursor <= *new_commit_index,
            cursor <= s.log.len() as u64,
            *new_commit_index as int <= s@.log.len(),
            forall |checked: int|
                s@.commit_index <= checked < cursor - 1
                ==> !(s@.log[checked].payload is Configuration),
        decreases
            *new_commit_index - cursor,
    {
        let log: &Vec<CLogEntry> = &*s.log;
        let entry = &log[(cursor - 1) as usize];

        match &entry.payload {
            CLogValue::Configuration { phase: _ } => {
                proof {
                    assert(
                        s@.log[cursor as int - 1].payload
                            is Configuration
                    );
                    assert(
                        s@.commit_index
                            <= cursor as int - 1
                            < *new_commit_index as int - 1
                    );
                    assert(
                        !commit_interval_stops_at_first_configuration(
                            s@.log,
                            s@.commit_index,
                            *new_commit_index as int,
                        )
                    );
                }
                return false;
            },
            CLogValue::Data { value: _ } => {
                proof {
                    assert(
                        !(s@.log[cursor as int - 1].payload
                            is Configuration)
                    );
                }
            },
        }

        cursor = cursor + 1;
    }

    proof {
        assert(cursor == *new_commit_index);
        assert forall |checked: int|
            s@.commit_index
                <= checked
                < *new_commit_index as int - 1
            implies !(s@.log[checked].payload is Configuration)
        by {
            assert(checked < cursor - 1);
        };
    }

    true
}

/// Transpiler-facing name for the verified commit-boundary guard.
#[allow(non_snake_case)]
pub fn Ccommit_interval_stops_at_first_configuration(
    s: &CState,
    new_commit_index: &u64,
) -> (result: bool)
    requires
        s.valid(),
        s.commit_index < *new_commit_index,
        *new_commit_index as int <= s@.log.len(),
        *new_commit_index <= s.log.len() as u64,
    ensures
        result == commit_interval_stops_at_first_configuration(
            s@.log,
            s@.commit_index,
            *new_commit_index as int,
        ),
{
    commit_interval_stops_at_first_configuration_exec(
        s,
        new_commit_index,
    )
}

/// Decide whether the servers that replicated `idx` form a quorum for
/// the membership phase derived from the committed log.
pub fn has_active_commit_quorum_exec(
    s: &CState,
    c: &CConstants,
    idx: &u64,
) -> (result: bool)
    ensures
        result == has_active_commit_quorum(
            s@,
            c@,
            *idx as int,
        ),
{
    let replicators = replicator_set_exec(
        s,
        c,
        idx,
    );

    let phase = active_membership_phase_exec(s, c);
    let result = is_quorum_for_membership_phase(
        &replicators,
        &phase,
    );

    proof {
        assert(
            replicators@.map(|server: u64| server as int)
                == replicator_set(
                s@,
                c@,
                *idx as int,
            )
        );
        assert(
            membership_phase_view(phase@)
                == active_membership_phase_for_state(s@, c@)
        );
        assert(
            result == is_quorum_for_phase(
                replicator_set(s@, c@, *idx as int),
                active_membership_phase_for_state(s@, c@),
            )
        );
        assert(
            result == has_active_commit_quorum(
                s@,
                c@,
                *idx as int,
            )
        );
    }
    result
}

/// Transpiler-facing name for the verified dynamic commit guard.
#[allow(non_snake_case)]
pub fn Chas_active_commit_quorum(
    s: &CState,
    c: &CConstants,
    idx: &u64,
) -> (result: bool)
    ensures
        result == has_active_commit_quorum(
            s@,
            c@,
            *idx as int,
        ),
{
    has_active_commit_quorum_exec(s, c, idx)
}

} // verus!
