use crate::common::collections::hashsets::{
    hashset_to_vec,
    lemma_hashset_view_finite,
    lemma_set_u64_to_int_len,
};
use crate::protocol::Raft::membership::is_majority_of;
use std::collections::HashSet;
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
    &&& config.finite()
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

    proof {
        lemma_hashset_view_finite(&config);
        lemma_hashset_view_finite(quorum);
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
    requires
        quorum.finite(),
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

    broadcast use seq_to_set_is_finite;

    servers.lemma_to_set_map_commutes(cast);
    lemma_set_u64_to_int_len(quorum);
    lemma_set_u64_to_int_len(config);
    quorum.lemma_map_finite(cast);
    config.lemma_map_finite(cast);

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
        lemma_hashset_view_finite(quorum);
        lemma_u64_majority_matches_logical(
            quorum@,
            servers@,
        );
    }
    result
}

} // verus!
