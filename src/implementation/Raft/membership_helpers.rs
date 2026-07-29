use crate::common::collections::hashsets::{
    hashset_to_vec,
    lemma_hashset_view_finite,
};
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

} // verus!
