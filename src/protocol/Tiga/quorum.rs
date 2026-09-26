//! The quorum arithmetic used by local log reconstruction.
use super::types::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub proof fn lemma_intersection(universe: Set<int>, a: Set<int>, b: Set<int>)
    requires a.subset_of(universe), b.subset_of(universe)
    ensures a.intersect(b).len() + universe.len() >= a.len() + b.len()
{
    broadcast use group_set_properties;
    lemma_len_union(a, b);
    assert(a.union(b).subset_of(universe));
    lemma_len_subset(a.union(b), universe);
    lemma_set_intersect_union_lens(a, b);
}

pub proof fn lemma_fast_recovery_intersection(c: Constants, sh: int, fast: Set<int>, recovery: Set<int>)
    requires valid_constants(c), 0 <= sh < c.shards,
        fast.subset_of(shard_members(c, sh)), recovery.subset_of(shard_members(c, sh)),
        fast.len() >= fast_size(c), recovery.len() >= c.f + 1
    ensures fast.intersect(recovery).len() >= recovery_threshold(c)
{
    broadcast use group_set_lib_default;
    assert((sh + 1) * replicas(c) - sh * replicas(c) == replicas(c)) by (nonlinear_arith);
    lemma_int_range(sh * replicas(c), (sh + 1) * replicas(c));
    lemma_intersection(shard_members(c, sh), fast, recovery);
}

pub proof fn lemma_slow_recovery_intersection(c: Constants, sh: int, slow: Set<int>, recovery: Set<int>)
    requires valid_constants(c), 0 <= sh < c.shards,
        slow.subset_of(shard_members(c, sh)), recovery.subset_of(shard_members(c, sh)),
        slow.len() >= c.f + 1, recovery.len() >= c.f + 1
    ensures slow.intersect(recovery).len() > 0
{
    broadcast use group_set_lib_default;
    assert((sh + 1) * replicas(c) - sh * replicas(c) == replicas(c)) by (nonlinear_arith);
    lemma_int_range(sh * replicas(c), (sh + 1) * replicas(c));
    lemma_intersection(shard_members(c, sh), slow, recovery);
}

} // verus!
