use super::types::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub proof fn lemma_intersection_bound(c: Constants, a: Set<int>, b: Set<int>)
    requires valid_constants(c), a.subset_of(members(c)), b.subset_of(members(c))
    ensures a.intersect(b).len() as int >= a.len() + b.len() - c.n
{
    broadcast use group_set_properties;
    lemma_len_union(a, b);
    lemma_set_intersect_union_lens(a, b);
    assert(a.union(b).subset_of(members(c)));
    lemma_len_subset(a.union(b), members(c));
    lemma_int_range(0, c.n);
    assert(members(c).len() == c.n);
}

pub proof fn lemma_majorities_intersect(c: Constants, a: Set<int>, b: Set<int>) -> (node: int)
    requires valid_constants(c), majority(c, a), majority(c, b)
    ensures a.contains(node), b.contains(node), member(c, node)
{
    broadcast use group_set_properties;
    broadcast use range_set_properties;
    lemma_intersection_bound(c, a, b);
    assert(a.intersect(b).len() > 0);
    let node = a.intersect(b).choose();
    node
}

pub proof fn lemma_fast_recovery_overlap(c: Constants, fast: Set<int>, recovery: Set<int>)
    requires valid_constants(c), fast_quorum(c, fast), majority(c, recovery)
    ensures
        fast.intersect(recovery).len() >= recovery.len() - c.e,
        recovery.len() - c.e > 0,
{
    lemma_intersection_bound(c, fast, recovery);
}

/// The baseline bound makes a fast quorum intersect the support of a pending
/// recovery. This is the cardinality fact used by the Waiting-abort rule.
pub proof fn lemma_fast_pending_intersection(
    c: Constants, fast: Set<int>, recovery: Set<int>, support: Set<int>,
) -> (node: int)
    requires
        valid_constants(c), fast_quorum(c, fast), majority(c, recovery),
        support.subset_of(recovery), support.len() >= recovery.len() - c.e,
    ensures fast.contains(node), support.contains(node), member(c, node)
{
    broadcast use group_set_properties;
    broadcast use range_set_properties;
    assert(support.subset_of(members(c)));
    lemma_intersection_bound(c, fast, support);
    assert(fast.intersect(support).len() > 0);
    fast.intersect(support).choose()
}

} // verus!
