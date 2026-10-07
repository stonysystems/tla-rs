//! Configuration positions in log prefixes, without protocol assumptions.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_config_lineage as lineage;
verus! {
pub open spec fn configuration(h: Seq<Entry>,c: Constants) -> Set<int> { config_at(h,last_config(h),c) }
pub open spec fn first_config(h: Seq<Entry>,start: int) -> int
    decreases h.len()-start
{
    if start >= h.len() { h.len() as int }
    else if h[start].kind == EntryKind::Config { start }
    else { first_config(h,start+1) }
}
pub proof fn first_config_properties(h: Seq<Entry>,start: int)
    requires 0 <= start <= h.len()
    ensures start <= first_config(h,start) <= h.len(),
        first_config(h,start) < h.len() ==> h[first_config(h,start)].kind == EntryKind::Config,
        forall |k: int| start <= k < first_config(h,start) ==> (#[trigger] h[k]).kind != EntryKind::Config
    decreases h.len()-start
{
    if start < h.len() && h[start].kind != EntryKind::Config {
        first_config_properties(h,start+1);
        assert forall |k: int| start <= k < first_config(h,start) implies (#[trigger] h[k]).kind != EntryKind::Config by {
            if k > start { assert(h[k].kind != EntryKind::Config); }
        }
    }
}
pub proof fn prefix_identity(h: Seq<Entry>)
    ensures sub(h,1,h.len() as int) == h
{ assert(sub(h,1,h.len() as int) =~= h); }
pub proof fn prefix_last(h: Seq<Entry>,length: int)
    requires 0 <= length <= h.len()
    ensures last_config(sub(h,1,length)) <= last_config(h),last_config(sub(h,1,length)) <= length,
        last_config(h) <= length ==> last_config(sub(h,1,length)) == last_config(h)
    decreases h.len()
{
    if length == h.len() { prefix_identity(h); configs::config_positions(h); }
    else {
        assert(h.len() > 0); let old=h.drop_last(); prefix_last(old,length);
        assert(sub(old,1,length) =~= sub(h,1,length));
    }
}
pub proof fn configuration_prefix(h: Seq<Entry>,c: Constants,length: int)
    requires last_config(h) <= length <= h.len()
    ensures configuration(sub(h,1,length),c) == configuration(h,c)
{
    configs::config_positions(h); types::last_config_valid(h); prefix_last(h,length);
}
pub proof fn no_configs(h: Seq<Entry>,start: int,end: int)
    requires 0 <= start <= end <= h.len(),
        forall |k: int| start <= k < end ==> (#[trigger] h[k]).kind != EntryKind::Config
    ensures last_config(sub(h,1,end)) == last_config(sub(h,1,start))
    decreases end-start
{
    if start < end {
        no_configs(h,start,end-1); assert(h[end-1].kind != EntryKind::Config);
        assert(sub(h,1,end).drop_last() =~= sub(h,1,end-1));
    }
}
pub proof fn configuration_no_configs(h: Seq<Entry>,c: Constants,start: int,end: int)
    requires 0 <= start <= end <= h.len(),
        forall |k: int| start <= k < end ==> (#[trigger] h[k]).kind != EntryKind::Config
    ensures configuration(sub(h,1,end),c) == configuration(sub(h,1,start),c)
{
    no_configs(h,start,end); configs::config_positions(sub(h,1,start));
}
pub proof fn configuration_after_entry(h: Seq<Entry>,c: Constants,k: int)
    requires 0 <= k < h.len(),h[k].kind == EntryKind::Config
    ensures last_config(sub(h,1,k+1)) == k+1,configuration(sub(h,1,k+1),c) == h[k].config
{}
pub proof fn first_parent(h: Seq<Entry>,c: Constants,start: int)
    requires 0 <= start <= h.len()
    ensures first_config(h,start) < h.len() ==> lineage::parent(h,first_config(h,start),c) == configuration(sub(h,1,start),c),
        first_config(h,start) == h.len() ==> configuration(h,c) == configuration(sub(h,1,start),c)
{
    first_config_properties(h,start); let end=first_config(h,start); configuration_no_configs(h,c,start,end);
    if end == h.len() { prefix_identity(h); }
}
pub proof fn before_last(h: Seq<Entry>,start: int)
    requires last_config(h) > 0,0 <= start < last_config(h),last_config(sub(h,1,last_config(h) as int-1)) <= start
    ensures first_config(h,start) == last_config(h) as int-1,
        forall |k: int| start <= k < last_config(h)-1 ==> (#[trigger] h[k]).kind != EntryKind::Config
{
    types::last_config_valid(h); let end=last_config(h) as int-1; let old=sub(h,1,end); configs::config_positions(old);
    assert forall |k: int| start <= k < end implies (#[trigger] h[k]).kind != EntryKind::Config by {
        if h[k].kind == EntryKind::Config { assert(old[k].kind == EntryKind::Config); assert(k+1 <= last_config(old)); assert(false); }
    }
    first_config_properties(h,start);
    if first_config(h,start) < end { assert(h[first_config(h,start)].kind != EntryKind::Config); assert(false); }
    if first_config(h,start) > end { assert(h[end].kind != EntryKind::Config); assert(false); }
}
pub proof fn after_last(h: Seq<Entry>,k: int)
    requires 0 <= k < h.len(),last_config(h) <= k
    ensures h[k].kind != EntryKind::Config
    decreases h.len()
{
    if k < h.len()-1 { after_last(h.drop_last(),k); assert(h.drop_last()[k] == h[k]); }
}
pub proof fn entry_below_last(h: Seq<Entry>,length: int,k: int)
    requires 0 <= k < length <= h.len(),h[k].kind == EntryKind::Config
    ensures k+1 <= last_config(sub(h,1,length))
{
    let before=sub(h,1,length); prefix_last(before,k+1);
    assert(sub(before,1,k+1) =~= sub(h,1,k+1));
    assert(last_config(sub(h,1,k+1)) == k+1);
}
} // verus!
