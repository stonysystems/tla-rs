//! Increasing transaction sequences, including empty histories during synchronization.
use vstd::prelude::*;
use super::zab::{self as z,Txn,Zxid};
use super::zk_election as fle;
use super::zookeeper::{floor_index,sub};
verus! {
broadcast use { vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn shape(h: Seq<Txn>) -> bool {
    (forall |k: int| 0 <= k < h.len() ==> (#[trigger] h[k]).zxid.epoch >= 0 && h[k].zxid.counter > 0)
    && forall |k: int| 0 < k < h.len() ==> #[trigger] z::next_zxid(h[k-1].zxid,h[k].zxid)
}
pub open spec fn bounded(h: Seq<Txn>,e: int) -> bool { super::zab_log_math::bounded(h,e) }
pub proof fn ordered(h: Seq<Txn>,x: int,y: int)
    requires shape(h),0 <= x <= y < h.len()
    ensures !z::newer(h[x].zxid,h[y].zxid),x < y ==> z::newer(h[y].zxid,h[x].zxid)
    decreases y-x
{
    if x < y { ordered(h,x,y-1); assert(z::next_zxid(h[y-1].zxid,h[y].zxid)); }
}
pub proof fn index_bounds(h: Seq<Txn>,zxid: Zxid)
    requires shape(h)
    ensures 0 <= z::index(h,zxid) <= h.len()+1
{
    let q=Set::range(1,h.len() as int+1).filter(|k: int| h[k-1].zxid == zxid);
    if !q.is_empty() {
        let k=choose |k: int| q.contains(k);
        assert(q =~= set![k]) by {
            assert forall |p: int| q.contains(p) implies p == k by { if p < k { ordered(h,p-1,k-1); } else { ordered(h,k-1,p-1); } }
        }
    }
}
pub proof fn floor_bounds(h: Seq<Txn>,zxid: Zxid)
    requires shape(h)
    ensures 0 <= floor_index(h,zxid) <= h.len()
{
    index_bounds(h,zxid);
    let q=Set::range(1,h.len() as int+1).filter(|k: int| z::newer(h[k-1].zxid,zxid));
    if !q.is_empty() {
        let le=|x: int,y: int| x <= y; q.find_unique_minimal_ensures(le); q.lemma_minimal_equivalent_least(le,q.find_unique_minimal(le));
        let k=q.find_unique_minimal(le);
        assert(q.contains(k)); assert forall |j: int| q.contains(j) implies k <= j by { assert(le(k,j)); }
        assert(exists |k: int| q.contains(k) && forall |j: int| q.contains(j) ==> k <= j);
    }
}
pub proof fn transfer(h: Seq<Txn>,q: Seq<Txn>,e: int)
    requires shape(h),bounded(h,e),super::zab_log_math::same(h,q)
    ensures shape(q),bounded(q,e)
{
    assert forall |k: int| 0 <= k < q.len() implies (#[trigger] q[k]).zxid.epoch >= 0 && q[k].zxid.counter > 0 by { assert(z::equal(h[k],q[k])); }
    assert forall |k: int| 0 < k < q.len() implies #[trigger] z::next_zxid(q[k-1].zxid,q[k].zxid) by { assert(z::equal(h[k-1],q[k-1])); assert(z::equal(h[k],q[k])); assert(z::next_zxid(h[k-1].zxid,h[k].zxid)); }
    assert forall |k: int| 0 <= k < q.len() implies (#[trigger] q[k]).zxid.epoch <= e by { assert(z::equal(h[k],q[k])); }
}
pub proof fn prefix(h: Seq<Txn>,end: int,e: int)
    requires shape(h),bounded(h,e),end <= h.len()
    ensures shape(sub(h,1,end)),bounded(sub(h,1,end),e)
{
    let q=sub(h,1,end);
    assert forall |k: int| 0 <= k < q.len() implies (#[trigger] q[k]).zxid.epoch >= 0 && q[k].zxid.counter > 0 by {}
    assert forall |k: int| 0 < k < q.len() implies #[trigger] z::next_zxid(q[k-1].zxid,q[k].zxid) by { assert(z::next_zxid(h[k-1].zxid,h[k].zxid)); }
    assert forall |k: int| 0 <= k < q.len() implies (#[trigger] q[k]).zxid.epoch <= e by {}
}
pub proof fn append(h: Seq<Txn>,t: Txn,e: int)
    requires shape(h),bounded(h,e),0 <= t.zxid.epoch <= e,t.zxid.counter > 0,h.len() == 0 || z::next_zxid(fle::latest(h).zxid,t.zxid)
    ensures shape(h.push(t)),bounded(h.push(t),e)
{
    let q=h.push(t);
    assert forall |k: int| 0 <= k < q.len() implies (#[trigger] q[k]).zxid.epoch >= 0 && q[k].zxid.counter > 0 by {}
    assert forall |k: int| 0 < k < q.len() implies #[trigger] z::next_zxid(q[k-1].zxid,q[k].zxid) by { if k < h.len() { assert(z::next_zxid(h[k-1].zxid,h[k].zxid)); } }
    assert forall |k: int| 0 <= k < q.len() implies (#[trigger] q[k]).zxid.epoch <= e by {}
}
pub proof fn request(h: Seq<Txn>,e: int,t: Txn)
    requires shape(h),bounded(h,e),e >= 0,t.zxid == (Zxid { epoch: e,counter: if fle::latest(h).zxid.epoch == e { fle::latest(h).zxid.counter+1 } else { 1 } })
    ensures shape(h.push(t)),bounded(h.push(t),e)
{
    if h.len() > 0 { assert(h[h.len()-1].zxid.epoch <= e); }
    append(h,t,e);
}
pub proof fn loosen(h: Seq<Txn>,a: int,b: int)
    requires bounded(h,a),a <= b
    ensures bounded(h,b)
{
    assert forall |k: int| 0 <= k < h.len() implies (#[trigger] h[k]).zxid.epoch <= b by {}
}
} // verus!
