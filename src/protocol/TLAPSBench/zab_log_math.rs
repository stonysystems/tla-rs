//! Sequence lemmas for dense, increasing Zab transaction identifiers.
use vstd::prelude::*;
use super::zab::{*,equal};
verus! {
pub open spec fn shape(h: Seq<Txn>) -> bool {
    h.len() > 0 && h[0].zxid == boot() && h[0].value == 0
    && (forall |k: int| 0 <= k < h.len() ==> (#[trigger] h[k]).zxid.epoch >= 0 && h[k].zxid.counter > 0)
    && (forall |k: int| 0 < k < h.len() ==> #[trigger] next_zxid(h[k-1].zxid,h[k].zxid))
}
pub open spec fn bounded(h: Seq<Txn>,e: int) -> bool {
    forall |k: int| 0 <= k < h.len() ==> (#[trigger] h[k]).zxid.epoch <= e
}
pub open spec fn same(a: Seq<Txn>,b: Seq<Txn>) -> bool {
    a.len() == b.len() && forall |k: int| 0 <= k < a.len() ==> #[trigger] equal(a[k],b[k])
}
pub proof fn ordered(h: Seq<Txn>,x: int,y: int)
    requires shape(h),0 <= x <= y < h.len()
    ensures !newer(h[x].zxid,h[y].zxid),x < y ==> newer(h[y].zxid,h[x].zxid)
    decreases y-x
{
    if x < y {
        ordered(h,x,y-1); assert(next_zxid(h[y-1].zxid,h[y].zxid));
    }
}
pub proof fn last_bound(h: Seq<Txn>,e: int)
    requires shape(h),last(h).epoch <= e
    ensures bounded(h,e)
{
    assert forall |k: int| 0 <= k < h.len() implies (#[trigger] h[k]).zxid.epoch <= e by { ordered(h,k,h.len() as int-1); }
}
pub proof fn drop_last(h: Seq<Txn>)
    requires shape(h),h.len() > 1
    ensures shape(h.drop_last())
{
    let u=h.drop_last();
    assert forall |k: int| 0 < k < u.len() implies #[trigger] next_zxid(u[k-1].zxid,u[k].zxid) by { assert(next_zxid(h[k-1].zxid,h[k].zxid)); }
}
pub proof fn counter_position(h: Seq<Txn>,count: int) -> (at: int)
    requires shape(h),1 <= count <= last(h).counter
    ensures 0 <= at < h.len(),h[at].zxid == (Zxid { epoch: last(h).epoch,counter: count })
    decreases h.len()
{
    if count == last(h).counter { h.len() as int-1 }
    else {
        assert(h.len() > 1); drop_last(h); let p=h.len() as int-1;
        assert(next_zxid(h[p-1].zxid,h[p].zxid)); counter_position(h.drop_last(),count)
    }
}
pub proof fn index_at(h: Seq<Txn>,at: int)
    requires shape(h),0 <= at < h.len()
    ensures index(h,h[at].zxid) == at+1
{
    let z=h[at].zxid;
    let matches=Set::range(1,h.len() as int+1).filter(|k: int| h[k-1].zxid == z);
    assert(matches.contains(at+1));
    assert(matches =~= set![at+1]) by {
        assert forall |k: int| matches.contains(k) implies k == at+1 by {
            if k-1 < at { ordered(h,k-1,at); } else { ordered(h,at,k-1); }
        }
    }
}
pub proof fn lookup(h: Seq<Txn>,z: Zxid)
    requires 1 <= index(h,z) <= h.len()
    ensures h[index(h,z)-1].zxid == z
{
    let matches=Set::range(1,h.len() as int+1).filter(|k: int| h[k-1].zxid == z);
    assert(matches.len() == 1); assert(!matches.is_empty());
    let k=choose |k: int| matches.contains(k); assert(k == index(h,z));
}
pub proof fn broadcast_index(n: LServer)
    requires shape(n.history),0 <= n.sent < counter(n)
    ensures 1 <= index(n.history,Zxid { epoch: n.current,counter: n.sent+1 }) <= n.history.len(),
        n.history[index(n.history,Zxid { epoch: n.current,counter: n.sent+1 })-1].zxid == (Zxid { epoch: n.current,counter: n.sent+1 })
{
    let at=counter_position(n.history,n.sent+1); index_at(n.history,at);
}
pub proof fn append(h: Seq<Txn>,t: Txn)
    requires shape(h),next_zxid(last(h),t.zxid)
    ensures shape(h.push(t))
{
    let u=h.push(t);
    assert forall |k: int| 0 < k < u.len() implies #[trigger] next_zxid(u[k-1].zxid,u[k].zxid) by {
        if k < h.len() { assert(next_zxid(h[k-1].zxid,h[k].zxid)); }
    }
}
pub proof fn request(h: Seq<Txn>,e: int,t: Txn)
    requires shape(h),bounded(h,e),t.zxid == (Zxid { epoch: e,counter: if e == last(h).epoch { last(h).counter+1 } else { 1 } })
    ensures shape(h.push(t)),bounded(h.push(t),e)
{
    assert(h[h.len() as int-1].zxid.epoch <= e); append(h,t);
}
pub proof fn transfer(a: Seq<Txn>,b: Seq<Txn>,e: int)
    requires shape(a),bounded(a,e),same(a,b)
    ensures shape(b),bounded(b,e)
{
    assert(equal(a[0],b[0]));
    assert forall |k: int| 0 <= k < b.len() implies (#[trigger] b[k]).zxid.epoch >= 0 && b[k].zxid.counter > 0 by { assert(equal(a[k],b[k])); }
    assert forall |k: int| 0 < k < b.len() implies #[trigger] next_zxid(b[k-1].zxid,b[k].zxid) by {
        assert(next_zxid(a[k-1].zxid,a[k].zxid)); assert(equal(a[k-1],b[k-1])); assert(equal(a[k],b[k]));
    }
    assert forall |k: int| 0 <= k < b.len() implies (#[trigger] b[k]).zxid.epoch <= e by { assert(equal(a[k],b[k])); }
}
pub proof fn ack_contents(h: Seq<Txn>,i: int,z: Zxid)
    ensures same(h,init_ack(h,i)),same(h,update_ack(h,i,z))
{}
pub proof fn same_last(a: Seq<Txn>,b: Seq<Txn>)
    requires same(a,b)
    ensures last(a) == last(b)
{
    if a.len() > 0 { assert(equal(a[a.len() as int-1],b[a.len() as int-1])); }
}
pub proof fn ack_prefix(h: Seq<Txn>,i: int,p: int)
    requires shape(h),0 <= p < h.len()
    ensures forall |k: int| 0 <= k < h.len() ==> (#[trigger] update_ack(h,i,h[p].zxid)[k]).ack ==
        (if k <= p { h[k].ack.insert(i) } else { h[k].ack })
{
    let z=h[p].zxid;
    assert forall |k: int| 0 <= k < p+1 implies !newer(h[k].zxid,z) by { ordered(h,k,p); }
    if p+1 < h.len() { ordered(h,p,p+1); }
    assert(exists |b: int| 0 <= b <= h.len() && (forall |k: int| 0 <= k < b ==> !newer(h[k].zxid,z)) && (b < h.len() ==> newer(h[b].zxid,z)));
    let b=choose |b: int| 0 <= b <= h.len() && (forall |k: int| 0 <= k < b ==> !newer(h[k].zxid,z)) && (b < h.len() ==> newer(h[b].zxid,z));
    if b <= p { ordered(h,b,p); assert(false); }
    if b > p+1 { assert(!newer(h[p+1].zxid,z)); ordered(h,p,p+1); assert(false); }
    assert(b == p+1);
}
pub proof fn update_contents(h: Seq<Txn>,at: int,t: Txn)
    requires 0 <= at < h.len(),equal(h[at],t)
    ensures same(h,h.update(at,t))
{}
} // verus!
