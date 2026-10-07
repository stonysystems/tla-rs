//! Log matching across arbitrary historical snapshots follows from epoch ownership.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs::{self as leader,prefix};
use super::zab_entry_origins::{self as origins,through};
use super::temporal::Behavior;
verus! {
pub proof fn unique_index(h: Seq<Txn>,k: int,l: int)
    requires math::shape(h),0 <= k < h.len(),0 <= l < h.len(),h[k].zxid == h[l].zxid
    ensures k == l
{
    if k < l { math::ordered(h,k,l); } else if l < k { math::ordered(h,l,k); }
}
pub proof fn common_prefix(a: Seq<Txn>,d: Seq<Txn>,old: Seq<Txn>,new: Seq<Txn>,k: int,l: int)
    requires math::shape(new),prefix(old,new),through(a,old,k),through(d,new,l),a[k].zxid == d[l].zxid
    ensures k == l,through(a,d,k)
{
    assert(equal(a[k],old[k])); assert(equal(old[k],new[k])); assert(equal(d[l],new[l])); unique_index(new,k,l);
    assert forall |p: int| 0 <= p <= k implies #[trigger] equal(a[p],d[p]) by {
        assert(equal(a[p],old[p])); assert(equal(old[p],new[p])); assert(equal(d[p],new[p]));
    }
}
pub proof fn matching_images(b: Behavior<LState>,c: Constants,ta: int,a: Seq<Txn>,td: int,d: Seq<Txn>,k: int,l: int)
    requires connections::safety_spec(b,c),0 <= ta,0 <= td,origins::images(b,c,ta,a),origins::images(b,c,td,d),
        0 <= k < a.len(),0 <= l < d.len(),a[k].zxid == d[l].zxid
    ensures k == l,through(a,d,k)
{
    assert(origins::entry(b,c,ta,a,k)); assert(origins::entry(b,c,td,d,l));
    if a[k].zxid.epoch == 0 { assert(k == 0 && l == 0); }
    else {
        let w=choose |w: (int,int)| origins::origin(b,c,ta,a,k,w);
        let v=choose |v: (int,int)| origins::origin(b,c,td,d,l,v);
        super::zab_elections::unique(b,c,w.0,w.1,v.0,v.1);
        if w.0 <= v.0 {
            leader::same_epoch(b,c,w.1,w.0,v.0); logs::at(b,c,v.0); logs::facts(b[v.0],c,w.1,w.1);
            common_prefix(a,d,b[w.0].nodes[w.1].history,b[v.0].nodes[w.1].history,k,l);
        } else {
            leader::same_epoch(b,c,w.1,v.0,w.0); logs::at(b,c,w.0); logs::facts(b[w.0],c,w.1,w.1);
            common_prefix(d,a,b[v.0].nodes[w.1].history,b[w.0].nodes[w.1].history,l,k);
            assert forall |p: int| 0 <= p <= k implies #[trigger] equal(a[p],d[p]) by { assert(equal(d[p],a[p])); }
        }
    }
}
pub proof fn historical_matching(b: Behavior<LState>,c: Constants,ti: int,i: int,tj: int,j: int,k: int,l: int)
    requires connections::safety_spec(b,c),ti >= 0,tj >= 0,c.servers.contains(i),c.servers.contains(j),
        0 <= k < b[ti].nodes[i].history.len(),0 <= l < b[tj].nodes[j].history.len(),
        b[ti].nodes[i].history[k].zxid == b[tj].nodes[j].history[l].zxid
    ensures k == l,through(b[ti].nodes[i].history,b[tj].nodes[j].history,k)
{
    origins::at(b,c,ti); origins::at(b,c,tj); origins::facts(b,c,ti,i,i); origins::facts(b,c,tj,j,j);
    matching_images(b,c,ti,b[ti].nodes[i].history,tj,b[tj].nodes[j].history,k,l);
}
} // verus!
