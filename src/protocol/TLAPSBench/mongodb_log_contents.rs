//! A commit record stores exactly its transaction's local write set and write identifier.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_storage_lifecycle as lifecycle;
use super::mongodb_storage_contents as contents;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn entry(s: LState,c: Constants,i: int,p: int) -> bool {
    let n=s.shards[i]; let e=n.log[p];
    c.txns.contains(e.txn) && e.data.dom().subset_of(c.keys)
    && if e.prepare { e.data.dom().is_empty() } else {
        n.txns[e.txn].snapshot.committed && e.data.dom() == n.txns[e.txn].snapshot.writes.to_iset()
        && forall |k: int| e.data.dom().contains(k) ==> #[trigger] e.data[k] == e.txn
    }
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |i: int,p: int| c.shards.contains(i) && 0 <= p < s.shards[i].log.len() ==> #[trigger] entry(s,c,i,p)
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),lifecycle::safe(s,c),contents::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply);
    assert forall |i: int,p: int| c.shards.contains(i) && 0 <= p < u.shards[i].log.len() implies #[trigger] entry(u,c,i,p) by {
        let e=u.shards[i].log[p];
        if p < s.shards[i].log.len() {
            assert(e == s.shards[i].log[p]); assert(entry(s,c,i,p));
            if !e.prepare { lifecycle::committed_fixed(s,c,a,i,e.txn); }
        } else {
            assert(p == s.shards[i].log.len()); assert(contents::node(s,c,i,e.txn));
            if e.prepare { assert(e.data.dom() =~= ISet::<int>::empty()); }
            else {
                assert(e.data.dom() =~= u.shards[i].txns[e.txn].snapshot.writes.to_iset());
                assert forall |k: int| e.data.dom().contains(k) implies #[trigger] e.data[k] == e.txn by {
                    assert(s.shards[i].txns[e.txn].snapshot.data[k] == e.txn);
                }
            }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures safe(b[time],c)
    decreases time
{
    if time > 0 {
        at(b,c,time-1); support::at(b,c,time-1); lifecycle::at(b,c,time-1); contents::at(b,c,time-1);
        let a=support::step(b,c,time-1); preserve(b[time-1],c,a);
    }
}
pub proof fn commit_data(b: Behavior<LState>,c: Constants,time: int,i: int,p: int)
    requires support::safety_spec(b,c),time >= 0,c.shards.contains(i),0 <= p < b[time].shards[i].log.len(),!b[time].shards[i].log[p].prepare
    ensures b[time].shards[i].log[p].data.dom() == write_keys(b[time].shards[i].txns[b[time].shards[i].log[p].txn].ops).to_iset(),
        forall |k: int| b[time].shards[i].log[p].data.dom().contains(k) ==> #[trigger] b[time].shards[i].log[p].data[k] == b[time].shards[i].log[p].txn
{
    at(b,c,time); contents::at(b,c,time); lifecycle::at(b,c,time); let s=b[time]; let t=s.shards[i].log[p].txn;
    assert(entry(s,c,i,p)); assert(contents::node(s,c,i,t)); assert(lifecycle::row(s,c,i)); assert(lifecycle::node(s.shards[i],t));
}
} // verus!
