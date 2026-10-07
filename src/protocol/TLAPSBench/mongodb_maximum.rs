//! Timestamp maxima are defined because only finitely many snapshots are active.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::set::Set::lemma_map_contains };
pub proof fn finite_max(q: Set<int>) -> (m: int)
    requires !q.is_empty()
    ensures q.contains(m),forall |v: int| q.contains(v) ==> v <= m
    decreases q.len()
{
    let n=choose |n: int| q.contains(n);
    if q.remove(n).is_empty() { n }
    else { let m=finite_max(q.remove(n)); if n > m { n } else { m } }
}
pub proof fn correct(q: ISet<int>)
    requires q.finite(),!q.is_empty()
    ensures q.contains(maximum(q)),forall |v: int| q.contains(v) ==> v <= maximum(q)
{
    reveal(maximum); let s=q.to_set().unwrap(); assert(s.to_iset() =~= q); let m=finite_max(s);
    assert(q.contains(m)); assert forall |v: int| q.contains(v) implies v <= m by { assert(s.contains(v)); }
}
pub proof fn active_finite(s: LState,c: Constants,i: int)
    requires support::shape(s,c),c.shards.contains(i)
    ensures active_read_ts(s.shards[i],c).finite()
{
    assert(support::shard(s,c,i)); let n=s.shards[i]; let q=active_read_ts(n,c);
    let values=n.active.map(|t: int| n.txns[t].snapshot.ts).insert(0).to_iset();
    assert(q.subset_of(values)) by {
        assert forall |v: int| q.contains(v) implies values.contains(v) by {
            let t=choose |t: int| c.txns.contains(t) && (if n.txns[t].snapshot.active { n.txns[t].snapshot.ts } else { 0 }) == v;
            if n.txns[t].snapshot.active { assert(n.active.contains(t)); assert(n.active.map(|t: int| n.txns[t].snapshot.ts).contains(v)); }
        }
    }
    vstd::iset_lib::lemma_iset_subset_finite(values,q);
}
pub proof fn active_member(n: LShard,c: Constants,t: int)
    requires c.txns.contains(t)
    ensures active_read_ts(n,c).contains(if n.txns[t].snapshot.active { n.txns[t].snapshot.ts } else { 0 }),!active_read_ts(n,c).is_empty()
{
    let f=|t: int| if n.txns[t].snapshot.active { n.txns[t].snapshot.ts } else { 0 };
    assert(c.txns.contains(t)); assert(c.txns.map(f).contains(f(t)));
}
pub proof fn next_above(s: LState,c: Constants,i: int,t: int)
    requires support::shape(s,c),c.shards.contains(i),c.txns.contains(t)
    ensures active_read_ts(s.shards[i],c).contains(maximum(active_read_ts(s.shards[i],c))),
        forall |v: int| active_read_ts(s.shards[i],c).contains(v) ==> v <= maximum(active_read_ts(s.shards[i],c)),
        forall |v: int| log_ts(s.shards[i]).union(active_read_ts(s.shards[i],c)).contains(v) ==> v < next_ts(s.shards[i],c)
{
    active_finite(s,c,i); active_member(s.shards[i],c,t); correct(active_read_ts(s.shards[i],c));
    let q=log_ts(s.shards[i]).union(active_read_ts(s.shards[i],c)); assert(q.finite()); assert(!q.is_empty()); correct(q);
}
pub proof fn log_member(n: LShard,p: int)
    requires 0 <= p < n.log.len()
    ensures log_ts(n).contains(n.log[p].ts)
{
    n.log.to_set_ensures(); assert(n.log.to_set().contains(n.log[p]));
    assert(n.log.to_set().map(|e: LogEntry| e.ts).contains(n.log[p].ts));
}
} // verus!
