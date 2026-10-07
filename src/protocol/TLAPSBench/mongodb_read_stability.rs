//! Later commits cannot change the timestamped value of a key already read.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_maximum as maxima;
use super::mongodb_storage_lifecycle as lifecycle;
use super::mongodb_storage_contents as contents;
use super::mongodb_prepare_barrier as barrier;
use super::mongodb_snapshot_values as values;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub proof fn new_commit_after_read(s: LState,c: Constants,m: Commit,r: int,k: int)
    requires support::shape(s,c),lifecycle::safe(s,c),contents::safe(s,c),barrier::safe(s,c),enabled(s,c,Action::Commit(m)),c.txns.contains(r),
        s.shards[m.shard].txns[r].snapshot.active || s.shards[m.shard].txns[r].snapshot.committed,barrier::read_key(s.shards[m.shard].txns[r].ops,k)
    ensures apply(s,c,Action::Commit(m)).shards[m.shard].log.last().data.dom().contains(k)
        ==> apply(s,c,Action::Commit(m)).shards[m.shard].log.last().ts > s.shards[m.shard].txns[r].snapshot.ts
{
    reveal(enabled); reveal(apply); let n=s.shards[m.shard]; let u=apply(s,c,Action::Commit(m)); let e=u.shards[m.shard].log.last();
    if e.data.dom().contains(k) {
        if m.txn == r { lifecycle::commit_bound(s,c,m); }
        else if m.ts == c.no_value {
            maxima::next_above(s,c,m.shard,m.txn); let q=log_ts(n).union(active_read_ts(n,c));
            if n.txns[r].snapshot.active { maxima::active_member(n,c,r); assert(q.contains(n.txns[r].snapshot.ts)); }
            else {
                assert(lifecycle::row(s,c,m.shard)); assert(lifecycle::node(n,r));
                let p=choose |p: int| 0 <= p < n.log.len() && (#[trigger] n.log[p]).txn == r && !n.log[p].prepare;
                maxima::log_member(n,p); assert(q.contains(n.log[p].ts)); assert(n.log[p].ts > n.txns[r].snapshot.ts);
            }
        } else {
            assert(contents::node(s,c,m.shard,m.txn)); assert(n.txns[m.txn].snapshot.writes.contains(k)); assert(barrier::node(n,c,r));
            assert(n.txns[m.txn].snapshot.prepare_ts > n.txns[r].snapshot.ts);
        }
    }
}
pub proof fn past_read(s: LState,c: Constants,a: Action,i: int,r: int,k: int)
    requires support::shape(s,c),lifecycle::safe(s,c),contents::safe(s,c),barrier::safe(s,c),enabled(s,c,a),c.shards.contains(i),c.txns.contains(r),
        s.shards[i].txns[r].snapshot.active || s.shards[i].txns[r].snapshot.committed,barrier::read_key(s.shards[i].txns[r].ops,k)
    ensures snapshot_read(s.shards[i],c,k,s.shards[i].txns[r].snapshot.ts) == snapshot_read(apply(s,c,a).shards[i],c,k,apply(s,c,a).shards[i].txns[r].snapshot.ts)
{
    reveal(enabled); reveal(apply); let n=s.shards[i]; let d=apply(s,c,a).shards[i]; lifecycle::timestamp_fixed(s,c,a,i,r);
    if n.log == d.log { values::same_log(n,d,c,k,n.txns[r].snapshot.ts); }
    else {
        let e=d.log.last(); assert(d.log == n.log.push(e));
        if let Action::Commit(m)=a { assert(m.shard == i); new_commit_after_read(s,c,m,r,k); }
        assert(!values::eligible(e,k,n.txns[r].snapshot.ts)); values::append_ignored(n,d,c,k,n.txns[r].snapshot.ts,e);
    }
}
} // verus!
