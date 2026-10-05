//! Snapshot lookup selects a real last eligible commit record and ignores ineligible appends.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_maximum as maxima;
use super::mongodb_storage_lifecycle as lifecycle;
use super::mongodb_log_contents as contents;
use super::mongodb_write_order as order;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn eligible(e: LogEntry,k: int,ts: int) -> bool { !e.prepare && e.data.dom().contains(k) && e.ts <= ts }
pub open spec fn candidates(log: Seq<LogEntry>,k: int,ts: int) -> Set<int> { Set::range(0,log.len() as int).filter(|p: int| eligible(log[p],k,ts)) }
pub proof fn selection(n: LShard,c: Constants,k: int,ts: int)
    requires !candidates(n.log,k,ts).is_empty()
    ensures 0 <= maximum(candidates(n.log,k,ts).to_iset()) < n.log.len(),eligible(n.log[maximum(candidates(n.log,k,ts).to_iset())],k,ts),
        snapshot_read(n,c,k,ts) == n.log[maximum(candidates(n.log,k,ts).to_iset())].data[k],
        forall |p: int| candidates(n.log,k,ts).contains(p) ==> p <= maximum(candidates(n.log,k,ts).to_iset())
{
    let q=candidates(n.log,k,ts); maxima::correct(q.to_iset());
    assert(Set::range(0,n.log.len() as int).filter(|p: int| !n.log[p].prepare && n.log[p].data.dom().contains(k) && n.log[p].ts <= ts) =~= q);
}
pub proof fn append_ignored(n: LShard,d: LShard,c: Constants,k: int,ts: int,e: LogEntry)
    requires d.log == n.log.push(e),!eligible(e,k,ts)
    ensures snapshot_read(d,c,k,ts) == snapshot_read(n,c,k,ts)
{
    let q=candidates(n.log,k,ts); let after=candidates(d.log,k,ts);
    assert(after =~= q) by {
        assert forall |p: int| after.contains(p) <==> q.contains(p) by { if 0 <= p < n.log.len() { assert(d.log[p] == n.log[p]); } }
    }
    if q.is_empty() {
        assert(Set::range(0,n.log.len() as int).filter(|p: int| !n.log[p].prepare && n.log[p].data.dom().contains(k) && n.log[p].ts <= ts) =~= q);
        assert(Set::range(0,d.log.len() as int).filter(|p: int| !d.log[p].prepare && d.log[p].data.dom().contains(k) && d.log[p].ts <= ts) =~= q);
    } else {
        selection(n,c,k,ts); selection(d,c,k,ts); let p=maximum(q.to_iset()); assert(d.log[p] == n.log[p]);
    }
}
pub proof fn same_log(n: LShard,d: LShard,c: Constants,k: int,ts: int)
    requires n.log == d.log
    ensures snapshot_read(n,c,k,ts) == snapshot_read(d,c,k,ts)
{
    let q=candidates(n.log,k,ts);
    if q.is_empty() {
        assert(Set::range(0,n.log.len() as int).filter(|p: int| !n.log[p].prepare && n.log[p].data.dom().contains(k) && n.log[p].ts <= ts) =~= q);
        assert(Set::range(0,d.log.len() as int).filter(|p: int| !d.log[p].prepare && d.log[p].data.dom().contains(k) && d.log[p].ts <= ts) =~= q);
    } else { selection(n,c,k,ts); selection(d,c,k,ts); }
}
pub proof fn latest(s: LState,c: Constants,i: int,k: int,ts: int)
    requires lifecycle::safe(s,c),contents::safe(s,c),order::safe(s,c),c.shards.contains(i),!candidates(s.shards[i].log,k,ts).is_empty()
    ensures {
        let p=maximum(candidates(s.shards[i].log,k,ts).to_iset()); let n=s.shards[i];
        snapshot_read(n,c,k,ts) == n.log[p].txn && c.txns.contains(n.log[p].txn) && eligible(n.log[p],k,ts)
        && forall |q: int| 0 <= q < n.log.len() && eligible(#[trigger] n.log[q],k,ts) ==> n.log[q].ts <= n.log[p].ts
    },
{
    let n=s.shards[i]; selection(n,c,k,ts); let p=maximum(candidates(n.log,k,ts).to_iset()); assert(contents::entry(s,c,i,p));
    assert forall |q: int| 0 <= q < n.log.len() && eligible(#[trigger] n.log[q],k,ts) implies n.log[q].ts <= n.log[p].ts by {
        assert(candidates(n.log,k,ts).contains(q)); if q < p { order::increasing(s,c,i,q,p,k); }
    }
}
} // verus!
