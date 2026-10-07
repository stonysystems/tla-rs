//! Sequential execution returns the last observed writer of each key.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_transaction_time as times;
use super::mongodb_operations as operations;
use super::mongodb_write_order as writes;
use super::mongodb_log_contents as logs;
use super::mongodb_snapshot_values as values;
use super::mongodb_order as order;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures };
pub open spec fn last(s: LState,q: Seq<int>,k: int,p: int) -> bool {
    0 <= p < q.len() && write_keys(s.ops[q[p]]).contains(k)
    && forall |j: int| p < j < q.len() ==> !#[trigger] write_keys(s.ops[q[j]]).contains(k)
}
pub open spec fn absent(s: LState,q: Seq<int>,k: int) -> bool {
    forall |p: int| 0 <= p < q.len() ==> !#[trigger] write_keys(s.ops[q[p]]).contains(k)
}
pub proof fn last_value(s: LState,c: Constants,q: Seq<int>,k: int)
    requires times::facts(s,c),c.keys.contains(k),forall |p: int| 0 <= p < q.len() ==> c.txns.contains(#[trigger] q[p])
    ensures execution(s,c,q).dom() == c.keys,
        (absent(s,q,k) && execution(s,c,q)[k] == c.no_value) || exists |p: int| #[trigger] last(s,q,k,p) && execution(s,c,q)[k] == q[p]
    decreases q.len()
{
    reveal(execution);
    if q.len() == 0 { assert(execution(s,c,q).dom() =~= c.keys); }
    else {
        let d=q.drop_last(); assert forall |p: int| 0 <= p < d.len() implies c.txns.contains(#[trigger] d[p]) by { assert(d[p] == q[p]); }
        last_value(s,c,d,k); let t=q.last(); assert(operations::valid(s.ops[t],c,t)); operations::effects_value(execution(s,c,d),s.ops[t],c,t,k);
        if write_keys(s.ops[t]).contains(k) { assert(last(s,q,k,(q.len()-1) as int)); }
        else {
            if absent(s,d,k) {
                assert forall |p: int| 0 <= p < q.len() implies !#[trigger] write_keys(s.ops[q[p]]).contains(k) by {
                    if p < d.len() { assert(d[p] == q[p]); } else { assert(q[p] == t); }
                }
            }
            else {
                let p=choose |p: int| #[trigger] last(s,d,k,p) && execution(s,c,d)[k] == d[p];
                assert(q[p] == d[p]);
                assert forall |j: int| p < j < q.len() implies !#[trigger] write_keys(s.ops[q[j]]).contains(k) by {
                    if j < d.len() { assert(d[j] == q[j]); } else { assert(q[j] == t); }
                }
                assert(last(s,q,k,p));
            }
        }
    }
}
pub proof fn domain(s: LState,c: Constants,q: Seq<int>)
    requires times::facts(s,c),forall |p: int| 0 <= p < q.len() ==> c.txns.contains(#[trigger] q[p])
    ensures execution(s,c,q).dom() == c.keys
    decreases q.len()
{
    if !c.keys.is_empty() { let k=choose |k: int| c.keys.contains(k); last_value(s,c,q,k); }
    else {
        reveal(execution);
        if q.len() > 0 {
            let d=q.drop_last(); assert forall |p: int| 0 <= p < d.len() implies c.txns.contains(#[trigger] d[p]) by { assert(d[p] == q[p]); }
            domain(s,c,d); let t=q.last(); assert(operations::valid(s.ops[t],c,t));
            if s.ops[t].len() > 0 { assert(c.keys.contains(s.ops[t][0].key)); assert(false); }
            reveal(effects);
        } else { assert(execution(s,c,q).dom() =~= c.keys); }
    }
}
pub proof fn write_separation(s: LState,c: Constants,t: int,w: int,k: int)
    requires times::facts(s,c),writes::safe(s,c),c.txns.contains(t),c.txns.contains(w),t != w,
        write_keys(s.ops[t]).contains(k),write_keys(s.ops[w]).contains(k),times::commit_ts(s,c,t) <= times::commit_ts(s,c,w)
    ensures times::commit_ts(s,c,t) <= times::read_ts(s,c,w)
{
    let p=times::global_write(s,c,t,k); let q=times::global_write(s,c,w,k); let i=s.catalog[k];
    times::record_time(s,c,t,i,p); times::record_time(s,c,w,i,q);
    if q < p { writes::increasing(s,c,i,q,p,k); assert(false); }
    assert(p < q); writes::increasing(s,c,i,p,q,k); assert(logs::entry(s,c,i,q)); times::local_read_ts(s,c,i,w);
}
pub proof fn equal_time_same_entry(s: LState,c: Constants,i: int,p: int,q: int,k: int)
    requires times::facts(s,c),writes::safe(s,c),c.shards.contains(i),0 <= p < s.shards[i].log.len(),0 <= q < s.shards[i].log.len(),
        !s.shards[i].log[p].prepare,!s.shards[i].log[q].prepare,s.shards[i].log[p].data.dom().contains(k),s.shards[i].log[q].data.dom().contains(k),
        s.shards[i].log[p].ts == s.shards[i].log[q].ts
    ensures p == q
{
    if p < q { writes::increasing(s,c,i,p,q,k); assert(false); }
    if q < p { writes::increasing(s,c,i,q,p,k); assert(false); }
}
pub proof fn snapshot_value(s: LState,c: Constants,q: Seq<int>,n: int,ts: int,k: int)
    requires times::facts(s,c),writes::safe(s,c),order::valid_order(s,c,q),0 <= n <= q.len(),c.keys.contains(k),
        forall |j: int| 0 <= j < q.len() ==> (j < n <==> order::rank(s,c)(#[trigger] q[j]) <= 2*ts)
    ensures execution(s,c,q.take(n))[k] == snapshot_read(s.shards[s.catalog[k]],c,k,ts)
{
    let prefix=q.take(n); let i=s.catalog[k]; let log=s.shards[i].log; let candidates=values::candidates(log,k,ts);
    assert forall |p: int| 0 <= p < prefix.len() implies c.txns.contains(#[trigger] prefix[p]) by {
        assert(prefix[p] == q[p]); assert(q.to_set().contains(q[p]));
    }
    last_value(s,c,prefix,k);
    if absent(s,prefix,k) {
        assert(candidates.is_empty()) by {
            if !candidates.is_empty() {
                let p=choose |p: int| candidates.contains(p); times::record_write(s,c,i,p,k); let t=log[p].txn;
                assert(s.ops[t].len() > 0) by { operations::write_member(s.ops[t],k); }
                assert(q.to_set().contains(t)); let j=choose |j: int| 0 <= j < q.len() && q[j] == t;
                assert(order::rank(s,c)(q[j]) <= 2*ts); assert(j < n); assert(prefix[j] == t); assert(false);
            }
        }
        assert(Set::range(0,log.len() as int).filter(|p: int| !log[p].prepare && log[p].data.dom().contains(k) && log[p].ts <= ts) =~= candidates);
    } else {
        let j=choose |j: int| #[trigger] last(s,prefix,k,j) && execution(s,c,prefix)[k] == prefix[j]; let t=prefix[j];
        let p=times::global_write(s,c,t,k); times::record_time(s,c,t,i,p); assert(q[j] == t);
        assert(order::rank(s,c)(q[j]) <= 2*ts); assert(log[p].ts <= ts); assert(candidates.contains(p)); assert(!candidates.is_empty());
        values::selection(s.shards[i],c,k,ts); values::latest(s,c,i,k,ts); let m=maximum(candidates.to_iset()); let w=log[m].txn;
        times::record_write(s,c,i,m,k); assert(s.ops[w].len() > 0) by { operations::write_member(s.ops[w],k); }
        assert(q.to_set().contains(w)); let h=choose |h: int| 0 <= h < q.len() && q[h] == w;
        assert(order::rank(s,c)(q[h]) <= 2*ts); assert(h < n); assert(prefix[h] == w);
        if j < h { assert(!write_keys(s.ops[prefix[h]]).contains(k)); assert(false); }
        assert(h <= j); if h < j { assert(order::rank(s,c)(q[h]) <= order::rank(s,c)(q[j])); }
        assert(log[m].ts <= log[p].ts); assert(values::eligible(log[p],k,ts)); assert(log[p].ts <= log[m].ts);
        equal_time_same_entry(s,c,i,p,m,k); assert(log[m].txn == t);
    }
}
} // verus!
