//! Prepare and commit records match transaction flags and occur after the read timestamp.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_maximum as maxima;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures };
pub open spec fn recorded(log: Seq<LogEntry>,t: int,prepare: bool) -> bool {
    exists |p: int| 0 <= p < log.len() && (#[trigger] log[p]).txn == t && log[p].prepare == prepare
}
pub proof fn append_record(log: Seq<LogEntry>,e: LogEntry,t: int,prepare: bool)
    ensures recorded(log.push(e),t,prepare) <==> recorded(log,t,prepare) || e.txn == t && e.prepare == prepare
{
    if recorded(log.push(e),t,prepare) {
        let p=choose |p: int| 0 <= p < log.push(e).len() && (#[trigger] log.push(e)[p]).txn == t && log.push(e)[p].prepare == prepare;
        if p < log.len() { assert(log.push(e)[p] == log[p]); }
    }
    if recorded(log,t,prepare) {
        let p=choose |p: int| 0 <= p < log.len() && (#[trigger] log[p]).txn == t && log[p].prepare == prepare;
        assert(log.push(e)[p] == log[p]);
    }
    assert(log.push(e)[log.len() as int] == e);
}
pub open spec fn node(n: LShard,t: int) -> bool {
    let x=n.txns[t]; let snap=x.snapshot;
    (snap.committed ==> !snap.active && !snap.aborted && !x.aborted)
    && (x.aborted ==> snap.aborted && !snap.active)
    && (snap.prepared ==> snap.prepare_ts > snap.ts)
    && (snap.committed <==> recorded(n.log,t,false)) && (snap.prepared <==> recorded(n.log,t,true))
    && forall |p: int| 0 <= p < n.log.len() && (#[trigger] n.log[p]).txn == t ==>
        if n.log[p].prepare { n.log[p].ts == snap.prepare_ts } else { n.log[p].ts > snap.ts }
}
pub open spec fn row(s: LState,c: Constants,i: int) -> bool {
    let n=s.shards[i];
    (forall |t: int| c.txns.contains(t) ==> #[trigger] node(n,t))
    && (forall |p: int| 0 <= p < n.log.len() ==> c.txns.contains((#[trigger] n.log[p]).txn) && n.log[p].ts > 0)
    && forall |p: int,q: int| 0 <= p < q < n.log.len() ==> (#[trigger] n.log[p]).txn != (#[trigger] n.log[q]).txn || n.log[p].prepare != n.log[q].prepare
}
pub open spec fn safe(s: LState,c: Constants) -> bool { forall |i: int| c.shards.contains(i) ==> #[trigger] row(s,c,i) }
pub proof fn prepare_bound(s: LState,c: Constants,m: Prepare)
    requires support::shape(s,c),enabled(s,c,Action::Prepare(m))
    ensures next_ts(s.shards[m.shard],c) > s.shards[m.shard].txns[m.txn].snapshot.ts
{
    reveal(enabled); maxima::next_above(s,c,m.shard,m.txn); maxima::active_member(s.shards[m.shard],c,m.txn);
    assert(active_read_ts(s.shards[m.shard],c).contains(s.shards[m.shard].txns[m.txn].snapshot.ts));
}
pub proof fn commit_bound(s: LState,c: Constants,m: Commit)
    requires support::shape(s,c),safe(s,c),enabled(s,c,Action::Commit(m))
    ensures (if m.ts == c.no_value { next_ts(s.shards[m.shard],c) } else { m.ts }) > s.shards[m.shard].txns[m.txn].snapshot.ts
{
    reveal(enabled); assert(support::shard(s,c,m.shard)); assert(row(s,c,m.shard)); assert(node(s.shards[m.shard],m.txn));
    if m.ts == c.no_value {
        maxima::next_above(s,c,m.shard,m.txn); maxima::active_member(s.shards[m.shard],c,m.txn);
        assert(active_read_ts(s.shards[m.shard],c).contains(s.shards[m.shard].txns[m.txn].snapshot.ts));
        assert(log_ts(s.shards[m.shard]).union(active_read_ts(s.shards[m.shard],c)).contains(s.shards[m.shard].txns[m.txn].snapshot.ts));
    }
}
pub proof fn initial_safe(c: Constants,catalog: IMap<int,int>)
    ensures safe(initial(c,catalog),c)
{
    let s=initial(c,catalog);
    assert forall |i: int| c.shards.contains(i) implies #[trigger] row(s,c,i) by {
        assert forall |t: int| c.txns.contains(t) implies #[trigger] node(s.shards[i],t) by {}
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply);
    match a { Action::Prepare(m) => { prepare_bound(s,c,m); },Action::Commit(m) => { commit_bound(s,c,m); },_ => {} }
    assert forall |i: int| c.shards.contains(i) implies #[trigger] row(u,c,i) by {
        assert(row(s,c,i));
        assert forall |t: int| c.txns.contains(t) implies #[trigger] node(u.shards[i],t) by {
            assert(node(s.shards[i],t));
            match a {
                Action::Prepare(m) => {
                    if i == m.shard {
                        let e=u.shards[i].log.last(); assert(u.shards[i].log == s.shards[i].log.push(e));
                        append_record(s.shards[i].log,e,t,true); append_record(s.shards[i].log,e,t,false);
                    }
                },
                Action::Commit(m) => {
                    if i == m.shard {
                        let e=u.shards[i].log.last(); assert(u.shards[i].log == s.shards[i].log.push(e));
                        append_record(s.shards[i].log,e,t,true); append_record(s.shards[i].log,e,t,false);
                    }
                },
                Action::Start(j,w) => { if i == j && t == w { assert(!recorded(s.shards[i].log,t,true)); assert(!recorded(s.shards[i].log,t,false)); } },
                _ => {},
            }
            assert forall |p: int| 0 <= p < u.shards[i].log.len() && (#[trigger] u.shards[i].log[p]).txn == t
                implies if u.shards[i].log[p].prepare { u.shards[i].log[p].ts == u.shards[i].txns[t].snapshot.prepare_ts } else { u.shards[i].log[p].ts > u.shards[i].txns[t].snapshot.ts } by {
                if p < s.shards[i].log.len() { assert(u.shards[i].log[p] == s.shards[i].log[p]); }
            }
        }
        assert forall |p: int| 0 <= p < u.shards[i].log.len() implies c.txns.contains((#[trigger] u.shards[i].log[p]).txn) && u.shards[i].log[p].ts > 0 by {
            if p < s.shards[i].log.len() { assert(u.shards[i].log[p] == s.shards[i].log[p]); }
        }
        assert forall |p: int,q: int| 0 <= p < q < u.shards[i].log.len() implies (#[trigger] u.shards[i].log[p]).txn != (#[trigger] u.shards[i].log[q]).txn || u.shards[i].log[p].prepare != u.shards[i].log[q].prepare by {
            if q < s.shards[i].log.len() { assert(u.shards[i].log[p] == s.shards[i].log[p]); assert(u.shards[i].log[q] == s.shards[i].log[q]); }
            else {
                assert(u.shards[i].log[p] == s.shards[i].log[p]); let t=u.shards[i].log[q].txn; assert(node(s.shards[i],t));
                if u.shards[i].log[p].txn == t && u.shards[i].log[p].prepare == u.shards[i].log[q].prepare {
                    assert(recorded(s.shards[i].log,t,u.shards[i].log[p].prepare)); assert(false);
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
    if time == 0 { initial_safe(c,b[0].catalog); }
    else { at(b,c,time-1); support::at(b,c,time-1); let a=support::step(b,c,time-1); preserve(b[time-1],c,a); }
}
pub proof fn committed_fixed(s: LState,c: Constants,a: Action,i: int,t: int)
    requires support::shape(s,c),safe(s,c),enabled(s,c,a),c.shards.contains(i),c.txns.contains(t),s.shards[i].txns[t].snapshot.committed
    ensures apply(s,c,a).shards[i].txns[t].snapshot == s.shards[i].txns[t].snapshot,
        apply(s,c,a).shards[i].txns[t].ops == s.shards[i].txns[t].ops
{
    assert(row(s,c,i)); assert(node(s.shards[i],t)); reveal(enabled); reveal(apply);
}
pub proof fn timestamp_fixed(s: LState,c: Constants,a: Action,i: int,t: int)
    requires support::shape(s,c),safe(s,c),enabled(s,c,a),c.shards.contains(i),c.txns.contains(t),super::mongodb_read_time::started(s.shards[i].txns[t])
    ensures apply(s,c,a).shards[i].txns[t].snapshot.ts == s.shards[i].txns[t].snapshot.ts
{
    assert(row(s,c,i)); assert(node(s.shards[i],t)); reveal(enabled); reveal(apply);
    if a == Action::Start(i,t) { assert(!recorded(s.shards[i].log,t,true)); assert(false); }
}
} // verus!
