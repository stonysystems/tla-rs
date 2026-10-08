//! Commit records carry either the common two-phase timestamp or a single-shard/read-only decision.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_router_time as time;
use super::mongodb_participants as parts;
use super::mongodb_coordination as coord;
use super::mongodb_votes as votes;
use super::mongodb_issued as issued;
use super::mongodb_storage_lifecycle as lifecycle;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures };
pub open spec fn direct(s: LState,c: Constants,t: int,i: int) -> bool {
    parts::selected(s,c,t) && parts::txn(s,c,t).committing && parts::shards(s,c,t).contains(i)
    && (parts::shards(s,c,t).len() == 1 || issued::read_only(s,c,t))
}
pub open spec fn message(s: LState,c: Constants,m: Commit) -> bool {
    c.txns.contains(m.txn) && c.shards.contains(m.shard) && parts::shards(s,c,m.txn).contains(m.shard)
    && (votes::ready(s,c,m.txn) && m.ts == votes::stamp(s,c,m.txn) || m.ts == c.no_value && direct(s,c,m.txn,m.shard))
}
pub open spec fn record(s: LState,c: Constants,i: int,p: int) -> bool {
    let e=s.shards[i].log[p];
    c.txns.contains(e.txn) && parts::shards(s,c,e.txn).contains(i)
    && (votes::ready(s,c,e.txn) && e.ts == votes::stamp(s,c,e.txn) || direct(s,c,e.txn,i))
}
pub open spec fn row(s: LState,c: Constants,i: int) -> bool {
    forall |p: int| 0 <= p < s.shards[i].log.len() && !s.shards[i].log[p].prepare ==> #[trigger] record(s,c,i,p)
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    (forall |m: Commit| s.commits.contains(m) ==> #[trigger] message(s,c,m))
    && forall |i: int| c.shards.contains(i) ==> #[trigger] row(s,c,i)
}
pub proof fn direct_retained(s: LState,c: Constants,a: Action,t: int,i: int)
    requires support::shape(s,c),time::safe(s,c),enabled(s,c,a),direct(s,c,t,i)
    ensures direct(apply(s,c,a),c,t,i),parts::shards(apply(s,c,a),c,t) == parts::shards(s,c,t)
{
    parts::frozen(s,c,a,t);
}
pub proof fn message_retained(s: LState,c: Constants,a: Action,m: Commit)
    requires support::shape(s,c),time::safe(s,c),lifecycle::safe(s,c),enabled(s,c,a),message(s,c,m)
    ensures message(apply(s,c,a),c,m)
{
    if votes::ready(s,c,m.txn) && m.ts == votes::stamp(s,c,m.txn) { votes::ready_retained(s,c,a,m.txn); coord::retained(s,c,a,m.txn); }
    else { direct_retained(s,c,a,m.txn,m.shard); }
}
pub proof fn initial_safe(c: Constants,catalog: IMap<int,int>)
    ensures safe(initial(c,catalog),c)
{
    let s=initial(c,catalog); assert forall |i: int| c.shards.contains(i) implies #[trigger] row(s,c,i) by {}
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),time::safe(s,c),parts::safe(s,c),coord::safe(s,c),votes::safe(s,c),lifecycle::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply);
    assert forall |m: Commit| u.commits.contains(m) implies #[trigger] message(u,c,m) by {
        if s.commits.contains(m) { assert(message(s,c,m)); message_retained(s,c,a,m); }
        else {
            match a {
                Action::RouterSingle { r,i,t } | Action::RouterReadOnly { r,i,t } => {
                    assert(time::router(s,c,r,t)); assert(time::selected(s,c,r,t)); parts::owner_is(s,c,r,t); parts::owner_fixed(s,c,a,t); assert(parts::router(s,c,r,t));
                    let q=if a is RouterSingle { seq![i] } else { participant_shards(s.routers[r][t].participants) };
                    assert(commit_messages(q,t,c.no_value).contains(m));
                    let j=choose |j: int| #![trigger q.to_set().contains(j)] q.to_set().contains(j) && Commit { shard: j,txn: t,ts: c.no_value } == m;
                    assert(q.contains(j)); let p=choose |p: int| 0 <= p < q.len() && q[p] == j;
                    if a is RouterSingle { assert(j == i); assert(parts::shards(u,c,t) =~= q); }
                    else { assert(c.shards.contains(s.routers[r][t].participants[p].shard)); assert(issued::read_only(u,c,t)); }
                    assert(direct(u,c,t,j));
                },
                Action::Decide(i,t) => {
                    votes::decision(s,c,i,t); votes::ready_retained(s,c,a,t); coord::retained(s,c,a,t); coord::deciding(s,c,i,t);
                    let x=s.shards[i].txns[t]; let ts=maximum(x.votes.map(|v: (int,int)| v.1).to_iset());
                    assert(commit_messages(x.participants,t,ts).contains(m));
                    let j=choose |j: int| #![trigger x.participants.to_set().contains(j)] x.participants.to_set().contains(j) && Commit { shard: j,txn: t,ts } == m;
                    assert(x.participants.contains(j)); assert(parts::shards(s,c,t).contains(j));
                },
                _ => { assert(false); },
            }
        }
    }
    assert forall |i: int| c.shards.contains(i) implies #[trigger] row(u,c,i) by {
        assert(row(s,c,i));
        assert forall |p: int| 0 <= p < u.shards[i].log.len() && !u.shards[i].log[p].prepare implies #[trigger] record(u,c,i,p) by {
            if p < s.shards[i].log.len() {
                assert(u.shards[i].log[p] == s.shards[i].log[p]); assert(record(s,c,i,p)); let e=s.shards[i].log[p];
                if votes::ready(s,c,e.txn) && e.ts == votes::stamp(s,c,e.txn) { votes::ready_retained(s,c,a,e.txn); coord::retained(s,c,a,e.txn); }
                else { direct_retained(s,c,a,e.txn,i); }
            } else {
                if let Action::Commit(m)=a {
                    assert(i == m.shard); assert(p == s.shards[i].log.len()); assert(message(s,c,m)); message_retained(s,c,a,m);
                    if m.ts == c.no_value {
                        if votes::ready(s,c,m.txn) { assert(s.shards[i].txns[m.txn].snapshot.prepared); assert(false); }
                        assert(direct(s,c,m.txn,i)); direct_retained(s,c,a,m.txn,i);
                    } else { votes::ready_retained(s,c,a,m.txn); }
                } else { assert(false); }
            }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c,b[0].catalog); }
    else {
        at(b,c,tick-1); support::at(b,c,tick-1); time::at(b,c,tick-1); parts::at(b,c,tick-1); coord::at(b,c,tick-1); votes::at(b,c,tick-1); lifecycle::at(b,c,tick-1);
        let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a);
    }
}
pub proof fn agree(s: LState,c: Constants,i: int,p: int,j: int,q: int,k: int)
    requires support::shape(s,c),safe(s,c),issued::safe(s,c),lifecycle::safe(s,c),
        c.shards.contains(i),c.shards.contains(j),0 <= p < s.shards[i].log.len(),0 <= q < s.shards[j].log.len(),
        !s.shards[i].log[p].prepare,!s.shards[j].log[q].prepare,s.shards[i].log[p].txn == s.shards[j].log[q].txn,
        write_keys(s.shards[i].txns[s.shards[i].log[p].txn].ops).contains(k)
    ensures s.shards[i].log[p].ts == s.shards[j].log[q].ts
{
    assert(row(s,c,i)); assert(row(s,c,j)); assert(record(s,c,i,p)); assert(record(s,c,j,q)); let t=s.shards[i].log[p].txn;
    if issued::read_only(s,c,t) { issued::no_writes(s,c,t,i); assert(false); }
    if parts::shards(s,c,t).len() == 1 {
        let ps=parts::shards(s,c,t); let pi=choose |pi: int| 0 <= pi < ps.len() && ps[pi] == i; let pj=choose |pj: int| 0 <= pj < ps.len() && ps[pj] == j;
        assert(i == j); assert(lifecycle::row(s,c,i));
        if p < q { assert(s.shards[i].log[p].txn != s.shards[i].log[q].txn || s.shards[i].log[p].prepare != s.shards[i].log[q].prepare); assert(false); }
        if q < p { assert(s.shards[i].log[q].txn != s.shards[i].log[p].txn || s.shards[i].log[q].prepare != s.shards[i].log[p].prepare); assert(false); }
    }
}
} // verus!
