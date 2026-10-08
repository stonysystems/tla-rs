//! Votes certify immutable prepare timestamps; complete votes determine one transaction timestamp.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_router_time as time;
use super::mongodb_participants as parts;
use super::mongodb_coordination as coord;
use super::mongodb_storage_lifecycle as lifecycle;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures };
pub open spec fn cert(s: LState,c: Constants,t: int,i: int,ts: int) -> bool {
    c.txns.contains(t) && c.shards.contains(i) && coord::frozen(s,c,t) && parts::shards(s,c,t).contains(i)
    && s.shards[i].txns[t].snapshot.prepared && s.shards[i].txns[t].snapshot.prepare_ts == ts
}
pub open spec fn node(s: LState,c: Constants,i: int,t: int) -> bool {
    forall |v: (int,int)| s.shards[i].txns[t].votes.contains(v) ==> #[trigger] cert(s,c,t,v.0,v.1)
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    (forall |m: Vote| s.votes.contains(m) ==> #[trigger] cert(s,c,m.txn,m.shard,m.ts))
    && forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) ==> #[trigger] node(s,c,i,t)
}
pub proof fn prepared_fixed(s: LState,c: Constants,a: Action,i: int,t: int)
    requires support::shape(s,c),lifecycle::safe(s,c),enabled(s,c,a),c.shards.contains(i),c.txns.contains(t),s.shards[i].txns[t].snapshot.prepared
    ensures apply(s,c,a).shards[i].txns[t].snapshot.prepared,
        apply(s,c,a).shards[i].txns[t].snapshot.prepare_ts == s.shards[i].txns[t].snapshot.prepare_ts
{
    assert(lifecycle::row(s,c,i)); assert(lifecycle::node(s.shards[i],t)); reveal(enabled); reveal(apply);
    if a == Action::Start(i,t) { assert(!lifecycle::recorded(s.shards[i].log,t,true)); assert(false); }
}
pub proof fn retained(s: LState,c: Constants,a: Action,t: int,i: int,ts: int)
    requires support::shape(s,c),time::safe(s,c),lifecycle::safe(s,c),enabled(s,c,a),cert(s,c,t,i,ts)
    ensures cert(apply(s,c,a),c,t,i,ts)
{
    coord::retained(s,c,a,t); prepared_fixed(s,c,a,i,t);
}
pub proof fn initial_safe(c: Constants,catalog: IMap<int,int>)
    ensures safe(initial(c,catalog),c)
{
    let s=initial(c,catalog); assert forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) implies #[trigger] node(s,c,i,t) by {}
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),time::safe(s,c),lifecycle::safe(s,c),coord::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    reveal(enabled); reveal(apply); let u=apply(s,c,a);
    assert forall |m: Vote| u.votes.contains(m) implies #[trigger] cert(u,c,m.txn,m.shard,m.ts) by {
        if s.votes.contains(m) { assert(cert(s,c,m.txn,m.shard,m.ts)); retained(s,c,a,m.txn,m.shard,m.ts); }
        else {
            if let Action::Prepare(p)=a {
                assert(m == Vote { shard: p.shard,txn: p.txn,to: p.coordinator,ts: next_ts(s.shards[p.shard],c) });
                assert(coord::prepare(s,c,p)); coord::retained(s,c,a,p.txn);
            } else { assert(false); }
        }
    }
    assert forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) implies #[trigger] node(u,c,i,t) by {
        assert(node(s,c,i,t));
        assert forall |v: (int,int)| u.shards[i].txns[t].votes.contains(v) implies #[trigger] cert(u,c,t,v.0,v.1) by {
            if s.shards[i].txns[t].votes.contains(v) { assert(cert(s,c,t,v.0,v.1)); retained(s,c,a,t,v.0,v.1); }
            else {
                if let Action::RecvVote(j,m)=a {
                    assert(i == j && t == m.txn && v == (m.shard,m.ts)); assert(cert(s,c,t,m.shard,m.ts)); retained(s,c,a,t,m.shard,m.ts);
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
        at(b,c,tick-1); support::at(b,c,tick-1); time::at(b,c,tick-1); coord::at(b,c,tick-1); lifecycle::at(b,c,tick-1);
        let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a);
    }
}
pub open spec fn ready(s: LState,c: Constants,t: int) -> bool {
    c.txns.contains(t) && coord::frozen(s,c,t) && forall |i: int| #![trigger c.shards.contains(i)] parts::shards(s,c,t).contains(i) ==> c.shards.contains(i) && s.shards[i].txns[t].snapshot.prepared
}
pub open spec fn prepare_times(s: LState,c: Constants,t: int) -> ISet<int> {
    parts::shards(s,c,t).to_set().map(|i: int| s.shards[i].txns[t].snapshot.prepare_ts).to_iset()
}
pub open spec fn stamp(s: LState,c: Constants,t: int) -> int { maximum(prepare_times(s,c,t)) }
pub proof fn ready_retained(s: LState,c: Constants,a: Action,t: int)
    requires support::shape(s,c),time::safe(s,c),lifecycle::safe(s,c),enabled(s,c,a),ready(s,c,t)
    ensures ready(apply(s,c,a),c,t),stamp(apply(s,c,a),c,t) == stamp(s,c,t)
{
    let u=apply(s,c,a); coord::retained(s,c,a,t); let q=parts::shards(s,c,t);
    assert forall |i: int| #![trigger q.contains(i)] q.contains(i) implies c.shards.contains(i) && u.shards[i].txns[t].snapshot.prepared && u.shards[i].txns[t].snapshot.prepare_ts == s.shards[i].txns[t].snapshot.prepare_ts by {
        prepared_fixed(s,c,a,i,t);
    }
    assert(prepare_times(u,c,t) =~= prepare_times(s,c,t)) by {
        assert forall |ts: int| prepare_times(u,c,t).contains(ts) implies prepare_times(s,c,t).contains(ts) by {
            let i=choose |i: int| #![trigger q.to_set().contains(i)] q.to_set().contains(i) && u.shards[i].txns[t].snapshot.prepare_ts == ts;
            assert(q.contains(i)); assert(s.shards[i].txns[t].snapshot.prepare_ts == ts);
            q.to_set().lemma_map_contains(|i: int| s.shards[i].txns[t].snapshot.prepare_ts,ts);
        }
        assert forall |ts: int| prepare_times(s,c,t).contains(ts) implies prepare_times(u,c,t).contains(ts) by {
            let i=choose |i: int| #![trigger q.to_set().contains(i)] q.to_set().contains(i) && s.shards[i].txns[t].snapshot.prepare_ts == ts;
            assert(q.contains(i)); assert(u.shards[i].txns[t].snapshot.prepare_ts == ts);
            q.to_set().lemma_map_contains(|i: int| u.shards[i].txns[t].snapshot.prepare_ts,ts);
        }
    }
}
pub proof fn decision(s: LState,c: Constants,i: int,t: int)
    requires support::shape(s,c),coord::safe(s,c),safe(s,c),enabled(s,c,Action::Decide(i,t))
    ensures ready(s,c,t),maximum(s.shards[i].txns[t].votes.map(|v: (int,int)| v.1).to_iset()) == stamp(s,c,t)
{
    coord::deciding(s,c,i,t); reveal(enabled); assert(node(s,c,i,t)); let v=s.shards[i].txns[t].votes; let q=parts::shards(s,c,t);
    assert forall |j: int| #![trigger q.contains(j)] q.contains(j) implies c.shards.contains(j) && s.shards[j].txns[t].snapshot.prepared by {
        assert(q.to_set().contains(j)); assert(v.map(|v: (int,int)| v.0).contains(j));
        let e=choose |e: (int,int)| #![trigger v.contains(e)] v.contains(e) && e.0 == j; assert(cert(s,c,t,j,e.1));
    }
    assert(v.map(|v: (int,int)| v.1).to_iset() =~= prepare_times(s,c,t)) by {
        assert forall |ts: int| v.map(|v: (int,int)| v.1).to_iset().contains(ts) implies prepare_times(s,c,t).contains(ts) by {
            let e=choose |e: (int,int)| #![trigger v.contains(e)] v.contains(e) && e.1 == ts; assert(cert(s,c,t,e.0,e.1));
            assert(q.to_set().contains(e.0)); q.to_set().lemma_map_contains(|j: int| s.shards[j].txns[t].snapshot.prepare_ts,ts);
        }
        assert forall |ts: int| prepare_times(s,c,t).contains(ts) implies v.map(|v: (int,int)| v.1).to_iset().contains(ts) by {
            let j=choose |j: int| #![trigger q.to_set().contains(j)] q.to_set().contains(j) && s.shards[j].txns[t].snapshot.prepare_ts == ts;
            assert(q.contains(j)); assert(v.map(|v: (int,int)| v.0).contains(j)); let e=choose |e: (int,int)| #![trigger v.contains(e)] v.contains(e) && e.0 == j;
            assert(cert(s,c,t,j,e.1)); v.lemma_map_contains(|v: (int,int)| v.1,ts);
        }
    }
}
} // verus!
