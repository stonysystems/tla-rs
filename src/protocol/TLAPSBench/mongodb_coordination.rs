//! Coordinator requests and prepare messages refer to the router's frozen participant set.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_router_time as time;
use super::mongodb_participants as parts;
use super::mongodb_read_time as reads;
use super::mongodb_storage_lifecycle as lifecycle;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures };
pub open spec fn frozen(s: LState,c: Constants,t: int) -> bool {
    parts::selected(s,c,t) && parts::txn(s,c,t).committing && parts::shards(s,c,t).len() > 1
}
pub open spec fn request(s: LState,c: Constants,t: int,e: Request) -> bool {
    match e { Request::Coordinate { participants,.. } => frozen(s,c,t) && participants == parts::shards(s,c,t),_ => true }
}
pub open spec fn node(s: LState,c: Constants,i: int,t: int) -> bool {
    let x=s.shards[i].txns[t];
    (x.committing ==> reads::started(x) && frozen(s,c,t) && x.participants == parts::shards(s,c,t))
    && (!x.committing ==> x.votes.is_empty())
    && (reads::started(x) ==> x.participants.len() > 0)
    && forall |e: Request| x.requests.contains(e) ==> #[trigger] request(s,c,t,e)
}
pub open spec fn prepare(s: LState,c: Constants,m: Prepare) -> bool {
    c.shards.contains(m.shard) && c.txns.contains(m.txn) && frozen(s,c,m.txn) && parts::shards(s,c,m.txn).contains(m.shard)
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    (forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) ==> #[trigger] node(s,c,i,t))
    && forall |m: Prepare| s.prepares.contains(m) ==> #[trigger] prepare(s,c,m)
}
pub proof fn retained(s: LState,c: Constants,a: Action,t: int)
    requires support::shape(s,c),time::safe(s,c),enabled(s,c,a),frozen(s,c,t)
    ensures frozen(apply(s,c,a),c,t),parts::shards(apply(s,c,a),c,t) == parts::shards(s,c,t)
{
    parts::frozen(s,c,a,t);
}
pub proof fn initial_safe(c: Constants,catalog: IMap<int,int>)
    ensures safe(initial(c,catalog),c)
{
    let s=initial(c,catalog); assert forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) implies #[trigger] node(s,c,i,t) by {}
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),time::safe(s,c),parts::safe(s,c),lifecycle::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply);
    assert forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) implies #[trigger] node(u,c,i,t) by {
        assert(support::shard(s,c,i)); assert(node(s,c,i,t)); let x=s.shards[i].txns[t];
        if x.committing { retained(s,c,a,t); }
        if a == Action::Start(i,t) {
            assert(lifecycle::row(s,c,i)); assert(lifecycle::node(s.shards[i],t)); assert(!lifecycle::recorded(s.shards[i].log,t,true));
            assert(!reads::started(x)); assert(!x.committing);
        }
        if a == Action::Coordinate(i,t) {
            let e=x.requests[0]; assert(x.requests.contains(e)); assert(request(s,c,t,e)); retained(s,c,a,t);
        }
        let y=u.shards[i].txns[t];
        assert(y.committing ==> reads::started(y) && frozen(u,c,t) && y.participants == parts::shards(u,c,t));
        assert(!y.committing ==> y.votes.is_empty());
        assert(reads::started(y) ==> y.participants.len() > 0);
        assert forall |e: Request| u.shards[i].txns[t].requests.contains(e) implies #[trigger] request(u,c,t,e) by {
            if x.requests.contains(e) {
                assert(request(s,c,t,e)); if e is Coordinate { retained(s,c,a,t); }
            } else {
                let p=choose |p: int| 0 <= p < u.shards[i].txns[t].requests.len() && u.shards[i].txns[t].requests[p] == e;
                match a {
                    Action::RouterCoordinate { r,i: ai,t: at } => {
                        if i == ai && t == at {
                            assert(time::router(s,c,r,t)); assert(time::selected(s,c,r,t)); parts::owner_is(s,c,r,t); parts::owner_fixed(s,c,a,t);
                            assert(e == u.shards[i].txns[t].requests.last());
                        } else { assert(x.requests[p] == e); assert(false); }
                    },
                    Action::RouterOp { r,i: ai,t: at,k,op } => { if i == ai && t == at { assert(e is Op); } else { assert(x.requests[p] == e); assert(false); } },
                    Action::Read(ai,at,_) | Action::Write(ai,at,_) | Action::Coordinate(ai,at) => {
                        if i == ai && t == at { assert(x.requests[p+1] == e); } else { assert(x.requests[p] == e); }
                        assert(x.requests.contains(e)); assert(false);
                    },
                    _ => { assert(x.requests[p] == e); assert(false); },
                }
            }
        }
    }
    assert forall |m: Prepare| u.prepares.contains(m) implies #[trigger] prepare(u,c,m) by {
        if s.prepares.contains(m) { assert(prepare(s,c,m)); retained(s,c,a,m.txn); }
        else {
            if let Action::Coordinate(i,t)=a {
                assert(node(s,c,i,t)); let e=s.shards[i].txns[t].requests[0]; assert(s.shards[i].txns[t].requests.contains(e)); assert(request(s,c,t,e));
                if let Request::Coordinate { participants,.. }=e {
                    let images=participants.to_set().map(|p: int| Prepare { shard: p,txn: t,coordinator: i }); assert(images.contains(m));
                    let j=choose |j: int| #![trigger participants.to_set().contains(j)] participants.to_set().contains(j) && Prepare { shard: j,txn: t,coordinator: i } == m;
                    assert(participants.contains(j)); let p=choose |p: int| 0 <= p < participants.len() && participants[p] == j;
                    retained(s,c,a,t); let r=parts::owner(s,c,t); assert(time::selected(s,c,r,t)); assert(parts::router(s,c,r,t));
                    assert(c.shards.contains(parts::txn(s,c,t).participants[p].shard));
                }
            } else { assert(false); }
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
        at(b,c,tick-1); support::at(b,c,tick-1); time::at(b,c,tick-1); parts::at(b,c,tick-1); lifecycle::at(b,c,tick-1);
        let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a);
    }
}
pub proof fn deciding(s: LState,c: Constants,i: int,t: int)
    requires support::shape(s,c),safe(s,c),enabled(s,c,Action::Decide(i,t))
    ensures frozen(s,c,t),s.shards[i].txns[t].committing,s.shards[i].txns[t].participants == parts::shards(s,c,t),!s.shards[i].txns[t].votes.is_empty()
{
    reveal(enabled); assert(node(s,c,i,t)); assert(support::shard(s,c,i)); let x=s.shards[i].txns[t];
    assert(reads::started(x)); assert(x.participants.len() > 0); assert(x.participants.to_set().contains(x.participants[0]));
    if x.votes.is_empty() { assert(x.votes.map(|v: (int,int)| v.0).is_empty()); assert(false); }
}
} // verus!
