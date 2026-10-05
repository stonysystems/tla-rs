//! Requests and started snapshots use the transaction's immutable router timestamp.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_router_time as router_time;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures };
pub open spec fn started(x: Transaction) -> bool { x.snapshot.active || x.snapshot.committed || x.snapshot.aborted || x.snapshot.prepared }
pub open spec fn request_ok(s: LState,c: Constants,i: int,t: int,e: Request) -> bool {
    match e {
        Request::Op { key,shard,read_ts,.. } => c.keys.contains(key) && shard == i && s.catalog[key] == i && router_time::owns(s,c,t,read_ts),
        Request::Coordinate { .. } => true,
    }
}
pub open spec fn node(s: LState,c: Constants,i: int,t: int) -> bool {
    (started(s.shards[i].txns[t]) ==> router_time::owns(s,c,t,s.shards[i].txns[t].snapshot.ts))
    && forall |e: Request| s.shards[i].txns[t].requests.contains(e) ==> #[trigger] request_ok(s,c,i,t,e)
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) ==> #[trigger] node(s,c,i,t)
}
pub proof fn request_retained(s: LState,c: Constants,a: Action,i: int,t: int,e: Request)
    requires support::shape(s,c),enabled(s,c,a),request_ok(s,c,i,t,e)
    ensures request_ok(apply(s,c,a),c,i,t,e)
{
    if let Request::Op { read_ts,.. }=e { router_time::owns_retained(s,c,a,t,read_ts); }
    reveal(apply);
}
pub proof fn initial_safe(c: Constants,catalog: IMap<int,int>)
    ensures safe(initial(c,catalog),c)
{
    let s=initial(c,catalog);
    assert forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) implies #[trigger] node(s,c,i,t) by {}
}
pub proof fn requests(s: LState,c: Constants,a: Action,i: int,t: int,e: Request)
    requires support::shape(s,c),safe(s,c),enabled(s,c,a),c.shards.contains(i),c.txns.contains(t),apply(s,c,a).shards[i].txns[t].requests.contains(e)
    ensures request_ok(apply(s,c,a),c,i,t,e)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply); assert(node(s,c,i,t));
    if s.shards[i].txns[t].requests.contains(e) { assert(request_ok(s,c,i,t,e)); request_retained(s,c,a,i,t,e); }
    else {
        let j=choose |j: int| 0 <= j < u.shards[i].txns[t].requests.len() && u.shards[i].txns[t].requests[j] == e;
        match a {
            Action::RouterOp { r,i: shard,t: txn,k,op } => {
                if shard == i && txn == t {
                    assert(router_time::selected(s,c,r,t)); router_time::selected_retained(s,c,a,r,t);
                    assert(e == u.shards[i].txns[t].requests.last());
                    assert(router_time::owns(u,c,t,s.routers[r][t].read_ts));
                } else { assert(s.shards[i].txns[t].requests[j] == e); assert(false); }
            },
            Action::RouterCoordinate { r,i: shard,t: txn } => {
                if shard == i && txn == t { assert(e is Coordinate); }
                else { assert(s.shards[i].txns[t].requests[j] == e); assert(false); }
            },
            Action::Read(shard,txn,_) | Action::Write(shard,txn,_) | Action::Coordinate(shard,txn) => {
                if shard == i && txn == t { assert(s.shards[i].txns[t].requests[j+1] == e); }
                else { assert(s.shards[i].txns[t].requests[j] == e); }
                assert(s.shards[i].txns[t].requests.contains(e)); assert(false);
            },
            _ => { assert(s.shards[i].txns[t].requests[j] == e); assert(false); },
        }
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply);
    assert forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) implies #[trigger] node(u,c,i,t) by {
        assert(node(s,c,i,t));
        assert forall |e: Request| u.shards[i].txns[t].requests.contains(e) implies #[trigger] request_ok(u,c,i,t,e) by { requests(s,c,a,i,t,e); }
        if started(u.shards[i].txns[t]) {
            if a == Action::Start(i,t) {
                let e=s.shards[i].txns[t].requests[0]; assert(s.shards[i].txns[t].requests.contains(e)); assert(request_ok(s,c,i,t,e));
                if let Request::Op { read_ts,.. }=e { router_time::owns_retained(s,c,a,t,read_ts); }
            } else {
                assert(started(s.shards[i].txns[t])); assert(u.shards[i].txns[t].snapshot.ts == s.shards[i].txns[t].snapshot.ts);
                router_time::owns_retained(s,c,a,t,s.shards[i].txns[t].snapshot.ts);
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
pub proof fn snapshot_time(b: Behavior<LState>,c: Constants,time: int,i: int,t: int)
    requires support::safety_spec(b,c),time >= 0,c.shards.contains(i),c.txns.contains(t),started(b[time].shards[i].txns[t])
    ensures c.timestamps.contains(b[time].shards[i].txns[t].snapshot.ts),b[time].shards[i].txns[t].snapshot.ts >= 0,
        b[time].shards[i].txns[t].snapshot.ts != c.no_value
{
    at(b,c,time); router_time::at(b,c,time); assert(node(b[time],c,i,t)); router_time::valid_time(b[time],c,t,b[time].shards[i].txns[t].snapshot.ts);
}
pub proof fn same_snapshot_time(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,t: int)
    requires support::safety_spec(b,c),time >= 0,c.shards.contains(i),c.shards.contains(j),c.txns.contains(t),
        started(b[time].shards[i].txns[t]),started(b[time].shards[j].txns[t])
    ensures b[time].shards[i].txns[t].snapshot.ts == b[time].shards[j].txns[t].snapshot.ts
{
    at(b,c,time); router_time::at(b,c,time); assert(node(b[time],c,i,t)); assert(node(b[time],c,j,t));
    router_time::same_time(b[time],c,t,b[time].shards[i].txns[t].snapshot.ts,b[time].shards[j].txns[t].snapshot.ts);
}
} // verus!
