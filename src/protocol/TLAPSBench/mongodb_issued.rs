//! Every pending and executed operation is represented in the router's participant kinds.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_router_time as time;
use super::mongodb_participants as parts;
use super::mongodb_operations as operations;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn cert(s: LState,c: Constants,t: int,i: int,kind: Kind) -> bool {
    parts::selected(s,c,t) && parts::issued(parts::txn(s,c,t).participants,i,kind)
}
pub open spec fn request(s: LState,c: Constants,t: int,i: int,e: Request) -> bool {
    match e { Request::Op { kind,.. } => cert(s,c,t,i,kind),_ => true }
}
pub open spec fn node(s: LState,c: Constants,i: int,t: int) -> bool {
    (forall |e: Request| s.shards[i].txns[t].requests.contains(e) ==> #[trigger] request(s,c,t,i,e))
    && forall |p: int| 0 <= p < s.shards[i].txns[t].ops.len() ==> #[trigger] cert(s,c,t,i,s.shards[i].txns[t].ops[p].kind)
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) ==> #[trigger] node(s,c,i,t)
}
pub proof fn retained(s: LState,c: Constants,a: Action,t: int,i: int,kind: Kind)
    requires support::shape(s,c),time::safe(s,c),parts::safe(s,c),enabled(s,c,a),cert(s,c,t,i,kind)
    ensures cert(apply(s,c,a),c,t,i,kind)
{
    parts::issued_retained(s,c,a,t,i,kind);
}
pub proof fn initial_safe(c: Constants,catalog: IMap<int,int>)
    ensures safe(initial(c,catalog),c)
{
    let s=initial(c,catalog); assert forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) implies #[trigger] node(s,c,i,t) by {}
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),time::safe(s,c),parts::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply);
    assert forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) implies #[trigger] node(u,c,i,t) by {
        assert(node(s,c,i,t));
        assert forall |e: Request| u.shards[i].txns[t].requests.contains(e) implies #[trigger] request(u,c,t,i,e) by {
            if s.shards[i].txns[t].requests.contains(e) {
                assert(request(s,c,t,i,e)); if let Request::Op { kind,.. }=e { retained(s,c,a,t,i,kind); }
            } else {
                let p=choose |p: int| 0 <= p < u.shards[i].txns[t].requests.len() && u.shards[i].txns[t].requests[p] == e;
                match a {
                    Action::RouterOp { r,i: ai,t: at,k,op } => {
                        if i == ai && t == at {
                            parts::owner_is(s,c,r,t); parts::owner_fixed(s,c,a,t);
                            assert(parts::router(s,c,r,t)); parts::update(s.routers[r][t].participants,c,i,op);
                            assert(e == u.shards[i].txns[t].requests.last());
                        } else { assert(s.shards[i].txns[t].requests[p] == e); assert(false); }
                    },
                    Action::RouterCoordinate { r,i: ai,t: at } => { if i == ai && t == at { assert(e is Coordinate); } else { assert(s.shards[i].txns[t].requests[p] == e); assert(false); } },
                    Action::Read(ai,at,_) | Action::Write(ai,at,_) | Action::Coordinate(ai,at) => {
                        if i == ai && t == at { assert(s.shards[i].txns[t].requests[p+1] == e); }
                        else { assert(s.shards[i].txns[t].requests[p] == e); }
                        assert(s.shards[i].txns[t].requests.contains(e)); assert(false);
                    },
                    _ => { assert(s.shards[i].txns[t].requests[p] == e); assert(false); },
                }
            }
        }
        assert forall |p: int| 0 <= p < u.shards[i].txns[t].ops.len() implies #[trigger] cert(u,c,t,i,u.shards[i].txns[t].ops[p].kind) by {
            if p < s.shards[i].txns[t].ops.len() {
                assert(u.shards[i].txns[t].ops[p] == s.shards[i].txns[t].ops[p]);
                assert(cert(s,c,t,i,s.shards[i].txns[t].ops[p].kind)); retained(s,c,a,t,i,s.shards[i].txns[t].ops[p].kind);
            } else {
                match a {
                    Action::Read(ai,at,_) | Action::Write(ai,at,_) => {
                        assert(ai == i && at == t); let e=s.shards[i].txns[t].requests[0];
                        assert(s.shards[i].txns[t].requests.contains(e)); assert(request(s,c,t,i,e));
                        if let Request::Op { kind,.. }=e { retained(s,c,a,t,i,kind); }
                    },
                    _ => { assert(false); },
                }
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
    else { at(b,c,tick-1); support::at(b,c,tick-1); time::at(b,c,tick-1); parts::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
pub open spec fn read_only(s: LState,c: Constants,t: int) -> bool {
    parts::selected(s,c,t) && forall |p: int| 0 <= p < parts::txn(s,c,t).participants.len() ==> (#[trigger] parts::txn(s,c,t).participants[p]).kinds == set![Kind::Read]
}
pub proof fn no_writes(s: LState,c: Constants,t: int,i: int)
    requires support::shape(s,c),safe(s,c),c.txns.contains(t),c.shards.contains(i),read_only(s,c,t)
    ensures write_keys(s.shards[i].txns[t].ops).is_empty()
{
    assert(node(s,c,i,t));
    assert forall |k: int| !write_keys(s.shards[i].txns[t].ops).contains(k) by {
        operations::write_member(s.shards[i].txns[t].ops,k);
        if write_keys(s.shards[i].txns[t].ops).contains(k) {
            let p=choose |p: int| 0 <= p < s.shards[i].txns[t].ops.len() && (#[trigger] s.shards[i].txns[t].ops[p]).kind == Kind::Write && s.shards[i].txns[t].ops[p].key == k;
            assert(cert(s,c,t,i,Kind::Write));
            let q=parts::txn(s,c,t).participants; let j=choose |j: int| 0 <= j < q.len() && (#[trigger] q[j]).shard == i && q[j].kinds.contains(Kind::Write);
            assert(q[j].kinds == set![Kind::Read]); assert(false);
        }
    }
}
} // verus!
