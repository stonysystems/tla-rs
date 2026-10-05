//! Local write sets and values agree with successful operations on the shard's keys.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_read_time as read_time;
use super::mongodb_storage_lifecycle as lifecycle;
use super::mongodb_operations as operations;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub open spec fn node(s: LState,c: Constants,i: int,t: int) -> bool {
    let x=s.shards[i].txns[t]; let snap=x.snapshot;
    snap.data.dom() == c.keys && snap.writes.to_iset().subset_of(c.keys)
    && (forall |k: int| snap.writes.contains(k) ==> #[trigger] snap.data[k] == t)
    && (!snap.aborted ==> snap.writes == write_keys(x.ops))
    && (!read_time::started(x) ==> x.ops.len() == 0)
    && operations::valid(x.ops,c,t) && operations::owned(x.ops,s.catalog,i)
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) ==> #[trigger] node(s,c,i,t)
}
pub proof fn initial_safe(c: Constants,catalog: IMap<int,int>)
    ensures safe(initial(c,catalog),c)
{
    let s=initial(c,catalog);
    assert forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) implies #[trigger] node(s,c,i,t) by {
        assert(s.shards[i].txns[t].snapshot.data.dom() =~= c.keys); assert(Seq::<Operation>::empty().to_set() =~= Set::<Operation>::empty());
        assert(write_keys(Seq::empty()) =~= Set::<int>::empty());
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),read_time::safe(s,c),lifecycle::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply);
    match a {
        Action::Read(i,t,k) | Action::Write(i,t,k) => {
            assert(read_time::node(s,c,i,t)); let e=s.shards[i].txns[t].requests[0];
            assert(s.shards[i].txns[t].requests.contains(e)); assert(read_time::request_ok(s,c,i,t,e)); assert(s.catalog[k] == i);
        },
        _ => {},
    }
    assert forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) implies #[trigger] node(u,c,i,t) by {
        assert(node(s,c,i,t)); assert(lifecycle::row(s,c,i)); assert(lifecycle::node(s.shards[i],t));
        match a {
            Action::Start(j,w) => {
                if i == j && t == w {
                    assert(!lifecycle::recorded(s.shards[i].log,t,true)); assert(!read_time::started(s.shards[i].txns[t]));
                    assert(write_keys(s.shards[i].txns[t].ops) =~= Set::<int>::empty());
                }
            },
            Action::Read(j,w,k) => { if i == j && t == w { operations::writes_append(s.shards[i].txns[t].ops,Operation { kind: Kind::Read,key: k,value: txn_read(s.shards[i],c,t,k) }); } },
            Action::Write(j,w,k) => { if i == j && t == w { operations::writes_append(s.shards[i].txns[t].ops,Operation { kind: Kind::Write,key: k,value: t }); } },
            _ => {},
        }
        assert(u.shards[i].txns[t].snapshot.data.dom() =~= c.keys);
        assert forall |k: int| u.shards[i].txns[t].snapshot.writes.contains(k) implies #[trigger] u.shards[i].txns[t].snapshot.data[k] == t by {
            if s.shards[i].txns[t].snapshot.writes.contains(k) { assert(s.shards[i].txns[t].snapshot.data[k] == t); }
        }
        assert(operations::valid(u.shards[i].txns[t].ops,c,t)) by {
            assert forall |p: int| 0 <= p < u.shards[i].txns[t].ops.len() implies c.keys.contains((#[trigger] u.shards[i].txns[t].ops[p]).key)
                && (c.txns.contains(u.shards[i].txns[t].ops[p].value) || u.shards[i].txns[t].ops[p].value == c.no_value)
                && (u.shards[i].txns[t].ops[p].kind == Kind::Write ==> u.shards[i].txns[t].ops[p].value == t) by {
                if p < s.shards[i].txns[t].ops.len() { assert(u.shards[i].txns[t].ops[p] == s.shards[i].txns[t].ops[p]); }
            }
        }
        assert(operations::owned(u.shards[i].txns[t].ops,u.catalog,i)) by {
            assert forall |p: int| 0 <= p < u.shards[i].txns[t].ops.len() implies #[trigger] u.catalog[u.shards[i].txns[t].ops[p].key] == i by {
                if p < s.shards[i].txns[t].ops.len() { assert(u.shards[i].txns[t].ops[p] == s.shards[i].txns[t].ops[p]); }
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
    else {
        at(b,c,time-1); support::at(b,c,time-1); read_time::at(b,c,time-1); lifecycle::at(b,c,time-1);
        let a=support::step(b,c,time-1); preserve(b[time-1],c,a);
    }
}
} // verus!
