//! A global writer has one commit timestamp, strictly after its common read timestamp.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_router_time as time;
use super::mongodb_read_time as reads;
use super::mongodb_participants as parts;
use super::mongodb_commit_time as commits;
use super::mongodb_issued as issued;
use super::mongodb_projection as projection;
use super::mongodb_operations as operations;
use super::mongodb_observed as observed;
use super::mongodb_storage_lifecycle as lifecycle;
use super::mongodb_storage_contents as contents;
use super::mongodb_log_contents as logs;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn facts(s: LState,c: Constants) -> bool {
    support::shape(s,c) && time::safe(s,c) && reads::safe(s,c) && commits::safe(s,c) && issued::safe(s,c) && projection::safe(s,c)
    && observed::safe(s,c) && lifecycle::safe(s,c) && contents::safe(s,c) && logs::safe(s,c)
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures facts(b[tick],c)
{
    support::at(b,c,tick); time::at(b,c,tick); reads::at(b,c,tick); commits::at(b,c,tick); issued::at(b,c,tick);
    projection::at(b,c,tick); observed::at(b,c,tick); lifecycle::at(b,c,tick); contents::at(b,c,tick); logs::at(b,c,tick);
}
pub open spec fn read_ts(s: LState,c: Constants,t: int) -> int { parts::txn(s,c,t).read_ts }
pub open spec fn writer(s: LState,t: int) -> bool { !write_keys(s.ops[t]).is_empty() }
pub open spec fn witness(s: LState,c: Constants,t: int,i: int,p: int) -> bool {
    c.shards.contains(i) && 0 <= p < s.shards[i].log.len() && !s.shards[i].log[p].prepare && s.shards[i].log[p].txn == t
    && !s.shards[i].log[p].data.dom().is_empty()
}
pub open spec fn representative(s: LState,c: Constants,t: int) -> (int,int) {
    choose |x: (int,int)| #[trigger] witness(s,c,t,x.0,x.1)
}
pub open spec fn commit_ts(s: LState,c: Constants,t: int) -> int {
    let x=representative(s,c,t); s.shards[x.0].log[x.1].ts
}
pub proof fn local_read_ts(s: LState,c: Constants,i: int,t: int)
    requires support::shape(s,c),time::safe(s,c),reads::safe(s,c),c.shards.contains(i),c.txns.contains(t),reads::started(s.shards[i].txns[t])
    ensures parts::selected(s,c,t),s.shards[i].txns[t].snapshot.ts == read_ts(s,c,t),c.timestamps.contains(read_ts(s,c,t))
{
    assert(reads::node(s,c,i,t)); let ts=s.shards[i].txns[t].snapshot.ts;
    let r=choose |r: int| #[trigger] time::selected(s,c,r,t) && s.routers[r][t].read_ts == ts;
    parts::owner_is(s,c,r,t); time::valid_time(s,c,t,ts);
}
pub proof fn global_write(s: LState,c: Constants,t: int,k: int) -> (p: int)
    requires facts(s,c),c.txns.contains(t),write_keys(s.ops[t]).contains(k)
    ensures c.keys.contains(k),c.shards.contains(s.catalog[k]),0 <= p < s.shards[s.catalog[k]].log.len(),
        !s.shards[s.catalog[k]].log[p].prepare,s.shards[s.catalog[k]].log[p].txn == t,s.shards[s.catalog[k]].log[p].data.dom().contains(k),
        witness(s,c,t,s.catalog[k],p)
{
    assert(operations::valid(s.ops[t],c,t)); operations::write_member(s.ops[t],k);
    let q=choose |q: int| 0 <= q < s.ops[t].len() && (#[trigger] s.ops[t][q]).kind == Kind::Write && s.ops[t][q].key == k;
    assert(c.keys.contains(k)); projection::written_key(s,c,t,k); let i=s.catalog[k];
    assert(lifecycle::row(s,c,i)); assert(lifecycle::node(s.shards[i],t)); assert(lifecycle::recorded(s.shards[i].log,t,false));
    let p=choose |p: int| 0 <= p < s.shards[i].log.len() && (#[trigger] s.shards[i].log[p]).txn == t && !s.shards[i].log[p].prepare;
    assert(logs::entry(s,c,i,p)); assert(contents::node(s,c,i,t)); assert(!s.shards[i].txns[t].snapshot.aborted);
    assert(s.shards[i].log[p].data.dom().contains(k)); p
}
pub proof fn represented(s: LState,c: Constants,t: int)
    requires facts(s,c),c.txns.contains(t),writer(s,t)
    ensures witness(s,c,t,representative(s,c,t).0,representative(s,c,t).1)
{
    let k=choose |k: int| write_keys(s.ops[t]).contains(k); let p=global_write(s,c,t,k);
    assert(witness(s,c,t,s.catalog[k],p)); assert(exists |x: (int,int)| #[trigger] witness(s,c,t,x.0,x.1)) by { assert(witness(s,c,t,(s.catalog[k],p).0,(s.catalog[k],p).1)); }
}
pub proof fn record_time(s: LState,c: Constants,t: int,i: int,p: int)
    requires facts(s,c),c.txns.contains(t),writer(s,t),c.shards.contains(i),0 <= p < s.shards[i].log.len(),!s.shards[i].log[p].prepare,s.shards[i].log[p].txn == t
    ensures s.shards[i].log[p].ts == commit_ts(s,c,t)
{
    represented(s,c,t); let w=representative(s,c,t); let j=w.0; let q=w.1;
    let k=choose |k: int| s.shards[j].log[q].data.dom().contains(k);
    assert(logs::entry(s,c,j,q)); assert(contents::node(s,c,j,t)); assert(lifecycle::row(s,c,j)); assert(lifecycle::node(s.shards[j],t));
    assert(write_keys(s.shards[j].txns[t].ops).contains(k)); commits::agree(s,c,j,q,i,p,k);
}
pub proof fn after_read(s: LState,c: Constants,t: int)
    requires valid_constants(c),facts(s,c),c.txns.contains(t),writer(s,t)
    ensures parts::selected(s,c,t),0 <= read_ts(s,c,t) < commit_ts(s,c,t)
{
    represented(s,c,t); let w=representative(s,c,t); let i=w.0; let p=w.1;
    assert(logs::entry(s,c,i,p)); assert(lifecycle::row(s,c,i)); assert(lifecycle::node(s.shards[i],t)); local_read_ts(s,c,i,t);
    assert(s.shards[i].log[p].ts > s.shards[i].txns[t].snapshot.ts);
}
pub proof fn record_write(s: LState,c: Constants,i: int,p: int,k: int)
    requires facts(s,c),c.shards.contains(i),0 <= p < s.shards[i].log.len(),!s.shards[i].log[p].prepare,s.shards[i].log[p].data.dom().contains(k)
    ensures c.keys.contains(k),s.catalog[k] == i,c.txns.contains(s.shards[i].log[p].txn),writer(s,s.shards[i].log[p].txn),
        write_keys(s.ops[s.shards[i].log[p].txn]).contains(k),s.shards[i].log[p].ts == commit_ts(s,c,s.shards[i].log[p].txn)
{
    let t=s.shards[i].log[p].txn; assert(logs::entry(s,c,i,p)); assert(contents::node(s,c,i,t)); assert(lifecycle::row(s,c,i)); assert(lifecycle::node(s.shards[i],t));
    assert(write_keys(s.shards[i].txns[t].ops).contains(k)); operations::write_member(s.shards[i].txns[t].ops,k);
    let q=choose |q: int| 0 <= q < s.shards[i].txns[t].ops.len() && (#[trigger] s.shards[i].txns[t].ops[q]).kind == Kind::Write && s.shards[i].txns[t].ops[q].key == k;
    assert(s.catalog[k] == i); assert(operations::valid(s.ops[t],c,t)); projection::written_key(s,c,t,k); record_time(s,c,t,i,p);
}
} // verus!
