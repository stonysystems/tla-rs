//! Comparing history reports from one current epoch compares prefixes of one leader log.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs::{self as leader,prefix};
use super::zab_current_logs as current;
use super::zab_entry_origins::through;
use super::temporal::Behavior;
verus! {
pub proof fn extend(h: Seq<Txn>,a: Seq<Txn>,d: Seq<Txn>,k: int)
    requires through(h,a,k),prefix(a,d)
    ensures through(h,d,k)
{
    assert forall |p: int| 0 <= p <= k implies #[trigger] equal(h[p],d[p]) by { assert(equal(h[p],a[p])); assert(equal(a[p],d[p])); }
}
pub proof fn prefixes(a: Seq<Txn>,d: Seq<Txn>,reference: Seq<Txn>)
    requires a.len() > 0,d.len() > 0,math::shape(reference),prefix(a,reference),prefix(d,reference),!newer(last(a),last(d))
    ensures prefix(a,d)
{
    let ka=a.len() as int-1; let kd=d.len() as int-1;
    assert(equal(a[ka],reference[ka])); assert(equal(d[kd],reference[kd]));
    if ka > kd { math::ordered(reference,kd,ka); assert(false); }
    assert forall |p: int| 0 <= p < a.len() implies #[trigger] equal(a[p],d[p]) by { assert(equal(a[p],reference[p])); assert(equal(d[p],reference[p])); }
}
pub proof fn reports(b: Behavior<LState>,c: Constants,ta: int,i: int,td: int,j: int)
    requires connections::safety_spec(b,c),ta >= 0,td >= 0,c.servers.contains(i),c.servers.contains(j),
        b[ta].nodes[i].current == b[td].nodes[j].current,b[ta].nodes[i].current > 0,
        !newer(last(b[ta].nodes[i].history),last(b[td].nodes[j].history))
    ensures prefix(b[ta].nodes[i].history,b[td].nodes[j].history)
{
    current::at(b,c,ta,i); current::at(b,c,td,j); let a=b[ta].nodes[i]; let d=b[td].nodes[j];
    let w=choose |w: (int,int)| current::witness(b,c,ta,a.history,a.current,w);
    let v=choose |v: (int,int)| current::witness(b,c,td,d.history,d.current,v);
    super::zab_elections::unique(b,c,w.0,w.1,v.0,v.1);
    logs::at(b,c,ta); logs::facts(b[ta],c,i,i); logs::at(b,c,td); logs::facts(b[td],c,j,j);
    if w.0 <= v.0 {
        leader::same_epoch(b,c,w.1,w.0,v.0); leader::transitive(a.history,b[w.0].nodes[w.1].history,b[v.0].nodes[w.1].history);
        logs::at(b,c,v.0); logs::facts(b[v.0],c,w.1,w.1); prefixes(a.history,d.history,b[v.0].nodes[w.1].history);
    } else {
        leader::same_epoch(b,c,w.1,v.0,w.0); leader::transitive(d.history,b[v.0].nodes[w.1].history,b[w.0].nodes[w.1].history);
        logs::at(b,c,w.0); logs::facts(b[w.0],c,w.1,w.1); prefixes(a.history,d.history,b[w.0].nodes[w.1].history);
    }
}
} // verus!
