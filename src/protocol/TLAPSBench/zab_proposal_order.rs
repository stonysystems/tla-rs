//! Passive proposal records preserve the issuing leader's log order within an epoch.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs as leader;
use super::temporal::Behavior;
verus! {
pub proof fn origin(b: Behavior<LState>,c: Constants,time: int,p: Proposal) -> (w: (int,int))
    requires connections::safety_spec(b,c),time >= 0,b[time].proposals.contains(p),p.epoch > 0
    ensures 0 <= w.0 <= time,c.servers.contains(p.source),b[w.0].nodes[p.source].role == Role::Leading,b[w.0].nodes[p.source].phase != Phase::Discovery,
        b[w.0].nodes[p.source].current == p.epoch,0 <= w.1 < b[w.0].nodes[p.source].history.len(),
        b[w.0].nodes[p.source].history[w.1].zxid == p.zxid,b[w.0].nodes[p.source].history[w.1].value == p.value
    decreases time
{
    if time == 0 { assert(false); (0,0) }
    else if b[time-1].proposals.contains(p) { origin(b,c,time-1,p) }
    else {
        let prev=time-1; let a=super::zab_sessions::step(b,c,prev); let s=b[prev]; let u=b[time];
        logs::at(b,c,prev); logs::preserve(s,c,a); reveal(enabled); reveal(apply);
        match a {
            Action::AckEpoch(i,j) => {
                logs::facts(s,c,i,j); logs::facts(u,c,i,j); let n=u.nodes[i];
                assert(records(i,n.current,n.history).contains(p));
                let k=choose |k: int| #![trigger n.history[k]] 0 <= k < n.history.len() && p == (Proposal { source: i,epoch: n.current,zxid: n.history[k].zxid,value: n.history[k].value });
                (time,k)
            },
            Action::Broadcast(i) => {
                logs::facts(s,c,i,i); logs::facts(u,c,i,i); let n=s.nodes[i]; math::broadcast_index(n);
                let k=index(n.history,Zxid { epoch: n.current,counter: n.sent+1 })-1; (time,k)
            },
            _ => { assert(false); (0,0) },
        }
    }
}
pub proof fn aligned(b: Behavior<LState>,c: Constants,time: int,p: Proposal,read: int,k: int,end: int)
    requires connections::safety_spec(b,c),0 <= read <= end <= time,c.servers.contains(p.source),
        b[read].nodes[p.source].role == Role::Leading,b[read].nodes[p.source].phase != Phase::Discovery,b[read].nodes[p.source].current == p.epoch,
        b[end].nodes[p.source].role == Role::Leading,b[end].nodes[p.source].phase != Phase::Discovery,b[end].nodes[p.source].current == p.epoch,
        0 <= k < b[read].nodes[p.source].history.len(),b[read].nodes[p.source].history[k].zxid == p.zxid,b[read].nodes[p.source].history[k].value == p.value
    ensures 0 <= k < b[end].nodes[p.source].history.len(),b[end].nodes[p.source].history[k].zxid == p.zxid,b[end].nodes[p.source].history[k].value == p.value
{
    leader::same_epoch(b,c,p.source,read,end); assert(equal(b[read].nodes[p.source].history[k],b[end].nodes[p.source].history[k]));
}
pub proof fn observed_pair(b: Behavior<LState>,c: Constants,time: int,a: Proposal,d: Proposal) -> (w: (int,int,int))
    requires connections::safety_spec(b,c),time >= 0,b[time].proposals.contains(a),b[time].proposals.contains(d),
        a.source == d.source,a.epoch == d.epoch,a.epoch > 0,a.zxid != d.zxid || a.value != d.value,!newer(a.zxid,d.zxid)
    ensures 0 <= w.0 <= time,c.servers.contains(a.source),0 <= w.1 < w.2 < b[w.0].nodes[a.source].history.len(),
        b[w.0].nodes[a.source].history[w.1].zxid == a.zxid,b[w.0].nodes[a.source].history[w.1].value == a.value,
        b[w.0].nodes[a.source].history[w.2].zxid == d.zxid,b[w.0].nodes[a.source].history[w.2].value == d.value
{
    let wa=origin(b,c,time,a); let wd=origin(b,c,time,d); let end=if wa.0 >= wd.0 { wa.0 } else { wd.0 };
    aligned(b,c,time,a,wa.0,wa.1,end); aligned(b,c,time,d,wd.0,wd.1,end); logs::at(b,c,end); logs::facts(b[end],c,a.source,a.source);
    let h=b[end].nodes[a.source].history; let x=wa.1; let y=wd.1;
    if x >= y { math::ordered(h,y,x); assert(false); } (end,x,y)
}
pub proof fn before_witness(n: LServer,a: Txn,d: Txn,x: int,y: int)
    requires 1 <= x < y <= n.committed.index,equal(n.history[x-1],a),equal(n.history[y-1],d)
    ensures before(n,a,d)
{}
pub proof fn delivered(b: Behavior<LState>,c: Constants,read: int,i: int,time: int,j: int,x: int,y: int,ta: Txn,td: Txn)
    requires connections::safety_spec(b,c),read >= 0,time >= 0,c.servers.contains(i),c.servers.contains(j),
        0 <= x < y < b[read].nodes[i].history.len(),equal(b[read].nodes[i].history[x],ta),equal(b[read].nodes[i].history[y],td),contains_txn(b[time].nodes[j],td)
    ensures before(b[time].nodes[j],ta,td)
{
    super::zab_committed_prefixes::at(b,c,time); assert(super::zab_committed_prefixes::node(b,c,time,j));
    let n=b[time].nodes[j]; let k=choose |k: int| 1 <= k <= n.committed.index && #[trigger] equal(n.history[k-1],td);
    super::zab_log_matching::historical_matching(b,c,read,i,time,j,y,k-1);
    assert(equal(b[read].nodes[i].history[x],n.history[x])); assert(equal(n.history[x],ta)); assert(equal(n.history[y],td));
    assert(1 <= x+1 < y+1 <= n.committed.index); before_witness(n,ta,td,x+1,y+1);
}
pub proof fn pair(b: Behavior<LState>,c: Constants,time: int,j: int,p: Proposal,q: Proposal)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(j),b[time].proposals.contains(p),b[time].proposals.contains(q),
        p.source == q.source,p.epoch == q.epoch,p.epoch > 0,p.zxid != q.zxid || p.value != q.value
    ensures {
        let a=if newer(p.zxid,q.zxid) { q } else { p }; let d=if newer(p.zxid,q.zxid) { p } else { q };
        let ta=Txn { zxid: a.zxid,value: a.value,ack: Set::empty(),epoch: 0 }; let td=Txn { zxid: d.zxid,value: d.value,ack: Set::empty(),epoch: 0 };
        contains_txn(b[time].nodes[j],td) ==> before(b[time].nodes[j],ta,td)
    },
{
    let a=if newer(p.zxid,q.zxid) { q } else { p }; let d=if newer(p.zxid,q.zxid) { p } else { q };
    let ta=Txn { zxid: a.zxid,value: a.value,ack: Set::empty(),epoch: 0 }; let td=Txn { zxid: d.zxid,value: d.value,ack: Set::empty(),epoch: 0 };
    if contains_txn(b[time].nodes[j],td) {
        let w=observed_pair(b,c,time,a,d); delivered(b,c,w.0,a.source,time,j,w.1,w.2,ta,td);
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures local_primary_order(b[time],c)
{
    let s=b[time];
    assert forall |i: int,e: int,j: int| c.servers.contains(i) && c.servers.contains(j) && 1 <= e <= s.nodes[i].current implies #[trigger] local_at(s,i,e,j) by {
        assert forall |p: Proposal,q: Proposal| #![trigger s.proposals.contains(p), s.proposals.contains(q)] s.proposals.contains(p) && s.proposals.contains(q) && p.source == i && q.source == i && p.epoch == e && q.epoch == e && (p.zxid != q.zxid || p.value != q.value)
            implies {
                let a=if newer(p.zxid,q.zxid) { q } else { p }; let d=if newer(p.zxid,q.zxid) { p } else { q };
                let ta=Txn { zxid: a.zxid,value: a.value,ack: Set::empty(),epoch: 0 }; let td=Txn { zxid: d.zxid,value: d.value,ack: Set::empty(),epoch: 0 };
                contains_txn(s.nodes[j],td) ==> before(s.nodes[j],ta,td)
            } by { pair(b,c,time,j,p,q); }
    }
}
pub proof fn benchmark_local_order(b: Behavior<LState>,c: Constants)
    requires connections::safety_spec(b,c)
    ensures forall |time: int| time >= 0 ==> #[trigger] local_primary_order(b[time],c)
{
    assert forall |time: int| time >= 0 implies #[trigger] local_primary_order(b[time],c) by { at(b,c,time); }
}
} // verus!
