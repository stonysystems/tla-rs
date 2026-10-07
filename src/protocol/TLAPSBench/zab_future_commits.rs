//! The complete FIFO replay contains the leader's currently advertised commitment.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs::epoch_prefix;
use super::zab_queue_math as queue;
use super::zab_queue_prefix::{self as projected,future};
use super::zab_queue_coverage as coverage;
use super::zab_broadcast_commits as commits;
use super::temporal::Behavior;
verus! {
pub proof fn covered_index(h: Seq<Txn>,d: Seq<Txn>,e: int,sent: int,k: int)
    requires math::shape(h),math::shape(d),epoch_prefix(d,h,e),sent <= queue::count(d,e),0 <= k < h.len(),commits::sent_or_old(h[k].zxid,e,sent)
    ensures k < d.len(),equal(h[k],d[k])
{
    if k >= d.len() {
        assert(h[k].zxid.epoch == e && h[k].zxid.counter > 0);
        let p=d.len() as int-1; assert(equal(d[p],h[p])); math::ordered(h,p,k); assert(false);
    }
    assert(equal(d[k],h[k]));
}
pub proof fn broadcasting(b: Behavior<LState>,c: Constants,time: int,i: int,j: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),i != j,
        b[time].nodes[i].role == Role::Leading,b[time].nodes[i].phase == Phase::Broadcast,ae_connected(b[time].nodes[i].ae).contains(j)
    ensures 1 <= index(future(b[time],i,j),b[time].nodes[i].committed.zxid) <= future(b[time],i,j).len(),
        index(future(b[time],i,j),b[time].nodes[i].committed.zxid) == b[time].nodes[i].committed.index
{
    projected::at(b,c,time,i,j); coverage::at(b,c,time); commits::at(b,c,time);
    let s=b[time]; logs::at(b,c,time); logs::facts(s,c,i,j); let n=s.nodes[i];
    assert(coverage::covered(s,i,j)); assert(commits::node(n)); let k=n.committed.index-1;
    covered_index(n.history,future(s,i,j),n.current,n.sent,k); math::index_at(future(s,i,j),k);
}
pub proof fn synchronizing(b: Behavior<LState>,c: Constants,time: int,i: int,j: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),i != j,
        b[time].nodes[i].role == Role::Leading,b[time].nodes[i].phase == Phase::Synchronization,ae_connected(b[time].nodes[i].ae).contains(j)
    ensures math::same(future(b[time],i,j),b[time].nodes[i].history),
        index(future(b[time],i,j),last(b[time].nodes[i].history)) == b[time].nodes[i].history.len(),
        1 <= index(future(b[time],i,j),last(b[time].nodes[i].history)) <= future(b[time],i,j).len()
{
    super::zab_sync_history::at(b,c,time,i); projected::at(b,c,time,i,j); let n=b[time].nodes[i]; let d=future(b[time],i,j);
    if d.len() < n.history.len() { let p=d.len() as int; assert(n.history[p].zxid.epoch == n.current); assert(n.history[p].zxid.epoch < n.current); }
    assert(math::same(d,n.history)); math::same_last(d,n.history); math::index_at(d,d.len() as int-1);
}
} // verus!
