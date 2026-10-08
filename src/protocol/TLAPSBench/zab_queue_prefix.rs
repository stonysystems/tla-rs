//! Replaying a connected follower's pending channel yields a prefix of its leader's log.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_sync as sync;
use super::zab_proposal_logs as proposals;
use super::zab_current_logs as current;
use super::zab_leader_logs::epoch_prefix;
use super::zab_queue_math as queue;
use super::temporal::Behavior;
verus! {
pub open spec fn future(s: LState,i: int,j: int) -> Seq<Txn> { queue::replay(s.nodes[j].history,s.msgs[(i,j)]) }
pub proof fn packets(s: LState,c: Constants,i: int,j: int)
    requires proposals::inductive(s,c),c.servers.contains(i),c.servers.contains(j)
    ensures queue::fits_queue(s.nodes[i].history,s.nodes[i].current,s.msgs[(i,j)])
{
    assert forall |p: int| 0 <= p < s.msgs[(i,j)].len() implies #[trigger] queue::fits(s.nodes[i].history,s.nodes[i].current,s.msgs[(i,j)][p]) by {
        assert(proposals::packet(s.nodes[i].history,s.nodes[i].current,s.msgs[(i,j)][p])); assert(logs::packet(s,i,s.msgs[(i,j)][p]));
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int,i: int,j: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),i != j,
        b[time].nodes[i].role == Role::Leading,b[time].nodes[i].phase != Phase::Discovery,ae_connected(b[time].nodes[i].ae).contains(j)
    ensures math::shape(future(b[time],i,j)),epoch_prefix(future(b[time],i,j),b[time].nodes[i].history,b[time].nodes[i].current),
        math::bounded(future(b[time],i,j),b[time].nodes[i].current),queue::count(future(b[time],i,j),b[time].nodes[i].current) >= 0
{
    proposals::at(b,c,time); let s=b[time]; logs::facts(s,c,i,j); packets(s,c,i,j); assert(sync::ready(s,c,i,j));
    let n=s.nodes[i]; let q=s.msgs[(i,j)];
    if s.nodes[j].current == n.current {
        current::at(b,c,time,j); current::aligned(b,c,time,j,i); queue::replay_prefix(s.nodes[j].history,n.history,n.current,q);
    } else {
        let p=choose |p: int| #![trigger q[p]] 0 <= p < q.len() && sync::leader_message(q[p],n.current);
        assert(queue::fits(n.history,n.current,q[p]));
        if let Message::NewLeader(e,h)=q[p] {
            queue::snapshot(s.nodes[j].history,q,p,e,h); queue::suffix(n.history,n.current,q,p+1);
            queue::replay_prefix(h,n.history,n.current,q.skip(p+1));
        }
    }
    queue::bounded_prefix(future(s,i,j),n.history,n.current);
    assert(future(s,i,j)[future(s,i,j).len() as int-1].zxid.counter > 0);
}
} // verus!
