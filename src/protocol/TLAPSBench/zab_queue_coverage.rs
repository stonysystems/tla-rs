//! A connected follower's queued log updates cover every broadcast counter.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_sync as sync;
use super::zab_broadcast_bounds as bounds;
use super::zab_queue_math as queue;
use super::zab_queue_prefix::{self as projected,future};
use super::zab_queue_transport as transport;
use super::zab_sessions as sessions;
use super::temporal::Behavior;
verus! {
pub open spec fn covered(s: LState,i: int,j: int) -> bool { s.nodes[i].sent <= queue::count(future(s,i,j),s.nodes[i].current) }
pub open spec fn inductive(b: Behavior<LState>,c: Constants,time: int) -> bool {
    forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) && i != j && b[time].nodes[i].role == Role::Leading
        && b[time].nodes[i].phase != Phase::Discovery && ae_connected(b[time].nodes[i].ae).contains(j) ==> #[trigger] covered(b[time],i,j)
}
pub proof fn initial_inductive(b: Behavior<LState>,c: Constants)
    requires connections::safety_spec(b,c)
    ensures inductive(b,c,0)
{}
pub proof fn preserve_pair(b: Behavior<LState>,c: Constants,time: int,i: int,j: int)
    requires connections::safety_spec(b,c),time >= 0,inductive(b,c,time),c.servers.contains(i),c.servers.contains(j),i != j,
        b[time+1].nodes[i].role == Role::Leading,b[time+1].nodes[i].phase != Phase::Discovery,ae_connected(b[time+1].nodes[i].ae).contains(j)
    ensures covered(b[time+1],i,j)
{
    let a=sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; bounds::at(b,c,time); bounds::preserve(s,c,a);
    logs::facts(s,c,i,j); logs::facts(u,c,i,j); projected::at(b,c,time+1,i,j); assert(bounds::node(u.nodes[i]));
    if u.nodes[i].sent > 0 {
        bounds::was_broadcast(s,c,a,i); reveal(enabled); reveal(apply); connections::channel_pair(c,i,j);
        match a {
            Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
                logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); logs::facts(s,c,j,x); logs::facts(s,c,j,y);
                sync::connected_change(s.nodes[x].ae,y,0,Seq::empty()); sync::connected_change(s.nodes[y].ae,x,0,Seq::empty());
                if a == Action::AckEpoch(x,y) { if let Message::AckEpoch(e,h)=s.msgs[(y,x)][0] { sync::connected_change(s.nodes[x].ae,y,e,h); } }
            },
            Action::Restart(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); logs::facts(s,c,j,y); sync::connected_change(s.nodes[y].ae,x,0,Seq::empty()); } },
            Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); },
            _ => {},
        }
        let n=s.nodes[i]; let q=s.msgs[(i,j)]; assert(bounds::node(n));
        if a == Action::AckEpoch(i,j) {
            queue::append(s.nodes[j].history,q,Message::NewLeader(n.accepted,n.history));
            assert(future(u,i,j) == n.history); assert(covered(u,i,j));
        } else {
            assert(ae_connected(n.ae).contains(j)); sync::connected_ae(s,c,i,j); assert(covered(s,i,j));
            if a == Action::Broadcast(i) {
                projected::at(b,c,time,i,j); math::broadcast_index(n);
                let t=n.history[index(n.history,Zxid { epoch: n.current,counter: n.sent+1 })-1];
                queue::append(s.nodes[j].history,q,Message::Propose(t.zxid,t.value));
                queue::next_counter(future(s,i,j),n.current,n.sent,t.value);
                assert(future(u,i,j) == queue::effect(future(s,i,j),Message::Propose(t.zxid,t.value))); assert(covered(u,i,j));
            } else {
                transport::preserve(s,c,a,i,j); assert(u.nodes[i].sent == n.sent); assert(covered(u,i,j));
            }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures inductive(b,c,time)
    decreases time
{
    if time == 0 { initial_inductive(b,c); }
    else {
        let prev=time-1; at(b,c,prev);
        assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) && i != j && b[time].nodes[i].role == Role::Leading
            && b[time].nodes[i].phase != Phase::Discovery && ae_connected(b[time].nodes[i].ae).contains(j)
            implies #[trigger] covered(b[time],i,j) by { preserve_pair(b,c,prev,i,j); }
    }
}
} // verus!
