//! Queued synchronization and proposal messages refer to their active leader's log.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_phases as phases;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs::{self as leader,epoch_prefix};
use super::temporal::Behavior;
verus! {
pub open spec fn contains(h: Seq<Txn>,z: Zxid,v: int) -> bool {
    exists |p: int| 0 <= p < h.len() && (#[trigger] h[p]).zxid == z && h[p].value == v
}
pub open spec fn packet(h: Seq<Txn>,e: int,m: Message) -> bool {
    match m {
        Message::NewLeader(epoch,copy) => epoch == e && epoch_prefix(copy,h,e),
        Message::Propose(z,v) => z.epoch == e && contains(h,z,v),
        _ => true,
    }
}
pub proof fn grow(a: Seq<Txn>,b: Seq<Txn>,e: int,m: Message)
    requires epoch_prefix(a,b,e),packet(a,e,m)
    ensures packet(b,e,m)
{
    match m {
        Message::NewLeader(_,h) => { leader::epoch_transitive(h,a,b,e); },
        Message::Propose(z,v) => {
            let p=choose |p: int| 0 <= p < a.len() && a[p].zxid == z && a[p].value == v;
            assert(equal(a[p],b[p])); assert(b[p].zxid == z && b[p].value == v);
        },
        _ => {},
    }
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    logs::inductive(s,c)
    && forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < s.msgs[(i,j)].len()
        ==> #[trigger] packet(s.nodes[i].history,s.nodes[i].current,s.msgs[(i,j)][k])
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{
    logs::initial_inductive(c);
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < initial(c).msgs[(i,j)].len()
        implies #[trigger] packet(initial(c).nodes[i].history,initial(c).nodes[i].current,initial(c).msgs[(i,j)][k]) by { connections::channel_pair(c,i,j); }
}
pub proof fn preserve_packet(s: LState,c: Constants,a: Action,i: int,j: int,k: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),0 <= k < apply(s,c,a).msgs[(i,j)].len()
    ensures packet(apply(s,c,a).nodes[i].history,apply(s,c,a).nodes[i].current,apply(s,c,a).msgs[(i,j)][k])
{
    reveal(enabled); reveal(apply); logs::facts(s,c,i,j); connections::channel_pair(c,i,j);
    logs::preserve(s,c,a); let u=apply(s,c,a); logs::facts(u,c,i,j);
    assert(phases::packet(u,c,i,j,u.msgs[(i,j)][k]));
    if s.nodes[i].role == Role::Leading && s.nodes[i].phase != Phase::Discovery && u.nodes[i].role == Role::Leading {
        leader::active_step(s,c,a,i);
        if k < s.msgs[(i,j)].len() { grow(s.nodes[i].history,u.nodes[i].history,s.nodes[i].current,s.msgs[(i,j)][k]); }
        if k+1 < s.msgs[(i,j)].len() { grow(s.nodes[i].history,u.nodes[i].history,s.nodes[i].current,s.msgs[(i,j)][k+1]); }
    }
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); logs::facts(s,c,j,x); logs::facts(s,c,j,y);
        },
        Action::Restart(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); logs::facts(s,c,j,y); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); },
        Action::Broadcast(x) => {
            logs::facts(s,c,i,x); logs::facts(s,c,j,x); math::broadcast_index(s.nodes[x]);
            let p=index(s.nodes[x].history,Zxid { epoch: s.nodes[x].current,counter: s.nodes[x].sent+1 })-1;
            let t=s.nodes[x].history[p]; assert(contains(s.nodes[x].history,t.zxid,t.value));
        },
        _ => {},
    }
    if k < s.msgs[(i,j)].len() { assert(packet(s.nodes[i].history,s.nodes[i].current,s.msgs[(i,j)][k])); assert(phases::packet(s,c,i,j,s.msgs[(i,j)][k])); }
    if k+1 < s.msgs[(i,j)].len() { assert(packet(s.nodes[i].history,s.nodes[i].current,s.msgs[(i,j)][k+1])); assert(phases::packet(s,c,i,j,s.msgs[(i,j)][k+1])); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    logs::preserve(s,c,a); let u=apply(s,c,a);
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < u.msgs[(i,j)].len()
        implies #[trigger] packet(u.nodes[i].history,u.nodes[i].current,u.msgs[(i,j)][k]) by { preserve_packet(s,c,a,i,j,k); }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures inductive(b[time],c)
    decreases time
{
    if time == 0 { initial_inductive(c); }
    else {
        at(b,c,time-1); let a=super::zab_sessions::step(b,c,time-1); preserve(b[time-1],c,a);
    }
}
} // verus!
