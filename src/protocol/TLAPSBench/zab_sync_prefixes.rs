//! FIFO synchronization snapshots include the prefixes processed before them.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs::{self as leader,epoch_prefix};
use super::zab_proposal_logs as proposals;
use super::zab_current_logs as current;
use super::zab_sessions as sessions;
use super::temporal::Behavior;
verus! {
pub open spec fn before(first: Message,second: Message) -> bool {
    match second {
        Message::NewLeader(e,h) => match first {
            Message::NewLeader(e0,h0) => e0 == e && epoch_prefix(h0,h,e),
            Message::Propose(z,v) => proposals::contains(h,z,v),
            _ => true,
        },
        _ => true,
    }
}
pub open spec fn awaiting(n: LServer,m: Message) -> bool {
    match m { Message::NewLeader(e,h) => n.current == e ==> epoch_prefix(n.history,h,e),_ => true }
}
pub open spec fn inductive(b: Behavior<LState>,c: Constants,time: int) -> bool {
    (forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < b[time].msgs[(i,j)].len()
        ==> #[trigger] awaiting(b[time].nodes[j],b[time].msgs[(i,j)][k]))
    && (forall |i: int,j: int,p: int,r: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < r < b[time].msgs[(i,j)].len()
        ==> #[trigger] before(b[time].msgs[(i,j)][p],b[time].msgs[(i,j)][r]))
}
pub proof fn initial_inductive(b: Behavior<LState>,c: Constants)
    requires connections::safety_spec(b,c)
    ensures inductive(b,c,0)
{
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < b[0].msgs[(i,j)].len()
        implies #[trigger] awaiting(b[0].nodes[j],b[0].msgs[(i,j)][k]) by { connections::channel_pair(c,i,j); }
    assert forall |i: int,j: int,p: int,r: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < r < b[0].msgs[(i,j)].len()
        implies #[trigger] before(b[0].msgs[(i,j)][p],b[0].msgs[(i,j)][r]) by { connections::channel_pair(c,i,j); }
}
pub proof fn preserve_order(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,p: int,r: int)
    requires connections::safety_spec(b,c),time >= 0,inductive(b,c,time),c.servers.contains(i),c.servers.contains(j),0 <= p < r < b[time+1].msgs[(i,j)].len()
    ensures before(b[time+1].msgs[(i,j)][p],b[time+1].msgs[(i,j)][r])
{
    let a=sessions::step(b,c,time); proposals::at(b,c,time); let s=b[time]; let u=b[time+1];
    proposals::preserve(s,c,a); connections::channel_pair(c,i,j); logs::facts(s,c,i,j); reveal(enabled); reveal(apply);
    assert(proposals::packet(u.nodes[i].history,u.nodes[i].current,u.msgs[(i,j)][p]));
    if r < s.msgs[(i,j)].len() { assert(before(s.msgs[(i,j)][p],s.msgs[(i,j)][r])); }
    if r+1 < s.msgs[(i,j)].len() { assert(before(s.msgs[(i,j)][p+1],s.msgs[(i,j)][r+1])); }
}
pub proof fn preserve_awaiting(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,k: int)
    requires connections::safety_spec(b,c),time >= 0,inductive(b,c,time),c.servers.contains(i),c.servers.contains(j),0 <= k < b[time+1].msgs[(i,j)].len()
    ensures awaiting(b[time+1].nodes[j],b[time+1].msgs[(i,j)][k])
{
    let a=sessions::step(b,c,time); proposals::at(b,c,time); let s=b[time]; let u=b[time+1];
    proposals::preserve(s,c,a); connections::channel_pair(c,i,j); logs::facts(s,c,i,j); logs::facts(u,c,i,j); reveal(enabled); reveal(apply);
    if let Message::NewLeader(e,h)=u.msgs[(i,j)][k] {
        assert(super::zab_phases::packet(u,c,i,j,u.msgs[(i,j)][k]));
        assert(super::zab_epochs::packet(u,c,i,j,u.msgs[(i,j)][k]));
        if u.nodes[j].current == e {
            current::at(b,c,time+1,j); current::aligned(b,c,time+1,j,i);
        }
    }
    if k < s.msgs[(i,j)].len() { assert(awaiting(s.nodes[j],s.msgs[(i,j)][k])); }
    if k+1 < s.msgs[(i,j)].len() {
        assert(awaiting(s.nodes[j],s.msgs[(i,j)][k+1])); assert(before(s.msgs[(i,j)][0],s.msgs[(i,j)][k+1]));
    }
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); logs::facts(s,c,j,x); logs::facts(s,c,j,y);
        },
        Action::Restart(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); logs::facts(s,c,j,y); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); },
        _ => {},
    }
    if a == Action::Propose(j,i) && k+1 < s.msgs[(i,j)].len() {
        if let Message::Propose(z,v)=s.msgs[(i,j)][0] {
            if let Message::NewLeader(e,h)=s.msgs[(i,j)][k+1] {
                let n=s.nodes[j];
                if next_zxid(last(n.history),z) {
                    assert(!super::zab_sync::pending(s.msgs[(i,j)],s.nodes[i].current,0)); assert(n.current == s.nodes[i].current);
                    assert(logs::packet(s,i,s.msgs[(i,j)][k+1])); assert(super::zab_epochs::packet(s,c,i,j,s.msgs[(i,j)][k+1]));
                    let p=choose |p: int| 0 <= p < h.len() && h[p].zxid == z && h[p].value == v;
                    leader::append_prefix(n.history,h,e,p,Txn { zxid: z,value: v,ack: Set::empty(),epoch: n.current });
                }
            }
        }
    }
}
pub proof fn preserve(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0,inductive(b,c,time)
    ensures inductive(b,c,time+1)
{
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < b[time+1].msgs[(i,j)].len()
        implies #[trigger] awaiting(b[time+1].nodes[j],b[time+1].msgs[(i,j)][k]) by { preserve_awaiting(b,c,time,i,j,k); }
    assert forall |i: int,j: int,p: int,r: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < r < b[time+1].msgs[(i,j)].len()
        implies #[trigger] before(b[time+1].msgs[(i,j)][p],b[time+1].msgs[(i,j)][r]) by { preserve_order(b,c,time,i,j,p,r); }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures inductive(b,c,time)
    decreases time
{
    if time == 0 { initial_inductive(b,c); }
    else { at(b,c,time-1); preserve(b,c,time-1); }
}
} // verus!
