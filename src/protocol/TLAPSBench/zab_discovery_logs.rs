//! Election history reports can be observed after accepting the new epoch.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_leader_logs as leader;
use super::zab_history_trace as history;
use super::zab_activation_logs as activation;
use super::zab_sessions::{self as sessions,interval};
use super::temporal::Behavior;
verus! {
pub proof fn step(s: LState,c: Constants,a: Action,i: int)
    requires logs::inductive(s,c),enabled(s,c,a),c.servers.contains(i),
        s.nodes[i].role == Role::Leading,apply(s,c,a).nodes[i].role == Role::Leading,apply(s,c,a).nodes[i].phase == Phase::Discovery
    ensures s.nodes[i].phase == Phase::Discovery,s.nodes[i].current == apply(s,c,a).nodes[i].current,s.nodes[i].history == apply(s,c,a).nodes[i].history
{
    if s.nodes[i].phase != Phase::Discovery { leader::active_step(s,c,a,i); assert(false); }
    reveal(enabled); reveal(apply); logs::facts(s,c,i,i);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y);
        },
        _ => {},
    }
}
pub proof fn unchanged(b: Behavior<LState>,c: Constants,i: int,left: int,right: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),interval(b,i,left,right),b[right].nodes[i].phase == Phase::Discovery
    ensures b[left].nodes[i].phase == Phase::Discovery,b[left].nodes[i].current == b[right].nodes[i].current,b[left].nodes[i].history == b[right].nodes[i].history
    decreases right-left
{
    if left < right {
        let prev=right-1; let a=sessions::step(b,c,prev); logs::at(b,c,prev); step(b[prev],c,a,i); unchanged(b,c,i,left,prev);
    }
}
pub proof fn report_witness(b: Behavior<LState>,c: Constants,time: int,i: int,r: AE) -> (read: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),
        b[time].nodes[i].role == Role::Leading,b[time].nodes[i].phase == Phase::Discovery,
        b[time+1].nodes[i].role == Role::Leading,b[time+1].nodes[i].phase != Phase::Discovery,b[time+1].nodes[i].ae.contains(r)
    ensures 0 <= read <= time,c.servers.contains(r.sid),b[read].nodes[r.sid].accepted == b[time+1].nodes[i].current,
        b[read].nodes[r.sid].current == r.epoch,b[read].nodes[r.sid].history == r.history,b[read].nodes[i].learners.contains(r.sid)
{
    let j=activation::activation_step(b,c,time,i); logs::at(b,c,time); logs::at(b,c,time+1); logs::facts(b[time],c,i,i); logs::facts(b[time+1],c,i,i);
    assert(ae_ids(b[time+1].nodes[i].ae).contains(r.sid)); assert(c.servers.contains(r.sid));
    let since=sessions::start(b,c,time+1,i); assert(since <= time);
    assert(history::payload(b[time+1].nodes[i].ae,r.sid,r.epoch,r.history));
    let sent=history::receipt_origin(b,c,since,time+1,i,r.sid,r.epoch,r.history);
    if r.sid == i {
        unchanged(b,c,i,since,time); reveal(enabled); reveal(apply); time
    } else {
        sessions::constant_epoch(b,c,i,sent,time+1); sent
    }
}
} // verus!
