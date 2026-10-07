//! A leader's synchronization history contains only entries from earlier epochs.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_activation_logs as activation;
use super::zab_sessions as sessions;
use super::temporal::Behavior;
verus! {
pub proof fn step(s: LState,c: Constants,a: Action,i: int)
    requires logs::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].role == Role::Leading,apply(s,c,a).nodes[i].phase == Phase::Synchronization
    ensures s.nodes[i].role == Role::Leading,
        s.nodes[i].phase == Phase::Discovery || (s.nodes[i].phase == Phase::Synchronization && s.nodes[i].current == apply(s,c,a).nodes[i].current && math::same(s.nodes[i].history,apply(s,c,a).nodes[i].history))
{
    reveal(enabled); reveal(apply); logs::facts(s,c,i,i);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y);
            if a == Action::AckLd(x,y) { if let Message::AckLd(z)=s.msgs[(y,x)][0] { math::ack_contents(s.nodes[x].history,y,z); } }
        },
        _ => {},
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),b[time].nodes[i].role == Role::Leading,b[time].nodes[i].phase == Phase::Synchronization
    ensures math::bounded(b[time].nodes[i].history,b[time].nodes[i].current-1)
    decreases time
{
    if time == 0 { assert(false); }
    else {
        let prev=time-1; let a=sessions::step(b,c,prev); logs::at(b,c,prev); logs::facts(b[prev],c,i,i); step(b[prev],c,a,i);
        if b[prev].nodes[i].phase == Phase::Discovery { activation::earlier_history(b,c,prev,i); }
        else {
            at(b,c,prev,i); math::transfer(b[prev].nodes[i].history,b[time].nodes[i].history,b[prev].nodes[i].current-1);
        }
    }
}
} // verus!
