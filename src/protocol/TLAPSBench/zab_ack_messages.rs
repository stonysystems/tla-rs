//! Queued acknowledgments witness an actual stored prefix in the leader's epoch.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs::{self as leader,prefix};
use super::zab_current_logs as current;
use super::zab_ack_epochs as epochs;
use super::zab_sessions::{self as sessions,interval};
use super::temporal::Behavior;
verus! {
pub open spec fn message(z: Zxid,ld: bool) -> Message { if ld { Message::AckLd(z) } else { Message::Ack(z) } }
pub proof fn created(s: LState,c: Constants,a: Action,i: int,j: int,z: Zxid,ld: bool)
    requires epochs::inductive(s,c),logs::inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),
        !s.msgs[(j,i)].contains(message(z,ld)),apply(s,c,a).msgs[(j,i)].contains(message(z,ld))
    ensures apply(s,c,a).nodes[j].history.len() > 0,last(apply(s,c,a).nodes[j].history) == z,
        apply(s,c,a).nodes[i].role == Role::Leading,apply(s,c,a).nodes[i].phase != Phase::Discovery,
        apply(s,c,a).nodes[j].accepted == apply(s,c,a).nodes[i].current,apply(s,c,a).nodes[j].current == apply(s,c,a).nodes[i].current,
        apply(s,c,a).nodes[i].learners.contains(j)
{
    epochs::preserve(s,c,a); logs::preserve(s,c,a); let u=apply(s,c,a); logs::facts(s,c,i,j); logs::facts(u,c,i,j); connections::channel_pair(c,j,i);
    reveal(enabled); reveal(apply); let m=message(z,ld);
    let k=choose |k: int| 0 <= k < u.msgs[(j,i)].len() && u.msgs[(j,i)][k] == m;
    assert(epochs::packet(u,j,i,u.msgs[(j,i)][k])); assert(super::zab_receipts::packet(u,c,j,i,u.msgs[(j,i)][k])); assert(super::zab_phases::packet(u,c,j,i,u.msgs[(j,i)][k]));
    if k < s.msgs[(j,i)].len() { assert(s.msgs[(j,i)][k] != m); }
    if k+1 < s.msgs[(j,i)].len() { assert(s.msgs[(j,i)][k+1] != m); }
    assert(if ld { a == Action::NewLeader(j,i) } else { a == Action::Propose(j,i) });
}
pub proof fn message_origin(b: Behavior<LState>,c: Constants,since: int,time: int,i: int,j: int,z: Zxid,ld: bool) -> (read: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),c.servers.contains(j),since > 0,interval(b,i,since,time),b[since-1].nodes[i].role != Role::Leading,
        b[time].msgs[(j,i)].contains(message(z,ld))
    ensures since < read <= time,b[read].nodes[j].history.len() > 0,last(b[read].nodes[j].history) == z,
        b[read].nodes[i].role == Role::Leading,b[read].nodes[i].phase != Phase::Discovery,
        b[read].nodes[j].accepted == b[read].nodes[i].current,b[read].nodes[j].current == b[read].nodes[i].current,
        b[read].nodes[i].learners.contains(j)
    decreases time-since
{
    if time == since { sessions::start_state(b,c,since,i); assert(false); since }
    else {
        let prev=time-1; let a=sessions::step(b,c,prev);
        if b[prev].msgs[(j,i)].contains(message(z,ld)) { message_origin(b,c,since,prev,i,j,z,ld) }
        else { epochs::at(b,c,prev); logs::at(b,c,prev); created(b[prev],c,a,i,j,z,ld); time }
    }
}
pub proof fn stored_prefix(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,z: Zxid,ld: bool) -> (read: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),b[time].msgs[(j,i)].contains(message(z,ld))
    ensures 0 <= read <= time,b[read].nodes[j].history.len() > 0,last(b[read].nodes[j].history) == z,
        b[read].nodes[j].accepted == b[time].nodes[i].current,b[read].nodes[j].current == b[time].nodes[i].current,
        b[read].nodes[i].role == Role::Leading,b[read].nodes[i].phase != Phase::Discovery,b[read].nodes[i].current == b[time].nodes[i].current,
        b[read].nodes[i].learners.contains(j),prefix(b[read].nodes[j].history,b[time].nodes[i].history),
        index(b[time].nodes[i].history,z) == b[read].nodes[j].history.len(),1 <= index(b[time].nodes[i].history,z) <= b[time].nodes[i].history.len()
{
    epochs::at(b,c,time); logs::at(b,c,time); logs::facts(b[time],c,i,j);
    let k=choose |k: int| 0 <= k < b[time].msgs[(j,i)].len() && b[time].msgs[(j,i)][k] == message(z,ld);
    assert(super::zab_phases::packet(b[time],c,j,i,b[time].msgs[(j,i)][k]));
    let since=sessions::start(b,c,time,i); let read=message_origin(b,c,since,time,i,j,z,ld);
    logs::at(b,c,read); logs::facts(b[read],c,i,j); current::at(b,c,read,j); current::aligned(b,c,read,j,i);
    leader::active_interval(b,c,i,read,time); leader::transitive(b[read].nodes[j].history,b[read].nodes[i].history,b[time].nodes[i].history);
    let p=b[read].nodes[j].history.len() as int-1;
    assert(equal(b[read].nodes[j].history[p],b[time].nodes[i].history[p])); math::index_at(b[time].nodes[i].history,p);
    read
}
} // verus!
