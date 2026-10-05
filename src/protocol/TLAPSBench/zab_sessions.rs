//! Leadership intervals and the oracle's restriction on new connections.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_epochs as epochs;
use super::zab_phases as phases;
use super::zab_receipts as receipts;
use super::temporal::Behavior;
verus! {
pub open spec fn interval(b: Behavior<LState>,i: int,left: int,right: int) -> bool {
    0 <= left <= right && forall |t: int| left <= t <= right ==> (#[trigger] b[t].nodes[i]).role == Role::Leading
}
pub proof fn step(b: Behavior<LState>,c: Constants,time: int) -> (a: Action)
    requires connections::safety_spec(b,c),time >= 0
    ensures receipts::inductive(b[time],c),enabled(b[time],c,a),b[time+1] == apply(b[time],c,a)
{
    receipts::at(b,c,time); assert(next(b[time],b[time+1],c)); reveal(next);
    choose |a: Action| #[trigger] enabled(b[time],c,a) && b[time+1] == apply(b[time],c,a)
}
pub proof fn start(b: Behavior<LState>,c: Constants,time: int,i: int) -> (since: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),b[time].nodes[i].role == Role::Leading
    ensures 0 < since <= time,interval(b,i,since,time),b[since-1].nodes[i].role != Role::Leading
    decreases time
{
    connections::at(b,c,time);
    if time == 0 { assert(false); 0 }
    else if b[time-1].nodes[i].role == Role::Leading {
        let since=start(b,c,time-1,i);
        assert forall |t: int| since <= t <= time implies (#[trigger] b[t].nodes[i]).role == Role::Leading by { if t < time { assert(t <= time-1); } }
        since
    } else { time }
}
pub proof fn start_state(b: Behavior<LState>,c: Constants,since: int,i: int)
    requires connections::safety_spec(b,c),since > 0,c.servers.contains(i),b[since].nodes[i].role == Role::Leading,b[since-1].nodes[i].role != Role::Leading
    ensures b[since].oracle == Some(i),b[since].nodes[i] == lead(b[since-1].nodes[i],i),b[since-1].nodes[i].role == Role::Looking,
        forall |j: int| c.servers.contains(j) ==> (#[trigger] b[since].msgs[(j,i)]).len() == 0
{
    let time=since-1; let a=step(b,c,time); let s=b[time]; receipts::facts(s,c,i,i);
    reveal(enabled); reveal(apply);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => { receipts::facts(s,c,i,x); receipts::facts(s,c,i,y); receipts::facts(s,c,x,y); },
        Action::Restart(x) => { receipts::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { receipts::facts(s,c,x,y); receipts::facts(s,c,i,y); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { receipts::facts(s,c,i,x); },
        _ => {},
    }
    assert(a == Action::UpdateLeader(i) || a == Action::FollowLeader(i));
    assert forall |j: int| c.servers.contains(j) implies (#[trigger] b[since].msgs[(j,i)]).len() == 0 by {
        connections::facts(s,c,i,j);
    }
}
pub proof fn stable_ce(s: LState,c: Constants,a: Action,i: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),s.nodes[i].role == Role::Leading,apply(s,c,a).nodes[i].role == Role::Leading,quorum(ce_ids(s.nodes[i].ce),c)
    ensures quorum(ce_ids(apply(s,c,a).nodes[i].ce),c),s.nodes[i].accepted == apply(s,c,a).nodes[i].accepted
{
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            receipts::facts(s,c,i,x); receipts::facts(s,c,i,y); receipts::facts(s,c,x,y);
            collections::disconnect_ids(s.nodes[x].ce,s.nodes[x].ae,s.nodes[x].al,y); collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x);
            if a == Action::CEpoch(x,y) { if let Message::CEpoch(e)=s.msgs[(y,x)][0] { collections::ce_update(s.nodes[x].ce,y,e); collections::quorum_add(ce_ids(s.nodes[x].ce),c,y); } }
        },
        Action::Restart(x) => { receipts::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { receipts::facts(s,c,x,y); receipts::facts(s,c,i,y); collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { receipts::facts(s,c,i,x); },
        _ => {},
    }
}
pub proof fn constant_epoch(b: Behavior<LState>,c: Constants,i: int,left: int,right: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),interval(b,i,left,right),quorum(ce_ids(b[left].nodes[i].ce),c)
    ensures b[left].nodes[i].accepted == b[right].nodes[i].accepted,quorum(ce_ids(b[right].nodes[i].ce),c)
    decreases right-left
{
    if left < right {
        let time=right-1; constant_epoch(b,c,i,left,time); let a=step(b,c,time); stable_ce(b[time],c,a,i);
    }
}
pub proof fn no_connections(s: LState,c: Constants,a: Action,i: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),s.nodes[i].role == Role::Leading,apply(s,c,a).nodes[i].role == Role::Leading,s.oracle != Some(i)
    ensures apply(s,c,a).oracle != Some(i),apply(s,c,a).nodes[i].learners.subset_of(s.nodes[i].learners)
{
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => { receipts::facts(s,c,i,x); receipts::facts(s,c,i,y); receipts::facts(s,c,x,y); },
        Action::Restart(x) => { receipts::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { receipts::facts(s,c,x,y); receipts::facts(s,c,i,y); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { receipts::facts(s,c,i,x); },
        _ => {},
    }
}
pub proof fn shrink(b: Behavior<LState>,c: Constants,i: int,left: int,right: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),interval(b,i,left,right),b[left].oracle != Some(i)
    ensures b[right].oracle != Some(i),b[right].nodes[i].learners.subset_of(b[left].nodes[i].learners)
    decreases right-left
{
    if left < right {
        let time=right-1; shrink(b,c,i,left,time); let a=step(b,c,time); no_connections(b[time],c,a,i);
    }
}
pub proof fn disjoint_learners(s: LState,c: Constants,i: int,j: int,k: int)
    requires connections::inductive(s,c),c.servers.contains(i),c.servers.contains(j),i != j,s.nodes[i].role == Role::Leading,s.nodes[j].role == Role::Leading,s.nodes[i].learners.contains(k)
    ensures !s.nodes[j].learners.contains(k)
{
    connections::facts(s,c,i,i); assert(c.servers.contains(k));
    connections::facts(s,c,i,k); connections::facts(s,c,j,k);
}
} // verus!
