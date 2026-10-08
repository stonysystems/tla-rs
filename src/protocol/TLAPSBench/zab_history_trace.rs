//! AE receipts trace to actual current epochs and histories within one leadership interval.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_receipts as receipts;
use super::zab_sessions::{self as sessions,interval};
use super::temporal::Behavior;
verus! {
pub open spec fn payload(q: Set<AE>,j: int,e: int,h: Seq<Txn>) -> bool {
    exists |r: AE| #![trigger q.contains(r)] q.contains(r) && r.sid == j && r.epoch == e && r.history == h
}
pub proof fn disconnect_payload(q: Set<AE>,who: int,j: int,e: int,h: Seq<Txn>)
    ensures payload(q,j,e,h) == payload(disconnect_ae(q,who),j,e,h)
{
    let u=disconnect_ae(q,who);
    if ae_ids(q).contains(who) {
        let old=choose |r: AE| #![trigger q.contains(r)] q.contains(r) && r.sid == who; assert(q.contains(old) && old.sid == who);
        let new=AE { connected: false,..old }; assert(u.contains(new));
        if payload(q,j,e,h) {
            let r=choose |r: AE| #![trigger q.contains(r)] q.contains(r) && r.sid == j && r.epoch == e && r.history == h;
            if r != old { assert(u.contains(r)); } else { assert(new.sid == j && new.epoch == e && new.history == h); }
        }
        if payload(u,j,e,h) {
            let r=choose |r: AE| #![trigger u.contains(r)] u.contains(r) && r.sid == j && r.epoch == e && r.history == h;
            if r != new { assert(q.contains(r)); } else { assert(old.sid == j && old.epoch == e && old.history == h); }
        }
    }
}
pub proof fn payload_change(s: LState,c: Constants,a: Action,i: int,j: int,e: int,h: Seq<Txn>)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),s.nodes[i].role == Role::Leading,apply(s,c,a).nodes[i].role == Role::Leading,
        !payload(s.nodes[i].ae,j,e,h),payload(apply(s,c,a).nodes[i].ae,j,e,h)
    ensures a == Action::AckEpoch(i,j),s.msgs[(j,i)][0] == Message::AckEpoch(e,h)
{
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,j);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            receipts::facts(s,c,x,y); receipts::facts(s,c,i,x); receipts::facts(s,c,i,y);
            disconnect_payload(s.nodes[x].ae,y,j,e,h); disconnect_payload(s.nodes[y].ae,x,j,e,h);
        },
        Action::Restart(x) => { receipts::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { receipts::facts(s,c,x,y); receipts::facts(s,c,i,y); disconnect_payload(s.nodes[y].ae,x,j,e,h); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { receipts::facts(s,c,i,x); },
        _ => {},
    }
}
pub proof fn message_change(s: LState,c: Constants,a: Action,i: int,j: int,e: int,h: Seq<Txn>)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),
        !s.msgs[(j,i)].contains(Message::AckEpoch(e,h)),apply(s,c,a).msgs[(j,i)].contains(Message::AckEpoch(e,h))
    ensures a == Action::NewEpoch(j,i),apply(s,c,a).nodes[j].current == e && apply(s,c,a).nodes[j].history == h,apply(s,c,a).nodes[i].learners.contains(j),
        apply(s,c,a).nodes[j].accepted == apply(s,c,a).nodes[i].accepted,quorum(ce_ids(apply(s,c,a).nodes[i].ce),c)
{
    reveal(enabled); reveal(apply); connections::channel_pair(c,j,i); receipts::facts(s,c,i,j); receipts::preserve(s,c,a);
    let u=apply(s,c,a); receipts::facts(u,c,i,j); let m=Message::AckEpoch(e,h);
    let k=choose |k: int| 0 <= k < u.msgs[(j,i)].len() && u.msgs[(j,i)][k] == m;
    assert(super::zab_epochs::packet(u,c,j,i,u.msgs[(j,i)][k])); assert(receipts::packet(u,c,j,i,u.msgs[(j,i)][k]));
    if k < s.msgs[(j,i)].len() { assert(s.msgs[(j,i)][k] != m); }
    if k+1 < s.msgs[(j,i)].len() { assert(s.msgs[(j,i)][k+1] != m); }
}
pub proof fn message_origin(b: Behavior<LState>,c: Constants,since: int,time: int,i: int,j: int,e: int,h: Seq<Txn>) -> (read: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),c.servers.contains(j),since > 0,interval(b,i,since,time),b[since-1].nodes[i].role != Role::Leading,
        b[time].msgs[(j,i)].contains(Message::AckEpoch(e,h))
    ensures since <= read <= time,b[read].nodes[j].current == e,b[read].nodes[j].history == h,b[read].nodes[i].learners.contains(j),
        i != j,b[read].nodes[j].accepted == b[read].nodes[i].accepted,quorum(ce_ids(b[read].nodes[i].ce),c)
    decreases time-since
{
    connections::at(b,c,time); connections::facts(b[time],c,i,j); assert(i != j);
    if time == since {
        sessions::start_state(b,c,since,i); assert(false); since
    } else {
        let prev=time-1; let a=sessions::step(b,c,prev);
        if b[prev].msgs[(j,i)].contains(Message::AckEpoch(e,h)) { message_origin(b,c,since,prev,i,j,e,h) }
        else { message_change(b[prev],c,a,i,j,e,h); time }
    }
}
pub proof fn receipt_origin(b: Behavior<LState>,c: Constants,since: int,time: int,i: int,j: int,e: int,h: Seq<Txn>) -> (read: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),c.servers.contains(j),since > 0,interval(b,i,since,time),b[since-1].nodes[i].role != Role::Leading,
        payload(b[time].nodes[i].ae,j,e,h)
    ensures since <= read <= time,b[read].nodes[j].current == e,b[read].nodes[j].history == h,b[read].nodes[i].learners.contains(j),since < time ==> read < time,
        j == i ==> read == since,
        j != i ==> b[read].nodes[j].accepted == b[read].nodes[i].accepted && quorum(ce_ids(b[read].nodes[i].ce),c)
    decreases time-since
{
    if time == since {
        sessions::start_state(b,c,since,i);
        assert(j == i); assert(e == b[since].nodes[i].current && h == b[since].nodes[i].history); since
    } else {
        let prev=time-1; let a=sessions::step(b,c,prev);
        if payload(b[prev].nodes[i].ae,j,e,h) { receipt_origin(b,c,since,prev,i,j,e,h) }
        else {
            payload_change(b[prev],c,a,i,j,e,h); reveal(enabled);
            connections::channel_pair(c,j,i);
            assert(b[prev].msgs[(j,i)].contains(Message::AckEpoch(e,h)));
            message_origin(b,c,since,prev,i,j,e,h)
        }
    }
}
} // verus!
