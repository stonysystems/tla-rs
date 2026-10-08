//! CE receipts trace to accepted-epoch snapshots within one leadership interval.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_receipts as receipts;
use super::zab_sessions::{self as sessions,interval};
use super::temporal::Behavior;
verus! {
pub open spec fn payload(q: Set<CE>,j: int,e: int) -> bool {
    exists |r: CE| #![trigger q.contains(r)] q.contains(r) && r.sid == j && r.epoch == e
}
pub proof fn disconnect_payload(q: Set<CE>,who: int,j: int,e: int)
    ensures payload(q,j,e) == payload(disconnect_ce(q,who),j,e)
{
    let u=disconnect_ce(q,who);
    if ce_ids(q).contains(who) {
        let old=choose |r: CE| #![trigger q.contains(r)] q.contains(r) && r.sid == who; assert(q.contains(old) && old.sid == who);
        let new=CE { connected: false,..old }; assert(u.contains(new));
        if payload(q,j,e) {
            let r=choose |r: CE| #![trigger q.contains(r)] q.contains(r) && r.sid == j && r.epoch == e;
            if r != old { assert(u.contains(r)); } else { assert(new.sid == j && new.epoch == e); }
        }
        if payload(u,j,e) {
            let r=choose |r: CE| #![trigger u.contains(r)] u.contains(r) && r.sid == j && r.epoch == e;
            if r != new { assert(q.contains(r)); } else { assert(old.sid == j && old.epoch == e); }
        }
    }
}
pub proof fn payload_change(s: LState,c: Constants,a: Action,i: int,j: int,e: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),s.nodes[i].role == Role::Leading,apply(s,c,a).nodes[i].role == Role::Leading,
        !payload(s.nodes[i].ce,j,e),payload(apply(s,c,a).nodes[i].ce,j,e)
    ensures a == Action::CEpoch(i,j),s.msgs[(j,i)][0] == Message::CEpoch(e)
{
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,j);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            receipts::facts(s,c,x,y); receipts::facts(s,c,i,x); receipts::facts(s,c,i,y);
            disconnect_payload(s.nodes[x].ce,y,j,e); disconnect_payload(s.nodes[y].ce,x,j,e);
        },
        Action::Restart(x) => { receipts::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { receipts::facts(s,c,x,y); receipts::facts(s,c,i,y); disconnect_payload(s.nodes[y].ce,x,j,e); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { receipts::facts(s,c,i,x); },
        _ => {},
    }
}
pub proof fn message_change(s: LState,c: Constants,a: Action,i: int,j: int,e: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),
        !s.msgs[(j,i)].contains(Message::CEpoch(e)),apply(s,c,a).msgs[(j,i)].contains(Message::CEpoch(e))
    ensures a == Action::Connect(i,j),apply(s,c,a).nodes[j].accepted == e,apply(s,c,a).nodes[i].learners.contains(j)
{
    reveal(enabled); reveal(apply); connections::channel_pair(c,j,i);
    let u=apply(s,c,a); let m=Message::CEpoch(e);
    let k=choose |k: int| 0 <= k < u.msgs[(j,i)].len() && u.msgs[(j,i)][k] == m;
    if k < s.msgs[(j,i)].len() { assert(s.msgs[(j,i)][k] != m); }
    if k+1 < s.msgs[(j,i)].len() { assert(s.msgs[(j,i)][k+1] != m); }
}
pub proof fn message_origin(b: Behavior<LState>,c: Constants,since: int,time: int,i: int,j: int,e: int) -> (read: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),c.servers.contains(j),since > 0,interval(b,i,since,time),b[since-1].nodes[i].role != Role::Leading,
        b[time].msgs[(j,i)].contains(Message::CEpoch(e))
    ensures since <= read <= time,b[read].nodes[j].accepted == e,b[read].nodes[i].learners.contains(j)
    decreases time-since
{
    if time == since {
        sessions::start_state(b,c,since,i); assert(false); since
    } else {
        let prev=time-1; let a=sessions::step(b,c,prev);
        if b[prev].msgs[(j,i)].contains(Message::CEpoch(e)) { message_origin(b,c,since,prev,i,j,e) }
        else { message_change(b[prev],c,a,i,j,e); time }
    }
}
pub proof fn receipt_origin(b: Behavior<LState>,c: Constants,since: int,time: int,i: int,j: int,e: int) -> (read: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),c.servers.contains(j),since > 0,interval(b,i,since,time),b[since-1].nodes[i].role != Role::Leading,
        payload(b[time].nodes[i].ce,j,e)
    ensures since <= read <= time,b[read].nodes[j].accepted == e,b[read].nodes[i].learners.contains(j)
    decreases time-since
{
    if time == since {
        sessions::start_state(b,c,since,i);
        assert(j == i); assert(e == b[since].nodes[i].accepted); since
    } else {
        let prev=time-1; let a=sessions::step(b,c,prev);
        if payload(b[prev].nodes[i].ce,j,e) { receipt_origin(b,c,since,prev,i,j,e) }
        else {
            payload_change(b[prev],c,a,i,j,e); reveal(enabled);
            connections::channel_pair(c,j,i);
            assert(b[prev].msgs[(j,i)].contains(Message::CEpoch(e)));
            message_origin(b,c,since,prev,i,j,e)
        }
    }
}
pub proof fn proposal(b: Behavior<LState>,c: Constants,since: int,time: int,i: int) -> (at: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),c.servers.len() > 1,since > 0,interval(b,i,since,time),b[since-1].nodes[i].role != Role::Leading,
        quorum(ce_ids(b[time].nodes[i].ce),c)
    ensures since < at <= time,quorum(ce_ids(b[at].nodes[i].ce),c),
        forall |r: CE| #![trigger b[at].nodes[i].ce.contains(r)] b[at].nodes[i].ce.contains(r) ==> r.epoch < b[time].nodes[i].accepted
    decreases time-since
{
    if time == since {
        sessions::start_state(b,c,since,i); collections::fresh_ids(b[since-1].nodes[i],i); assert(false); since
    } else {
        let prev=time-1; let a=sessions::step(b,c,prev); let s=b[prev]; let u=b[time]; receipts::facts(s,c,i,i);
        if quorum(ce_ids(s.nodes[i].ce),c) {
            let at=proposal(b,c,since,prev,i); sessions::stable_ce(s,c,a,i); at
        } else {
            reveal(enabled); reveal(apply);
            match a {
                Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
                    receipts::facts(s,c,x,y); receipts::facts(s,c,i,x); receipts::facts(s,c,i,y);
                    collections::disconnect_ids(s.nodes[x].ce,s.nodes[x].ae,s.nodes[x].al,y); collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x);
                },
                Action::Restart(x) => { receipts::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { receipts::facts(s,c,x,y); receipts::facts(s,c,i,y); collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x); } },
                Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { receipts::facts(s,c,i,x); },
                _ => {},
            }
            assert(exists |j: int| a == Action::CEpoch(i,j));
            let j=choose |j: int| a == Action::CEpoch(i,j);
            receipts::facts(s,c,i,j);
            collections::maximum_correct(u.nodes[i].ce.map(|r: CE| r.epoch));
            assert forall |r: CE| #![trigger u.nodes[i].ce.contains(r)] u.nodes[i].ce.contains(r) implies r.epoch < u.nodes[i].accepted by {
                assert(u.nodes[i].ce.map(|r: CE| r.epoch).contains(r.epoch));
            }
            time
        }
    }
}
} // verus!
