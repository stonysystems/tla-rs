//! Every epoch-acknowledgment quorum has actual accepted-epoch witnesses.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_receipts as receipts;
use super::zab_sessions::{self as sessions,interval};
use super::temporal::Behavior;
verus! {
pub proof fn new_sender(s: LState,c: Constants,a: Action,i: int,j: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),s.nodes[i].role == Role::Leading,apply(s,c,a).nodes[i].role == Role::Leading,
        !ae_ids(s.nodes[i].ae).contains(j),ae_ids(apply(s,c,a).nodes[i].ae).contains(j)
    ensures a == Action::AckEpoch(i,j)
{
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,j);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            receipts::facts(s,c,x,y); receipts::facts(s,c,i,x); receipts::facts(s,c,i,y);
            collections::disconnect_ids(s.nodes[x].ce,s.nodes[x].ae,s.nodes[x].al,y); collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x);
            if a == Action::AckEpoch(x,y) { if let Message::AckEpoch(e,h)=s.msgs[(y,x)][0] { collections::ae_update(s.nodes[x].ae,y,e,h); } }
        },
        Action::Restart(x) => { receipts::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { receipts::facts(s,c,x,y); receipts::facts(s,c,i,y); collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { receipts::facts(s,c,i,x); },
        _ => {},
    }
}
pub proof fn accepted_witness(b: Behavior<LState>,c: Constants,since: int,time: int,i: int,j: int) -> (at: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),c.servers.contains(j),since > 0,interval(b,i,since,time),b[since-1].nodes[i].role != Role::Leading,
        ae_ids(b[time].nodes[i].ae).contains(j)
    ensures since <= at <= time,b[at].nodes[j].accepted == b[time].nodes[i].accepted,b[at].nodes[i].learners.contains(j)
    decreases time-since
{
    if j == i { connections::at(b,c,time); connections::facts(b[time],c,i,i); time }
    else if time == since {
        sessions::start_state(b,c,since,i); collections::fresh_ids(b[since-1].nodes[i],i); assert(false); since
    } else {
        let prev=time-1; let a=sessions::step(b,c,prev); receipts::facts(b[prev],c,i,j);
        if ae_ids(b[prev].nodes[i].ae).contains(j) {
            assert(!ae_ids(b[prev].nodes[i].ae).subset_of(set![i]));
            assert(quorum(ce_ids(b[prev].nodes[i].ce),c)); sessions::stable_ce(b[prev],c,a,i);
            accepted_witness(b,c,since,prev,i,j)
        } else {
            new_sender(b[prev],c,a,i,j); reveal(enabled);
            assert(b[prev].msgs[(j,i)].len() > 0); receipts::facts(b[prev],c,i,j);
            assert(quorum(ce_ids(b[prev].nodes[i].ce),c)); sessions::stable_ce(b[prev],c,a,i);
            prev
        }
    }
}
} // verus!
