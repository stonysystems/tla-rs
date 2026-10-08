//! Consuming a queued message has the same log effect as logical FIFO replay.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_sync as sync;
use super::zab_queue_math as queue;
use super::zab_queue_prefix::future;
verus! {
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn preserve(s: LState,c: Constants,a: Action,i: int,j: int)
    requires logs::inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),i != j,
        s.nodes[i].role == Role::Leading,s.nodes[i].phase == Phase::Broadcast,ae_connected(s.nodes[i].ae).contains(j),
        apply(s,c,a).nodes[i].role == Role::Leading,apply(s,c,a).nodes[i].phase == Phase::Broadcast,ae_connected(apply(s,c,a).nodes[i].ae).contains(j),
        a != Action::Broadcast(i),a != Action::AckEpoch(i,j)
    ensures future(apply(s,c,a),i,j) == future(s,i,j)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); logs::facts(s,c,i,j); connections::channel_pair(c,i,j); logs::preserve(s,c,a);
    let u=apply(s,c,a); logs::facts(u,c,i,j); sync::connected_ae(s,c,i,j); sync::connected_ae(u,c,i,j);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); logs::facts(s,c,j,x); logs::facts(s,c,j,y);
            if a == Action::Propose(x,y) { assert(!sync::pending(s.msgs[(y,x)],s.nodes[y].current,0)); }
        },
        Action::Restart(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); logs::facts(s,c,j,y); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); },
        _ => {},
    }
    let h=s.nodes[j].history; let q=s.msgs[(i,j)]; let d=u.nodes[j].history; let r=u.msgs[(i,j)];
    if r == q && d == h {}
    else if q.len() > 0 && r == q.drop_first() && d == queue::effect(h,q[0]) {}
    else {
        assert(r.len() > 0); let m=r.last();
        assert(r == q.push(m) && d == h && queue::effect(future(s,i,j),m) == future(s,i,j));
        queue::append(h,q,m);
    }
}
} // verus!
