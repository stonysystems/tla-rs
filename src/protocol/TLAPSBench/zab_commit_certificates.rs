//! Each new leader commitment is backed by a quorum of actual stored prefixes.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_sync_acks as sync;
use super::zab_ack_certificates as acks;
use super::zab_sessions as sessions;
use super::temporal::Behavior;
verus! {
pub open spec fn certified(b: Behavior<LState>,c: Constants,time: int,e: int,h: Seq<Txn>,k: int) -> bool {
    exists |i: int,q: Set<int>| c.servers.contains(i) && quorum(q,c)
        && forall |j: int| q.contains(j) ==> #[trigger] acks::certificate(b,c,time,i,e,h,k,j)
}
pub proof fn quorum_certificate(b: Behavior<LState>,c: Constants,time: int,i: int,k: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),b[time].nodes[i].role == Role::Leading,b[time].nodes[i].phase != Phase::Discovery,
        0 <= k < b[time].nodes[i].history.len(),quorum(b[time].nodes[i].history[k].ack,c)
    ensures certified(b,c,time,b[time].nodes[i].current,b[time].nodes[i].history,k)
{
    acks::at(b,c,time); let n=b[time].nodes[i]; let q=n.history[k].ack;
    assert forall |j: int| q.contains(j) implies #[trigger] acks::certificate(b,c,time,i,n.current,n.history,k,j) by {}
}
pub proof fn new_commit(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),
        b[time+1].nodes[i].role == Role::Leading,b[time+1].nodes[i].phase != Phase::Discovery,
        b[time+1].nodes[i].committed != b[time].nodes[i].committed
    ensures 1 <= b[time+1].nodes[i].committed.index <= b[time+1].nodes[i].history.len(),
        b[time+1].nodes[i].history[b[time+1].nodes[i].committed.index-1].zxid == b[time+1].nodes[i].committed.zxid,
        quorum(b[time+1].nodes[i].history[b[time+1].nodes[i].committed.index-1].ack,c),
        certified(b,c,time+1,b[time+1].nodes[i].current,b[time+1].nodes[i].history,b[time+1].nodes[i].committed.index-1)
{
    let a=sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; sync::at(b,c,time); logs::preserve(s,c,a);
    logs::facts(s,c,i,i); logs::facts(u,c,i,i); reveal(enabled); reveal(apply);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); logs::facts(u,c,x,y);
            match a {
                Action::AckLd(_,_) => {
                    assert(x == i && s.nodes[i].phase == Phase::Synchronization);
                    sync::ackld_all(s,c,i,y); let k=u.nodes[i].history.len() as int-1;
                    acks::domain(b,c,time+1,i,k);
                    assert(al_ids(u.nodes[i].al).subset_of(u.nodes[i].history[k].ack));
                    collections::quorum_superset(al_ids(u.nodes[i].al),u.nodes[i].history[k].ack,c);
                },
                Action::Ack(_,_) => if let Message::Ack(z)=s.msgs[(y,x)][0] {
                    assert(x == i && 1 <= index(s.nodes[i].history,z) <= s.nodes[i].history.len()); math::lookup(s.nodes[i].history,z);
                },
                _ => { assert(false); },
            }
        },
        Action::Restart(x) => {
            logs::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); }
            assert(false);
        },
        _ => { assert(false); },
    }
    quorum_certificate(b,c,time+1,i,u.nodes[i].committed.index-1);
}
} // verus!
