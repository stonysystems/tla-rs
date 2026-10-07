//! Entering broadcast commits all inherited entries; later commits retain that barrier.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs as leader;
use super::zab_broadcast_commits as commits;
use super::temporal::Behavior;
verus! {
pub open spec fn barrier(n: LServer) -> bool {
    n.role == Role::Leading && n.phase == Phase::Broadcast ==>
        forall |k: int| 0 <= k < n.history.len() && (#[trigger] n.history[k]).zxid.epoch < n.current ==> k < n.committed.index
}
pub proof fn progress(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),
        b[time].nodes[i].role == Role::Leading,b[time].nodes[i].phase == Phase::Broadcast,
        b[time+1].nodes[i].role == Role::Leading,b[time+1].nodes[i].phase == Phase::Broadcast
    ensures b[time].nodes[i].committed.index <= b[time+1].nodes[i].committed.index
{
    let a=super::zab_sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; logs::at(b,c,time); logs::at(b,c,time+1);
    commits::at(b,c,time); commits::at(b,c,time+1); logs::facts(s,c,i,i); logs::facts(u,c,i,i);
    assert(commits::node(s.nodes[i])); assert(commits::node(u.nodes[i])); leader::active_step(s,c,a,i);
    reveal(enabled); reveal(apply);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y);
        },
        Action::Restart(x) => { logs::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); } },
        _ => {},
    }
    if u.nodes[i].committed.index < s.nodes[i].committed.index {
        assert(newer(u.nodes[i].committed.zxid,s.nodes[i].committed.zxid));
        let p=u.nodes[i].committed.index-1; let q=s.nodes[i].committed.index-1;
        assert(equal(s.nodes[i].history[q],u.nodes[i].history[q])); math::ordered(u.nodes[i].history,p,q);
    }
}
pub proof fn preserve(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),barrier(b[time].nodes[i])
    ensures barrier(b[time+1].nodes[i])
{
    let a=super::zab_sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; logs::at(b,c,time); logs::preserve(s,c,a);
    logs::facts(s,c,i,i); logs::facts(u,c,i,i);
    if u.nodes[i].role == Role::Leading && u.nodes[i].phase == Phase::Broadcast {
        if s.nodes[i].role == Role::Leading && s.nodes[i].phase == Phase::Broadcast {
            leader::active_step(s,c,a,i); progress(b,c,time,i);
            assert forall |k: int| 0 <= k < u.nodes[i].history.len() && (#[trigger] u.nodes[i].history[k]).zxid.epoch < u.nodes[i].current
                implies k < u.nodes[i].committed.index by {
                assert(k < s.nodes[i].history.len()); assert(equal(s.nodes[i].history[k],u.nodes[i].history[k]));
            }
        } else {
            reveal(enabled); reveal(apply);
            match a {
                Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
                    logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y);
                    if let Action::AckLd(_,_) = a { if let Message::AckLd(z)=s.msgs[(y,x)][0] { math::ack_contents(s.nodes[x].history,y,z); } }
                },
                Action::Restart(x) => { logs::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); } },
                _ => {},
            }
            assert(u.nodes[i].committed.index == u.nodes[i].history.len());
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i)
    ensures barrier(b[time].nodes[i])
    decreases time
{
    if time > 0 { at(b,c,time-1,i); preserve(b,c,time-1,i); }
}
pub proof fn integrity_at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures primary_integrity(b[time],c)
{
    let s=b[time]; super::zab_committed_prefixes::at(b,c,time); super::zab_receipt_links::at(b,c,time); logs::at(b,c,time);
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && s.nodes[i].role == Role::Leading && s.nodes[i].learners.contains(j) && s.nodes[j].role == Role::Following && s.nodes[j].leader == Some(i)
        && s.nodes[i].phase == Phase::Broadcast && s.nodes[j].phase == Phase::Broadcast && 1 <= k <= s.nodes[j].committed.index && s.nodes[j].history[k-1].zxid.epoch < s.nodes[i].current
        implies #[trigger] contains_txn(s.nodes[i],s.nodes[j].history[k-1]) by {
        logs::facts(s,c,i,j); super::zab_receipt_links::facts(s,c,i,j); super::zab_receipt_links::connected_al(s,c,i,j);
        super::zab_current_logs::at(b,c,time,j); super::zab_current_logs::aligned(b,c,time,j,i); at(b,c,time,i);
        assert(super::zab_committed_prefixes::node(b,c,time,j)); assert(equal(s.nodes[j].history[k-1],s.nodes[i].history[k-1]));
        assert(k <= s.nodes[i].committed.index); assert(equal(s.nodes[i].history[k-1],s.nodes[j].history[k-1]));
    }
}
pub proof fn benchmark_primary_integrity(b: Behavior<LState>,c: Constants)
    requires connections::safety_spec(b,c)
    ensures forall |time: int| time >= 0 ==> #[trigger] primary_integrity(b[time],c)
{
    assert forall |time: int| time >= 0 implies #[trigger] primary_integrity(b[time],c) by { integrity_at(b,c,time); }
}
} // verus!
