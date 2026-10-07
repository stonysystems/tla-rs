//! A broadcasting leader advertises an existing entry covered by its broadcast counter.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs as leader;
use super::zab_sent_messages as sent;
use super::zab_sync_history as sync;
use super::zab_commit_certificates as commits;
use super::zab_sessions as sessions;
use super::temporal::Behavior;
verus! {
pub open spec fn sent_or_old(z: Zxid,e: int,sent: int) -> bool { z.epoch < e || z.epoch == e && z.counter <= sent }
pub open spec fn node(n: LServer) -> bool {
    n.role == Role::Leading && n.phase == Phase::Broadcast ==>
        1 <= n.committed.index <= n.history.len() && n.history[n.committed.index-1].zxid == n.committed.zxid && sent_or_old(n.committed.zxid,n.current,n.sent)
}
pub open spec fn inductive(b: Behavior<LState>,c: Constants,time: int) -> bool {
    forall |i: int| c.servers.contains(i) ==> #[trigger] node(b[time].nodes[i])
}
pub proof fn initial_inductive(b: Behavior<LState>,c: Constants)
    requires connections::safety_spec(b,c)
    ensures inductive(b,c,0)
{}
pub proof fn preserve_node(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),inductive(b,c,time)
    ensures node(b[time+1].nodes[i])
{
    let a=sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; sent::at(b,c,time); sent::preserve(s,c,a);
    logs::facts(s,c,i,i); logs::facts(u,c,i,i); assert(node(s.nodes[i])); reveal(enabled); reveal(apply);
    if u.nodes[i].role == Role::Leading && u.nodes[i].phase == Phase::Broadcast {
        match a {
            Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
                logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y);
            },
            Action::Restart(x) => { logs::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); } },
            _ => {},
        }
        if s.nodes[i].role == Role::Leading && s.nodes[i].phase == Phase::Broadcast {
            leader::active_step(s,c,a,i); assert(u.nodes[i].sent >= s.nodes[i].sent);
            if u.nodes[i].committed == s.nodes[i].committed {
                let p=s.nodes[i].committed.index-1; assert(equal(s.nodes[i].history[p],u.nodes[i].history[p]));
            } else {
                commits::new_commit(b,c,time,i);
                assert(exists |j: int| a == Action::Ack(i,j)); let j=choose |j: int| a == Action::Ack(i,j);
                assert(sent::packet(s,j,i,s.msgs[(j,i)][0]));
            }
        } else {
            assert(exists |j: int| a == Action::AckLd(i,j)); let j=choose |j: int| a == Action::AckLd(i,j);
            logs::facts(s,c,i,j); assert(s.nodes[i].phase == Phase::Synchronization); sync::at(b,c,time,i);
            if let Message::AckLd(z)=s.msgs[(j,i)][0] {
                math::ack_contents(s.nodes[i].history,j,z); math::same_last(s.nodes[i].history,u.nodes[i].history);
                assert(s.nodes[i].history[s.nodes[i].history.len() as int-1].zxid.epoch < s.nodes[i].current);
            }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures inductive(b,c,time)
    decreases time
{
    if time == 0 { initial_inductive(b,c); }
    else {
        let prev=time-1; at(b,c,prev);
        assert forall |i: int| c.servers.contains(i) implies #[trigger] node(b[time].nodes[i]) by { preserve_node(b,c,prev,i); }
    }
}
} // verus!
