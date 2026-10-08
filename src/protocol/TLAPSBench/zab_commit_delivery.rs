//! FIFO prefixes deliver the log entry named by each synchronization commit.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_sync as sync;
use super::zab_receipt_links as links;
use super::zab_queue_math as queue;
use super::zab_future_commits as future;
use super::temporal::Behavior;
verus! {
pub open spec fn position(s: LState,i: int,j: int,p: int) -> bool {
    match s.msgs[(i,j)][p] {
        Message::CommitLd(z) => {
            let h=queue::replay(s.nodes[j].history,s.msgs[(i,j)].take(p));
            1 <= index(h,z) <= h.len()
        },
        _ => true,
    }
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < s.msgs[(i,j)].len() ==> #[trigger] position(s,i,j,p)
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{
    assert forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < initial(c).msgs[(i,j)].len()
        implies #[trigger] position(initial(c),i,j,p) by { connections::channel_pair(c,i,j); }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn transport(s: LState,c: Constants,a: Action,i: int,j: int,p: int)
    requires logs::inductive(s,c),links::inductive(s,c),logs::inductive(apply(s,c,a),c),links::inductive(apply(s,c,a),c),enabled(s,c,a),
        c.servers.contains(i),c.servers.contains(j),0 <= p < apply(s,c,a).msgs[(i,j)].len(),apply(s,c,a).msgs[(i,j)][p] is CommitLd
    ensures {
        let u=apply(s,c,a); let h=s.nodes[j].history; let q=s.msgs[(i,j)]; let d=u.nodes[j].history; let r=u.msgs[(i,j)];
        (r == q && d == h) || (q.len() > 0 && r == q.drop_first() && d == queue::effect(h,q[0])) || (r == q.push(r.last()) && d == h)
    },
{
    hide(update_ack);
    let u=apply(s,c,a); logs::facts(s,c,i,j); logs::facts(u,c,i,j); links::facts(s,c,i,j); links::facts(u,c,i,j); connections::channel_pair(c,i,j);
    assert(super::zab_phases::packet(u,c,i,j,u.msgs[(i,j)][p])); assert(links::packet(u,i,j,u.msgs[(i,j)][p])); links::connected_al(u,c,i,j);
        reveal(enabled); reveal(apply);
        match a {
            Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
                logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); logs::facts(s,c,j,x); logs::facts(s,c,j,y); links::facts(s,c,x,y);
                if a == Action::Propose(x,y) { assert(!sync::pending(s.msgs[(y,x)],s.nodes[y].current,0)); }
            },
            Action::Restart(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); logs::facts(s,c,j,y); } },
            Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); },
            _ => {},
        }
}
#[verifier::spinoff_prover]
pub proof fn created(s: LState,c: Constants,a: Action,i: int,j: int,z: Zxid)
    requires logs::inductive(s,c),links::inductive(s,c),logs::inductive(apply(s,c,a),c),links::inductive(apply(s,c,a),c),enabled(s,c,a),
        c.servers.contains(i),c.servers.contains(j),apply(s,c,a).msgs[(i,j)] == s.msgs[(i,j)].push(Message::CommitLd(z))
    ensures i != j,ae_connected(s.nodes[i].ae).contains(j),s.nodes[i].role == Role::Leading,
        (s.nodes[i].phase == Phase::Synchronization && z == last(s.nodes[i].history)) || (s.nodes[i].phase == Phase::Broadcast && z == s.nodes[i].committed.zxid)
{
    hide(update_ack);
    let u=apply(s,c,a); logs::facts(s,c,i,j); logs::facts(u,c,i,j); links::facts(s,c,i,j); connections::channel_pair(c,i,j); reveal(enabled); reveal(apply);
    assert(u.msgs[(i,j)].len() == s.msgs[(i,j)].len()+1); assert(u.msgs[(i,j)].last() == Message::CommitLd(z));
    assert(links::packet(u,i,j,u.msgs[(i,j)][u.msgs[(i,j)].len() as int-1]));
    assert(super::zab_phases::packet(u,c,i,j,u.msgs[(i,j)][u.msgs[(i,j)].len() as int-1])); links::connected_al(u,c,i,j);
        match a {
            Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
                logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); logs::facts(s,c,j,x); logs::facts(s,c,j,y); links::facts(s,c,x,y);
                if a == Action::Propose(x,y) { assert(!sync::pending(s.msgs[(y,x)],s.nodes[y].current,0)); }
            },
            Action::Restart(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); logs::facts(s,c,j,y); } },
            Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); },
            _ => {},
        }
    assert(exists |y: int| a == Action::AckLd(i,y)); let y=choose |y: int| a == Action::AckLd(i,y);
    logs::facts(s,c,i,y); links::facts(s,c,i,y); links::updates(s.nodes[i].ae,s.nodes[i].al,y,0,Seq::empty());
    assert(links::packet(u,i,j,u.msgs[(i,j)][u.msgs[(i,j)].len() as int-1]));
    assert(super::zab_phases::packet(u,c,i,j,u.msgs[(i,j)][u.msgs[(i,j)].len() as int-1])); links::connected_al(u,c,i,j);
}
pub proof fn preserve_position(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,p: int)
    requires connections::safety_spec(b,c),time >= 0,inductive(b[time],c),c.servers.contains(i),c.servers.contains(j),0 <= p < b[time+1].msgs[(i,j)].len()
    ensures position(b[time+1],i,j,p)
{
    let a=super::zab_sessions::step(b,c,time); let s=b[time]; let u=b[time+1];
    logs::at(b,c,time); logs::preserve(s,c,a); links::at(b,c,time); links::preserve(s,c,a);
    logs::facts(s,c,i,j); logs::facts(u,c,i,j); links::facts(s,c,i,j); links::facts(u,c,i,j); connections::channel_pair(c,i,j);
    if let Message::CommitLd(z)=u.msgs[(i,j)][p] {
        assert(super::zab_phases::packet(u,c,i,j,u.msgs[(i,j)][p]));
        assert(links::packet(u,i,j,u.msgs[(i,j)][p])); links::connected_al(u,c,i,j);
        transport(s,c,a,i,j,p);
        let h=s.nodes[j].history; let q=s.msgs[(i,j)]; let d=u.nodes[j].history; let r=u.msgs[(i,j)];
        if r == q && d == h { assert(position(s,i,j,p)); }
        else if q.len() > 0 && r == q.drop_first() && d == queue::effect(h,q[0]) {
            assert(position(s,i,j,p+1)); queue::take_step(h,q,p);
        } else {
            assert(r.len() > 0); let m=r.last(); assert(r == q.push(m) && d == h);
            if p < q.len() { assert(position(s,i,j,p)); assert(r.take(p) =~= q.take(p)); }
            else {
                assert(p == q.len() && m == Message::CommitLd(z)); assert(r.take(p) =~= q);
                created(s,c,a,i,j,z);
                if s.nodes[i].phase == Phase::Synchronization { future::synchronizing(b,c,time,i,j); }
                else { assert(s.nodes[i].phase == Phase::Broadcast); future::broadcasting(b,c,time,i,j); }
            }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures inductive(b[time],c)
    decreases time
{
    if time == 0 { initial_inductive(c); }
    else {
        at(b,c,time-1);
        assert forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < b[time].msgs[(i,j)].len()
            implies #[trigger] position(b[time],i,j,p) by { preserve_position(b,c,time-1,i,j,p); }
    }
}
pub proof fn head(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,z: Zxid)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),b[time].msgs[(i,j)].len() > 0,b[time].msgs[(i,j)][0] == Message::CommitLd(z)
    ensures 1 <= index(b[time].nodes[j].history,z) <= b[time].nodes[j].history.len()
{
    at(b,c,time); assert(position(b[time],i,j,0)); assert(b[time].msgs[(i,j)].take(0) =~= Seq::<Message>::empty());
}
} // verus!
