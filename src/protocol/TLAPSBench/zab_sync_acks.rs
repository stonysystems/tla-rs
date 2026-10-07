//! During synchronization, every AL receipt acknowledges the whole selected history.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::temporal::Behavior;
verus! {
pub open spec fn all_acked(n: LServer) -> bool {
    forall |k: int| 0 <= k < n.history.len() ==> al_ids(n.al).subset_of((#[trigger] n.history[k]).ack)
}
pub open spec fn node(n: LServer) -> bool {
    n.role == Role::Leading && n.phase == Phase::Synchronization ==> all_acked(n)
}
pub open spec fn packet(s: LState,i: int,j: int,m: Message) -> bool {
    match m {
        Message::NewLeader(_,h) => s.nodes[i].phase == Phase::Synchronization ==> math::same(h,s.nodes[i].history),
        Message::AckLd(z) => s.nodes[j].phase == Phase::Synchronization ==> z == last(s.nodes[j].history),
        _ => true,
    }
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    logs::inductive(s,c)
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] node(s.nodes[i]))
    && (forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < s.msgs[(i,j)].len() ==> #[trigger] packet(s,i,j,s.msgs[(i,j)][k]))
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{
    logs::initial_inductive(c);
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < initial(c).msgs[(i,j)].len()
        implies #[trigger] packet(initial(c),i,j,initial(c).msgs[(i,j)][k]) by { connections::channel_pair(c,i,j); }
}
pub proof fn ackld_all(s: LState,c: Constants,i: int,j: int)
    requires inductive(s,c),enabled(s,c,Action::AckLd(i,j)),s.nodes[i].phase == Phase::Synchronization
    ensures all_acked(apply(s,c,Action::AckLd(i,j)).nodes[i])
{
    reveal(enabled); reveal(apply); logs::facts(s,c,i,j); let n=s.nodes[i]; assert(node(n));
    assert(packet(s,j,i,s.msgs[(j,i)][0]));
    if let Message::AckLd(z)=s.msgs[(j,i)][0] {
        let p=n.history.len() as int-1; assert(n.history[p].zxid == z); math::ack_prefix(n.history,j,p); collections::al_update(n.al,j);
        let u=apply(s,c,Action::AckLd(i,j)).nodes[i];
        assert forall |k: int| 0 <= k < u.history.len() implies al_ids(u.al).subset_of((#[trigger] u.history[k]).ack) by {
            assert(al_ids(n.al).subset_of(n.history[k].ack));
        }
    }
}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a).nodes[i])
{
    reveal(enabled); reveal(apply); logs::facts(s,c,i,i); assert(node(s.nodes[i]));
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y);
            collections::disconnect_ids(s.nodes[x].ce,s.nodes[x].ae,s.nodes[x].al,y); collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x);
            if a == Action::AckLd(x,y) && s.nodes[x].phase == Phase::Synchronization { ackld_all(s,c,x,y); }
        },
        Action::Restart(x) => { logs::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { logs::facts(s,c,i,x); },
        _ => {},
    }
}
pub proof fn preserve_packet(s: LState,c: Constants,a: Action,i: int,j: int,k: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),0 <= k < apply(s,c,a).msgs[(i,j)].len()
    ensures packet(apply(s,c,a),i,j,apply(s,c,a).msgs[(i,j)][k])
{
    reveal(enabled); reveal(apply); logs::facts(s,c,i,j); connections::channel_pair(c,i,j);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); logs::facts(s,c,j,x); logs::facts(s,c,j,y);
            let n=s.nodes[x];
            match a {
                Action::NewLeader(_,_) => if let Message::NewLeader(e,h)=s.msgs[(y,x)][0] {
                    assert(packet(s,y,x,s.msgs[(y,x)][0]));
                    if s.nodes[y].phase == Phase::Synchronization { math::same_last(h,s.nodes[y].history); }
                },
                Action::AckLd(_,_) => if let Message::AckLd(z)=s.msgs[(y,x)][0] { math::ack_contents(n.history,y,z); math::same_last(n.history,update_ack(n.history,y,z)); },
                Action::Ack(_,_) => if let Message::Ack(z)=s.msgs[(y,x)][0] {
                    let p=index(n.history,z)-1;
                    if 0 <= p < n.history.len() {
                        let t=Txn { ack: n.history[p].ack.insert(y),..n.history[p] }; math::update_contents(n.history,p,t); math::same_last(n.history,n.history.update(p,t));
                    }
                },
                _ => {},
            }
        },
        Action::Restart(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); logs::facts(s,c,j,y); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); },
        _ => {},
    }
    if k < s.msgs[(i,j)].len() { assert(packet(s,i,j,s.msgs[(i,j)][k])); assert(super::zab_phases::packet(s,c,i,j,s.msgs[(i,j)][k])); }
    if k+1 < s.msgs[(i,j)].len() { assert(packet(s,i,j,s.msgs[(i,j)][k+1])); assert(super::zab_phases::packet(s,c,i,j,s.msgs[(i,j)][k+1])); }
    let u=apply(s,c,a);
    if let Message::NewLeader(e,h)=u.msgs[(i,j)][k] {
        if u.nodes[i].phase == Phase::Synchronization {
            assert forall |p: int| 0 <= p < h.len() implies #[trigger] super::zab::equal(h[p],u.nodes[i].history[p]) by {
                if s.nodes[i].phase == Phase::Synchronization { assert(super::zab::equal(h[p],s.nodes[i].history[p])); }
            }
        }
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    logs::preserve(s,c,a); let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u.nodes[i]) by { preserve_node(s,c,a,i); }
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < u.msgs[(i,j)].len()
        implies #[trigger] packet(u,i,j,u.msgs[(i,j)][k]) by { preserve_packet(s,c,a,i,j,k); }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures inductive(b[time],c)
    decreases time
{
    if time == 0 { initial_inductive(c); }
    else { at(b,c,time-1); let a=super::zab_sessions::step(b,c,time-1); preserve(b[time-1],c,a); }
}
} // verus!
