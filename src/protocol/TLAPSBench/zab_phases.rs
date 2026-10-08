//! Phase transitions justified by receipt quorums and queued message kinds.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_epochs as epochs;
use super::temporal::Behavior;
verus! {
pub open spec fn node(n: LServer,c: Constants,i: int) -> bool {
    n.role == Role::Leading ==> {
        &&& ae_ids(n.ae).contains(i) && al_ids(n.al).contains(i)
        &&& (ae_ids(n.ae).subset_of(set![i]) || quorum(ce_ids(n.ce),c))
        &&& (al_ids(n.al).subset_of(set![i]) || quorum(ae_ids(n.ae),c))
        &&& (quorum(ae_ids(n.ae),c) ==> quorum(ce_ids(n.ce),c))
        &&& (quorum(al_ids(n.al),c) ==> quorum(ae_ids(n.ae),c))
        &&& (n.phase == Phase::Discovery <==> c.servers.len() <= 1 || !quorum(ae_ids(n.ae),c))
        &&& (n.phase == Phase::Synchronization <==> c.servers.len() > 1 && quorum(ae_ids(n.ae),c) && !quorum(al_ids(n.al),c))
        &&& (n.phase == Phase::Broadcast <==> c.servers.len() > 1 && quorum(al_ids(n.al),c))
        &&& (n.phase != Phase::Discovery ==> n.current == n.accepted)
        &&& (c.servers.len() > 1 && quorum(ce_ids(n.ce),c) ==> n.accepted > 0)
    }
}
pub open spec fn packet(s: LState,c: Constants,i: int,j: int,m: Message) -> bool {
    match m {
        Message::NewLeader(_,_) => s.nodes[i].role == Role::Leading && quorum(ae_ids(s.nodes[i].ae),c),
        Message::AckLd(_) => s.nodes[j].role == Role::Leading && quorum(ae_ids(s.nodes[j].ae),c),
        Message::CommitLd(_) | Message::Propose(_,_) | Message::Commit(_) => s.nodes[i].role == Role::Leading && s.nodes[i].phase == Phase::Broadcast,
        Message::Ack(_) => s.nodes[j].role == Role::Leading && s.nodes[j].phase == Phase::Broadcast,
        _ => true,
    }
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    epochs::inductive(s,c)
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] node(s.nodes[i],c,i))
    && (forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < s.msgs[(i,j)].len() ==> #[trigger] packet(s,c,i,j,s.msgs[(i,j)][k]))
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{
    epochs::initial_inductive(c);
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < initial(c).msgs[(i,j)].len() implies #[trigger] packet(initial(c),c,i,j,initial(c).msgs[(i,j)][k]) by { connections::channel_pair(c,i,j); }
}
pub proof fn facts(s: LState,c: Constants,i: int,j: int)
    requires inductive(s,c),c.servers.contains(i),c.servers.contains(j)
    ensures node(s.nodes[i],c,i),node(s.nodes[j],c,j),epochs::node(s.nodes[i],c,i),epochs::node(s.nodes[j],c,j),connections::node(s,c,i),connections::node(s,c,j),connections::link(s,c,i,j),connections::link(s,c,j,i),
        s.msgs[(i,j)].len() > 0 ==> packet(s,c,i,j,s.msgs[(i,j)][0]) && epochs::packet(s,c,i,j,s.msgs[(i,j)][0]) && connections::packet_link(s,i,j),
        s.msgs[(j,i)].len() > 0 ==> packet(s,c,j,i,s.msgs[(j,i)][0]) && epochs::packet(s,c,j,i,s.msgs[(j,i)][0]) && connections::packet_link(s,j,i),
        i != j ==> c.servers.len() > 1
{
    epochs::facts(s,c,i,j);
}
pub proof fn fresh(n: LServer,c: Constants,i: int)
    requires c.servers.contains(i)
    ensures node(lead(n,i),c,i)
{
    let u=lead(n,i);
    assert(u.ce.contains(CE { sid: i,connected: true,epoch: n.accepted }));
    assert(u.ae.contains(AE { sid: i,connected: true,epoch: n.current,history: n.history }));
    assert(u.al.contains(AL { sid: i,connected: true }));
    assert(ce_ids(u.ce).contains(i)); assert(ae_ids(u.ae).contains(i)); assert(al_ids(u.al).contains(i));
    assert(ce_ids(u.ce) =~= set![i]); assert(ae_ids(u.ae) =~= set![i]); assert(al_ids(u.al) =~= set![i]);
}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a).nodes[i],c,i)
{
    reveal(enabled); reveal(apply); facts(s,c,i,i); epochs::preserve_node(s,c,a,i);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            facts(s,c,x,y); facts(s,c,i,x); facts(s,c,i,y);
            collections::disconnect_ids(s.nodes[x].ce,s.nodes[x].ae,s.nodes[x].al,y);
            collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x);
            match a {
                Action::CEpoch(_,_) => if let Message::CEpoch(e)=s.msgs[(y,x)][0] {
                    collections::ce_update(s.nodes[x].ce,y,e); collections::quorum_add(ce_ids(s.nodes[x].ce),c,y);
                    let ce=update_ce(s.nodes[x].ce,y,e); let r=CE { sid: y,connected: true,epoch: e };
                    assert(ce.contains(r)); assert(ce.map(|r: CE| r.epoch).contains(e)); collections::maximum_correct(ce.map(|r: CE| r.epoch));
                },
                Action::AckEpoch(_,_) => if let Message::AckEpoch(e,h)=s.msgs[(y,x)][0] { collections::ae_update(s.nodes[x].ae,y,e,h); collections::quorum_add(ae_ids(s.nodes[x].ae),c,y); },
                Action::AckLd(_,_) => { collections::al_update(s.nodes[x].al,y); collections::quorum_add(al_ids(s.nodes[x].al),c,y); },
                _ => {},
            }
        },
        Action::Restart(x) => { facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { facts(s,c,x,y); facts(s,c,i,y); collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { facts(s,c,i,x); fresh(s.nodes[x],c,x); },
        _ => {},
    }
}
#[verifier::spinoff_prover]
pub proof fn preserve_packet(s: LState,c: Constants,a: Action,i: int,j: int,k: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),0 <= k < apply(s,c,a).msgs[(i,j)].len()
    ensures packet(apply(s,c,a),c,i,j,apply(s,c,a).msgs[(i,j)][k])
{
    hide(update_ack);
    reveal(enabled); reveal(apply); facts(s,c,i,j); connections::channel_pair(c,i,j);
    preserve_node(s,c,a,i); preserve_node(s,c,a,j);
    let u=apply(s,c,a);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            facts(s,c,x,y); facts(s,c,i,x); facts(s,c,i,y); facts(s,c,j,x); facts(s,c,j,y);
            collections::disconnect_ids(s.nodes[x].ce,s.nodes[x].ae,s.nodes[x].al,y);
            collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x);
            if a == Action::AckEpoch(x,y) { if let Message::AckEpoch(e,h)=s.msgs[(y,x)][0] { collections::ae_update(s.nodes[x].ae,y,e,h); collections::quorum_add(ae_ids(s.nodes[x].ae),c,y); } }
            if a == Action::AckLd(x,y) { collections::al_update(s.nodes[x].al,y); collections::quorum_add(al_ids(s.nodes[x].al),c,y); }
        },
        Action::Restart(x) => { facts(s,c,i,x); facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { facts(s,c,x,y); facts(s,c,i,y); facts(s,c,j,y); collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { facts(s,c,i,x); facts(s,c,j,x); },
        _ => {},
    }
    if k < s.msgs[(i,j)].len() { assert(packet(s,c,i,j,s.msgs[(i,j)][k])); }
    if k+1 < s.msgs[(i,j)].len() { assert(packet(s,c,i,j,s.msgs[(i,j)][k+1])); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    epochs::preserve(s,c,a); let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u.nodes[i],c,i) by { preserve_node(s,c,a,i); }
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < u.msgs[(i,j)].len() implies #[trigger] packet(u,c,i,j,u.msgs[(i,j)][k]) by { preserve_packet(s,c,a,i,j,k); }
}
pub proof fn at(b: Behavior<LState>,c: Constants,k: int)
    requires connections::safety_spec(b,c),k >= 0
    ensures inductive(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c); }
    else {
        at(b,c,k-1); let time=k-1; assert(next(b[time],b[time+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[time],c,a) && b[time+1] == apply(b[time],c,a);
        preserve(b[time],c,a);
    }
}
} // verus!
