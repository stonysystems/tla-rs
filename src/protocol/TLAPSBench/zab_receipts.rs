//! Receipt epochs remain bounded by their senders, including after disconnect.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_epochs as epochs;
use super::zab_phases as phases;
use super::temporal::Behavior;
verus! {
pub open spec fn receipt(s: LState,c: Constants,i: int,j: int) -> bool {
    let n=s.nodes[i]; let peer=s.nodes[j];
    &&& (forall |r: CE| #![trigger n.ce.contains(r)] n.ce.contains(r) && r.sid == j ==> r.epoch <= peer.accepted
        && (n.role == Role::Leading && r.connected ==> n.learners.contains(j)))
    &&& (forall |r: AE| #![trigger n.ae.contains(r)] n.ae.contains(r) && r.sid == j ==> r.epoch <= peer.current
        && (n.role == Role::Leading && r.connected ==> n.learners.contains(j) && peer.accepted == n.accepted))
    &&& (forall |r: AL| #![trigger n.al.contains(r)] n.al.contains(r) && r.sid == j && n.role == Role::Leading && r.connected ==>
        n.learners.contains(j) && peer.accepted == n.accepted && peer.current == n.current)
}
pub open spec fn packet(s: LState,c: Constants,i: int,j: int,m: Message) -> bool {
    match m {
        Message::CEpoch(e) => e <= s.nodes[i].accepted,
        Message::AckEpoch(e,_) => e <= s.nodes[i].current && s.nodes[i].accepted == s.nodes[j].accepted,
        Message::NewLeader(_,_) => s.nodes[i].accepted == s.nodes[j].accepted,
        Message::AckLd(_) => s.nodes[i].current == s.nodes[j].current && s.nodes[i].accepted == s.nodes[j].accepted,
        _ => true,
    }
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    phases::inductive(s,c)
    && (forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] receipt(s,c,i,j))
    && (forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < s.msgs[(i,j)].len() ==> #[trigger] packet(s,c,i,j,s.msgs[(i,j)][k]))
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{
    phases::initial_inductive(c);
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < initial(c).msgs[(i,j)].len() implies #[trigger] packet(initial(c),c,i,j,initial(c).msgs[(i,j)][k]) by { connections::channel_pair(c,i,j); }
}
pub proof fn facts(s: LState,c: Constants,i: int,j: int)
    requires inductive(s,c),c.servers.contains(i),c.servers.contains(j)
    ensures receipt(s,c,i,j),receipt(s,c,j,i),phases::node(s.nodes[i],c,i),phases::node(s.nodes[j],c,j),epochs::node(s.nodes[i],c,i),epochs::node(s.nodes[j],c,j),connections::node(s,c,i),connections::node(s,c,j),connections::link(s,c,i,j),connections::link(s,c,j,i),
        s.msgs[(i,j)].len() > 0 ==> packet(s,c,i,j,s.msgs[(i,j)][0]) && phases::packet(s,c,i,j,s.msgs[(i,j)][0]) && epochs::packet(s,c,i,j,s.msgs[(i,j)][0]) && connections::packet_link(s,i,j),
        s.msgs[(j,i)].len() > 0 ==> packet(s,c,j,i,s.msgs[(j,i)][0]) && phases::packet(s,c,j,i,s.msgs[(j,i)][0]) && epochs::packet(s,c,j,i,s.msgs[(j,i)][0]) && connections::packet_link(s,j,i),
        i != j ==> c.servers.len() > 1
{
    phases::facts(s,c,i,j);
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn preserve_receipt(s: LState,c: Constants,a: Action,i: int,j: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j)
    ensures receipt(apply(s,c,a),c,i,j)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); facts(s,c,i,j);
    collections::record_ids(s.nodes[i]); collections::record_ids(apply(s,c,a).nodes[i]);
    epochs::preserve_node(s,c,a,i); epochs::preserve_node(s,c,a,j);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            facts(s,c,x,y); facts(s,c,i,x); facts(s,c,i,y); facts(s,c,j,x); facts(s,c,j,y);
            if a == Action::CEpoch(x,y) { if let Message::CEpoch(e)=s.msgs[(y,x)][0] { collections::ce_update(s.nodes[x].ce,y,e); } }
            if a == Action::AckEpoch(x,y) { if let Message::AckEpoch(e,h)=s.msgs[(y,x)][0] { collections::ae_update(s.nodes[x].ae,y,e,h); } }
            if a == Action::AckLd(x,y) { collections::al_update(s.nodes[x].al,y); }
            collections::record_ids(s.nodes[x]); collections::record_ids(s.nodes[y]);
            match a {
                Action::CEpoch(_,_) => { assert(receipt(apply(s,c,a),c,i,j)); },
                Action::AckEpoch(_,_) => { assert(receipt(apply(s,c,a),c,i,j)); },
                Action::AckLd(_,_) => { assert(receipt(apply(s,c,a),c,i,j)); },
                Action::Timeout(_,_) => { assert(receipt(apply(s,c,a),c,i,j)); },
                Action::NewEpoch(_,_) => { assert(receipt(apply(s,c,a),c,i,j)); },
                Action::NewLeader(_,_) => { assert(receipt(apply(s,c,a),c,i,j)); },
                _ => { assert(receipt(apply(s,c,a),c,i,j)); },
            }
        },
        Action::Restart(x) => { facts(s,c,i,x); facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { facts(s,c,x,y); facts(s,c,i,y); facts(s,c,j,y); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { facts(s,c,i,x); facts(s,c,j,x); },
        _ => {},
    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn preserve_packet(s: LState,c: Constants,a: Action,i: int,j: int,k: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),0 <= k < apply(s,c,a).msgs[(i,j)].len()
    ensures packet(apply(s,c,a),c,i,j,apply(s,c,a).msgs[(i,j)][k])
{
    hide(update_ack);
    reveal(enabled); reveal(apply); facts(s,c,i,j); connections::channel_pair(c,i,j);
    epochs::preserve_node(s,c,a,i); epochs::preserve_node(s,c,a,j);
    preserve_receipt(s,c,a,i,j);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            facts(s,c,x,y); facts(s,c,i,x); facts(s,c,i,y); facts(s,c,j,x); facts(s,c,j,y);
        },
        Action::Restart(x) => { facts(s,c,i,x); facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { facts(s,c,x,y); facts(s,c,i,y); facts(s,c,j,y); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { facts(s,c,i,x); facts(s,c,j,x); },
        _ => {},
    }
    if k < s.msgs[(i,j)].len() { assert(packet(s,c,i,j,s.msgs[(i,j)][k])); assert(phases::packet(s,c,i,j,s.msgs[(i,j)][k])); assert(epochs::packet(s,c,i,j,s.msgs[(i,j)][k])); }
    if k+1 < s.msgs[(i,j)].len() { assert(packet(s,c,i,j,s.msgs[(i,j)][k+1])); assert(phases::packet(s,c,i,j,s.msgs[(i,j)][k+1])); assert(epochs::packet(s,c,i,j,s.msgs[(i,j)][k+1])); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    phases::preserve(s,c,a); let u=apply(s,c,a);
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] receipt(u,c,i,j) by { preserve_receipt(s,c,a,i,j); }
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
