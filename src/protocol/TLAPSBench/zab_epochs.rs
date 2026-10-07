//! Epoch bounds and advertisement consistency, including disconnected receipts.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::temporal::Behavior;
verus! {
pub open spec fn node(n: LServer,c: Constants,i: int) -> bool {
    0 <= n.current <= n.accepted
    && ce_ids(n.ce).subset_of(c.servers) && ae_ids(n.ae).subset_of(c.servers) && al_ids(n.al).subset_of(c.servers)
    && (forall |r: CE| n.ce.contains(r) ==> r.epoch >= 0)
    && (forall |r: AE| n.ae.contains(r) ==> 0 <= r.epoch <= n.accepted)
    && (forall |r: CE,t: CE| n.ce.contains(r) && n.ce.contains(t) && r.sid == t.sid ==> r == t)
    && (forall |r: AE,t: AE| n.ae.contains(r) && n.ae.contains(t) && r.sid == t.sid ==> r == t)
    && (forall |r: AL,t: AL| n.al.contains(r) && n.al.contains(t) && r.sid == t.sid ==> r == t)
    && (n.role == Role::Leading ==> exists |r: CE| n.ce.contains(r) && r.sid == i && r.connected && r.epoch <= n.accepted
        && (!quorum(ce_ids(n.ce),c) ==> r.epoch == n.accepted))
}
pub open spec fn packet(s: LState,c: Constants,i: int,j: int,m: Message) -> bool {
    match m {
        Message::CEpoch(e) => s.nodes[i].role == Role::Following && s.nodes[j].role == Role::Leading && e >= 0,
        Message::NewEpoch(e) => s.nodes[i].role == Role::Leading && quorum(ce_ids(s.nodes[i].ce),c) && e == s.nodes[i].accepted,
        Message::AckEpoch(e,h) => s.nodes[j].role == Role::Leading && quorum(ce_ids(s.nodes[j].ce),c) && 0 <= e <= s.nodes[j].accepted,
        Message::NewLeader(e,h) => s.nodes[i].role == Role::Leading && quorum(ce_ids(s.nodes[i].ce),c) && e == s.nodes[i].accepted,
        _ => true,
    }
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    connections::inductive(s,c)
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] node(s.nodes[i],c,i))
    && (forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < s.msgs[(i,j)].len() ==> #[trigger] packet(s,c,i,j,s.msgs[(i,j)][k]))
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{
    connections::initial_invariant(c);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(initial(c).nodes[i],c,i) by {}
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < initial(c).msgs[(i,j)].len() implies #[trigger] packet(initial(c),c,i,j,initial(c).msgs[(i,j)][k]) by { connections::channel_pair(c,i,j); }
}
pub proof fn facts(s: LState,c: Constants,i: int,j: int)
    requires inductive(s,c),c.servers.contains(i),c.servers.contains(j)
    ensures node(s.nodes[i],c,i),node(s.nodes[j],c,j),connections::node(s,c,i),connections::node(s,c,j),connections::link(s,c,i,j),connections::link(s,c,j,i),
        s.msgs[(i,j)].len() > 0 ==> packet(s,c,i,j,s.msgs[(i,j)][0]) && connections::packet_link(s,i,j),
        s.msgs[(j,i)].len() > 0 ==> packet(s,c,j,i,s.msgs[(j,i)][0]) && connections::packet_link(s,j,i),
        i != j ==> c.servers.len() > 1
{
    connections::facts(s,c,i,j);
}
pub proof fn remove_preserves(n: LServer,c: Constants,i: int,j: int)
    requires node(n,c,i),i != j
    ensures node(LServer { ce: disconnect_ce(n.ce,j),ae: disconnect_ae(n.ae,j),al: disconnect_al(n.al,j),..n },c,i)
{
    collections::disconnect_ids(n.ce,n.ae,n.al,j);
    if ce_ids(n.ce).contains(j) { let old=choose |r: CE| n.ce.contains(r) && r.sid == j; assert(n.ce.contains(old) && old.sid == j); }
    if ae_ids(n.ae).contains(j) { let old=choose |r: AE| n.ae.contains(r) && r.sid == j; assert(n.ae.contains(old) && old.sid == j); }
    if al_ids(n.al).contains(j) { let old=choose |r: AL| n.al.contains(r) && r.sid == j; assert(n.al.contains(old) && old.sid == j); }
    if n.role == Role::Leading {
        let own=choose |r: CE| n.ce.contains(r) && r.sid == i && r.connected && r.epoch <= n.accepted && (!quorum(ce_ids(n.ce),c) ==> r.epoch == n.accepted);
        assert(disconnect_ce(n.ce,j).contains(own));
    }
    let u=LServer { ce: disconnect_ce(n.ce,j),ae: disconnect_ae(n.ae,j),al: disconnect_al(n.al,j),..n };
    assert(ce_ids(u.ce).subset_of(c.servers) && ae_ids(u.ae).subset_of(c.servers) && al_ids(u.al).subset_of(c.servers));
    assert forall |r: CE| u.ce.contains(r) implies r.epoch >= 0 by {}
    assert forall |r: AE| u.ae.contains(r) implies 0 <= r.epoch <= u.accepted by {}
    assert forall |r: CE,t: CE| u.ce.contains(r) && u.ce.contains(t) && r.sid == t.sid implies r == t by {}
    assert forall |r: AE,t: AE| u.ae.contains(r) && u.ae.contains(t) && r.sid == t.sid implies r == t by {}
    assert forall |r: AL,t: AL| u.al.contains(r) && u.al.contains(t) && r.sid == t.sid implies r == t by {}

}
pub proof fn fresh_leader(n: LServer,c: Constants,i: int)
    requires node(n,c,i),c.servers.contains(i)
    ensures node(lead(n,i),c,i)
{
    let u=lead(n,i);
    let own=CE { sid: i,connected: true,epoch: n.accepted }; assert(u.ce.contains(own));
}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a).nodes[i],c,i),s.nodes[i].accepted <= apply(s,c,a).nodes[i].accepted,
        s.nodes[i].current <= apply(s,c,a).nodes[i].current
{
    reveal(enabled); reveal(apply); facts(s,c,i,i);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            facts(s,c,x,y); facts(s,c,i,x); facts(s,c,i,y);
            collections::disconnect_ids(s.nodes[x].ce,s.nodes[x].ae,s.nodes[x].al,y);
            collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x);
            if x != y { remove_preserves(s.nodes[x],c,x,y); remove_preserves(s.nodes[y],c,y,x); }
            match a {
                Action::CEpoch(_,_) => if let Message::CEpoch(e)=s.msgs[(y,x)][0] {
                    collections::ce_update(s.nodes[x].ce,y,e);
                    let n=s.nodes[x]; let ce=update_ce(n.ce,y,e); collections::maximum_correct(ce.map(|r: CE| r.epoch));
                    assert(x != y);
                    if ce_ids(n.ce).contains(y) { let old=choose |r: CE| n.ce.contains(r) && r.sid == y; assert(n.ce.contains(old) && old.sid == y); }
                    let own=choose |r: CE| n.ce.contains(r) && r.sid == x && r.connected && r.epoch <= n.accepted && (!quorum(ce_ids(n.ce),c) ==> r.epoch == n.accepted);
                    assert(ce.contains(own)); assert(ce.map(|r: CE| r.epoch).contains(own.epoch));
                    collections::quorum_add(ce_ids(n.ce),c,y);
                    assert(s.nodes[i].accepted <= apply(s,c,a).nodes[i].accepted);
                    assert(node(apply(s,c,a).nodes[i],c,i));
                } else { assert(apply(s,c,a) == s); },
                Action::AckEpoch(_,_) => if let Message::AckEpoch(e,h)=s.msgs[(y,x)][0] { collections::ae_update(s.nodes[x].ae,y,e,h); collections::quorum_add(ae_ids(s.nodes[x].ae),c,y); assert(node(apply(s,c,a).nodes[i],c,i)); } else { assert(apply(s,c,a) == s); },
                Action::AckLd(_,_) => { collections::al_update(s.nodes[x].al,y); collections::quorum_add(al_ids(s.nodes[x].al),c,y); assert(node(apply(s,c,a).nodes[i],c,i)); },
                Action::Timeout(_,_) => { assert(node(apply(s,c,a).nodes[i],c,i)); },
                Action::NewEpoch(_,_) => { assert(node(apply(s,c,a).nodes[i],c,i)); },
                Action::NewLeader(_,_) => { assert(node(apply(s,c,a).nodes[i],c,i)); },
                _ => { assert(node(apply(s,c,a).nodes[i],c,i)); },
            }
            assert(node(apply(s,c,a).nodes[i],c,i));
        },
        Action::Restart(x) => { facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { facts(s,c,x,y); facts(s,c,i,y); collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x); remove_preserves(s.nodes[y],c,y,x); } assert(node(apply(s,c,a).nodes[i],c,i)); },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { facts(s,c,i,x); fresh_leader(s.nodes[x],c,x); assert(node(apply(s,c,a).nodes[i],c,i)); },
        _ => {},
    }
}
pub proof fn preserve_packet(s: LState,c: Constants,a: Action,i: int,j: int,k: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),0 <= k < apply(s,c,a).msgs[(i,j)].len()
    ensures packet(apply(s,c,a),c,i,j,apply(s,c,a).msgs[(i,j)][k])
{
    reveal(enabled); reveal(apply); facts(s,c,i,j); connections::channel_pair(c,i,j);
    preserve_node(s,c,a,i); preserve_node(s,c,a,j);
    let u=apply(s,c,a);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            facts(s,c,x,y); facts(s,c,i,x); facts(s,c,i,y); facts(s,c,j,x); facts(s,c,j,y);
            collections::disconnect_ids(s.nodes[x].ce,s.nodes[x].ae,s.nodes[x].al,y);
            collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x);
            if a == Action::CEpoch(x,y) { if let Message::CEpoch(e)=s.msgs[(y,x)][0] { collections::ce_update(s.nodes[x].ce,y,e); collections::quorum_add(ce_ids(s.nodes[x].ce),c,y); } }
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
    connections::preserve(s,c,a); let u=apply(s,c,a);
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
pub proof fn monotone(b: Behavior<LState>,c: Constants,left: int,right: int,i: int)
    requires connections::safety_spec(b,c),0 <= left <= right,c.servers.contains(i)
    ensures b[left].nodes[i].accepted <= b[right].nodes[i].accepted,
        b[left].nodes[i].current <= b[right].nodes[i].current
    decreases right-left
{
    if left < right {
        let time=right-1; monotone(b,c,left,time,i); at(b,c,time);
        assert(next(b[time],b[time+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[time],c,a) && b[time+1] == apply(b[time],c,a);
        preserve_node(b[time],c,a,i);
    }
}
} // verus!
