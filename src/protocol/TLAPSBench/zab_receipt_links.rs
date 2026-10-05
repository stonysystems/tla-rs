//! Connected synchronization receipts and their in-flight messages retain epoch receipts.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_receipts as receipts;
use super::temporal::Behavior;
verus! {
pub proof fn updates(ae: Set<AE>,al: Set<AL>,i: int,e: int,h: Seq<Txn>)
    ensures ae_connected(update_ae(ae,i,e,h)) =~= ae_connected(ae).insert(i),al_connected(update_al(al,i)) =~= al_connected(al).insert(i)
{
    if ae_ids(ae).contains(i) { let old=choose |r: AE| ae.contains(r) && r.sid == i; assert(ae.contains(old) && old.sid == i); }
    if al_ids(al).contains(i) { let old=choose |r: AL| al.contains(r) && r.sid == i; assert(al.contains(old) && old.sid == i); }
    assert forall |j: int| ae_connected(update_ae(ae,i,e,h)).contains(j) <==> ae_connected(ae).insert(i).contains(j) by {
        if j == i { let r=AE { sid: i,connected: true,epoch: e,history: h }; assert(update_ae(ae,i,e,h).filter(|r: AE| r.connected).contains(r)); }
        else if ae_connected(ae).contains(j) {
            let r=choose |r: AE| ae.contains(r) && r.connected && r.sid == j;
            assert(update_ae(ae,i,e,h).filter(|r: AE| r.connected).contains(r));
        }
        if ae_connected(update_ae(ae,i,e,h)).contains(j) && j != i {
            let r=choose |r: AE| update_ae(ae,i,e,h).contains(r) && r.connected && r.sid == j;
            assert(ae.filter(|r: AE| r.connected).contains(r));
        }
    }
    assert forall |j: int| al_connected(update_al(al,i)).contains(j) <==> al_connected(al).insert(i).contains(j) by {
        if j == i { let r=AL { sid: i,connected: true }; assert(update_al(al,i).filter(|r: AL| r.connected).contains(r)); }
        else if al_connected(al).contains(j) {
            let r=choose |r: AL| al.contains(r) && r.connected && r.sid == j;
            assert(update_al(al,i).filter(|r: AL| r.connected).contains(r));
        }
        if al_connected(update_al(al,i)).contains(j) && j != i {
            let r=choose |r: AL| update_al(al,i).contains(r) && r.connected && r.sid == j;
            assert(al.filter(|r: AL| r.connected).contains(r));
        }
    }
}
pub proof fn disconnect(ae: Set<AE>,al: Set<AL>,i: int)
    requires forall |r: AE,t: AE| ae.contains(r) && ae.contains(t) && r.sid == t.sid ==> r == t,
        forall |r: AL,t: AL| al.contains(r) && al.contains(t) && r.sid == t.sid ==> r == t
    ensures ae_connected(disconnect_ae(ae,i)) =~= ae_connected(ae).remove(i),al_connected(disconnect_al(al,i)) =~= al_connected(al).remove(i)
{
    if ae_ids(ae).contains(i) { let old=choose |r: AE| ae.contains(r) && r.sid == i; assert(ae.contains(old) && old.sid == i); }
    if al_ids(al).contains(i) { let old=choose |r: AL| al.contains(r) && r.sid == i; assert(al.contains(old) && old.sid == i); }
    assert forall |j: int| ae_connected(disconnect_ae(ae,i)).contains(j) <==> ae_connected(ae).remove(i).contains(j) by {
        if j != i && ae_connected(ae).contains(j) {
            let r=choose |r: AE| ae.contains(r) && r.connected && r.sid == j;
            assert(disconnect_ae(ae,i).filter(|r: AE| r.connected).contains(r));
        }
        if ae_connected(disconnect_ae(ae,i)).contains(j) {
            let r=choose |r: AE| disconnect_ae(ae,i).contains(r) && r.connected && r.sid == j;
            assert(ae.filter(|r: AE| r.connected).contains(r));
            if j == i { let old=choose |r: AE| ae.contains(r) && r.sid == i; assert(r == old); assert(false); }
        }
    }
    assert forall |j: int| al_connected(disconnect_al(al,i)).contains(j) <==> al_connected(al).remove(i).contains(j) by {
        if j != i && al_connected(al).contains(j) {
            let r=choose |r: AL| al.contains(r) && r.connected && r.sid == j;
            assert(disconnect_al(al,i).filter(|r: AL| r.connected).contains(r));
        }
        if al_connected(disconnect_al(al,i)).contains(j) {
            let r=choose |r: AL| disconnect_al(al,i).contains(r) && r.connected && r.sid == j;
            assert(al.filter(|r: AL| r.connected).contains(r));
            if j == i { let old=choose |r: AL| al.contains(r) && r.sid == i; assert(r == old); assert(false); }
        }
    }
}
pub proof fn fresh(n: LServer,i: int)
    ensures ae_connected(lead(n,i).ae) =~= set![i],al_connected(lead(n,i).al) =~= set![i]
{
    let ae=AE { sid: i,connected: true,epoch: n.current,history: n.history }; let al=AL { sid: i,connected: true };
    assert(lead(n,i).ae.filter(|r: AE| r.connected).contains(ae)); assert(lead(n,i).al.filter(|r: AL| r.connected).contains(al));
}
pub open spec fn relation(s: LState,i: int,j: int) -> bool {
    (s.nodes[i].role == Role::Leading && al_connected(s.nodes[i].al).contains(j) ==> ae_connected(s.nodes[i].ae).contains(j))
    && (s.nodes[j].role == Role::Following && s.nodes[j].phase == Phase::Broadcast && s.nodes[j].leader == Some(i) ==> al_connected(s.nodes[i].al).contains(j))
}
pub open spec fn packet(s: LState,i: int,j: int,m: Message) -> bool {
    match m {
        Message::NewLeader(_,_) | Message::Propose(_,_) => ae_connected(s.nodes[i].ae).contains(j),
        Message::AckLd(_) | Message::Ack(_) => ae_connected(s.nodes[j].ae).contains(i),
        Message::CommitLd(_) | Message::Commit(_) => al_connected(s.nodes[i].al).contains(j),
        _ => true,
    }
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    receipts::inductive(s,c)
    && (forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] relation(s,i,j))
    && (forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < s.msgs[(i,j)].len() ==> #[trigger] packet(s,i,j,s.msgs[(i,j)][k]))
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{
    receipts::initial_inductive(c);
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < initial(c).msgs[(i,j)].len()
        implies #[trigger] packet(initial(c),i,j,initial(c).msgs[(i,j)][k]) by { connections::channel_pair(c,i,j); }
}
pub proof fn facts(s: LState,c: Constants,i: int,j: int)
    requires inductive(s,c),c.servers.contains(i),c.servers.contains(j)
    ensures relation(s,i,j),relation(s,j,i),
        s.msgs[(i,j)].len() > 0 ==> packet(s,i,j,s.msgs[(i,j)][0]),s.msgs[(j,i)].len() > 0 ==> packet(s,j,i,s.msgs[(j,i)][0])
{}
pub proof fn preserve_relation(s: LState,c: Constants,a: Action,i: int,j: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j)
    ensures relation(apply(s,c,a),i,j)
{
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,j); facts(s,c,i,j);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            receipts::facts(s,c,x,y); receipts::facts(s,c,i,x); receipts::facts(s,c,i,y); receipts::facts(s,c,j,x); receipts::facts(s,c,j,y); facts(s,c,x,y);
            disconnect(s.nodes[x].ae,s.nodes[x].al,y); disconnect(s.nodes[y].ae,s.nodes[y].al,x);
            if a == Action::AckLd(x,y) { updates(s.nodes[x].ae,s.nodes[x].al,y,0,Seq::empty()); }
            if a == Action::AckEpoch(x,y) { if let Message::AckEpoch(e,h)=s.msgs[(y,x)][0] { updates(s.nodes[x].ae,s.nodes[x].al,y,e,h); } }
        },
        Action::Restart(x) => { receipts::facts(s,c,i,x); receipts::facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { receipts::facts(s,c,x,y); receipts::facts(s,c,i,y); receipts::facts(s,c,j,y); disconnect(s.nodes[y].ae,s.nodes[y].al,x); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) => { receipts::facts(s,c,i,x); receipts::facts(s,c,j,x); fresh(s.nodes[x],x); },
        _ => {},
    }
}
pub proof fn preserve_packet(s: LState,c: Constants,a: Action,i: int,j: int,k: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),0 <= k < apply(s,c,a).msgs[(i,j)].len()
    ensures packet(apply(s,c,a),i,j,apply(s,c,a).msgs[(i,j)][k])
{
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,j); facts(s,c,i,j); connections::channel_pair(c,i,j);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            receipts::facts(s,c,x,y); receipts::facts(s,c,i,x); receipts::facts(s,c,i,y); receipts::facts(s,c,j,x); receipts::facts(s,c,j,y); facts(s,c,x,y);
            disconnect(s.nodes[x].ae,s.nodes[x].al,y); disconnect(s.nodes[y].ae,s.nodes[y].al,x);
            if a == Action::AckLd(x,y) { updates(s.nodes[x].ae,s.nodes[x].al,y,0,Seq::empty()); }
            if a == Action::AckEpoch(x,y) { if let Message::AckEpoch(e,h)=s.msgs[(y,x)][0] { updates(s.nodes[x].ae,s.nodes[x].al,y,e,h); } }
        },
        Action::Restart(x) => { receipts::facts(s,c,i,x); receipts::facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { receipts::facts(s,c,x,y); receipts::facts(s,c,i,y); receipts::facts(s,c,j,y); disconnect(s.nodes[y].ae,s.nodes[y].al,x); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) => { receipts::facts(s,c,i,x); receipts::facts(s,c,j,x); fresh(s.nodes[x],x); },
        Action::Request(x) | Action::Broadcast(x) => { receipts::facts(s,c,i,x); receipts::facts(s,c,j,x); },
        _ => {},
    }
    if k < s.msgs[(i,j)].len() { assert(packet(s,i,j,s.msgs[(i,j)][k])); assert(super::zab_phases::packet(s,c,i,j,s.msgs[(i,j)][k])); assert(super::zab_epochs::packet(s,c,i,j,s.msgs[(i,j)][k])); }
    if k+1 < s.msgs[(i,j)].len() { assert(packet(s,i,j,s.msgs[(i,j)][k+1])); assert(super::zab_phases::packet(s,c,i,j,s.msgs[(i,j)][k+1])); assert(super::zab_epochs::packet(s,c,i,j,s.msgs[(i,j)][k+1])); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    receipts::preserve(s,c,a); let u=apply(s,c,a);
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] relation(u,i,j) by { preserve_relation(s,c,a,i,j); }
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
pub proof fn connected_al(s: LState,c: Constants,i: int,j: int)
    requires inductive(s,c),c.servers.contains(i),c.servers.contains(j),s.nodes[i].role == Role::Leading,al_connected(s.nodes[i].al).contains(j)
    ensures ae_connected(s.nodes[i].ae).contains(j),s.nodes[i].learners.contains(j),s.nodes[j].current == s.nodes[i].current,s.nodes[j].accepted == s.nodes[i].accepted
{
    receipts::facts(s,c,i,j); facts(s,c,i,j);
    let r=choose |r: AL| s.nodes[i].al.contains(r) && r.connected && r.sid == j; assert(s.nodes[i].al.contains(r) && r.connected && r.sid == j);
}
} // verus!
