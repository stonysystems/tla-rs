//! Increasing log identifiers, current-epoch bounds, and valid broadcast lookup.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_epochs as epochs;
use super::zab_phases as phases;
use super::zab_receipts as receipts;
use super::zab_sync as sync;
use super::zab_log_math::{self as logs,shape,bounded};
use super::temporal::Behavior;
verus! {
pub open spec fn ae_histories(q: Set<AE>) -> bool {
    forall |r: AE| (#[trigger] q.contains(r)) ==> shape(r.history) && bounded(r.history,r.epoch)
}
pub open spec fn node(n: LServer) -> bool { shape(n.history) && bounded(n.history,n.current) && n.sent >= 0 && ae_histories(n.ae) }
pub open spec fn packet(s: LState,i: int,m: Message) -> bool {
    match m {
        Message::AckEpoch(e,h) | Message::NewLeader(e,h) => shape(h) && bounded(h,e),
        Message::Propose(z,_) => z.epoch == s.nodes[i].current && z.epoch > 0 && z.counter > 0,
        _ => true,
    }
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    sync::inductive(s,c)
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] node(s.nodes[i]))
    && (forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < s.msgs[(i,j)].len() ==> #[trigger] packet(s,i,s.msgs[(i,j)][k]))
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{
    sync::initial_inductive(c);
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < initial(c).msgs[(i,j)].len() implies #[trigger] packet(initial(c),i,initial(c).msgs[(i,j)][k]) by { connections::channel_pair(c,i,j); }
}
pub proof fn facts(s: LState,c: Constants,i: int,j: int)
    requires inductive(s,c),c.servers.contains(i),c.servers.contains(j)
    ensures node(s.nodes[i]),node(s.nodes[j]),sync::fifo(s,c,i,j),sync::fifo(s,c,j,i),
        phases::node(s.nodes[i],c,i),phases::node(s.nodes[j],c,j),epochs::node(s.nodes[i],c,i),epochs::node(s.nodes[j],c,j),connections::node(s,c,i),connections::node(s,c,j),connections::link(s,c,i,j),connections::link(s,c,j,i),
        s.msgs[(i,j)].len() > 0 ==> packet(s,i,s.msgs[(i,j)][0]) && receipts::packet(s,c,i,j,s.msgs[(i,j)][0]) && phases::packet(s,c,i,j,s.msgs[(i,j)][0]) && epochs::packet(s,c,i,j,s.msgs[(i,j)][0]) && connections::packet_link(s,i,j),
        s.msgs[(j,i)].len() > 0 ==> packet(s,j,s.msgs[(j,i)][0]) && receipts::packet(s,c,j,i,s.msgs[(j,i)][0]) && phases::packet(s,c,j,i,s.msgs[(j,i)][0]) && epochs::packet(s,c,j,i,s.msgs[(j,i)][0]) && connections::packet_link(s,j,i),
        i != j ==> c.servers.len() > 1
{ receipts::facts(s,c,i,j); }
pub proof fn disconnect_histories(q: Set<AE>,i: int)
    requires ae_histories(q)
    ensures ae_histories(disconnect_ae(q,i))
{
    if ae_ids(q).contains(i) { let old=choose |r: AE| #![trigger q.contains(r)] q.contains(r) && r.sid == i; assert(q.contains(old)); }
    assert forall |r: AE| (#[trigger] disconnect_ae(q,i).contains(r)) implies shape(r.history) && bounded(r.history,r.epoch) by {}
}
pub proof fn update_histories(q: Set<AE>,i: int,e: int,h: Seq<Txn>)
    requires ae_histories(q),shape(h),bounded(h,e)
    ensures ae_histories(update_ae(q,i,e,h))
{}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a).nodes[i])
{
    reveal(enabled); reveal(apply); facts(s,c,i,i); epochs::preserve_node(s,c,a,i);
    let u=apply(s,c,a);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            facts(s,c,x,y); facts(s,c,i,x); facts(s,c,i,y);
            disconnect_histories(s.nodes[x].ae,y); disconnect_histories(s.nodes[y].ae,x);
            let n=s.nodes[x];
            match a {
                Action::AckEpoch(_,_) => if let Message::AckEpoch(e,h)=s.msgs[(y,x)][0] {
                    update_histories(n.ae,y,e,h); epochs::preserve_node(s,c,a,x);
                    let q=update_ae(n.ae,y,e,h); assert(q.contains(AE { sid: y,connected: true,epoch: e,history: h }));
                    let chosen=collections::selected_origin(q); assert(shape(chosen.history) && bounded(chosen.history,chosen.epoch));
                    assert(chosen.epoch <= n.accepted); assert(bounded(chosen.history,n.accepted));
                    logs::ack_contents(chosen.history,x,zero()); logs::transfer(chosen.history,init_ack(chosen.history,x),n.accepted);
                },
                Action::AckLd(_,_) => if let Message::AckLd(z)=s.msgs[(y,x)][0] { logs::ack_contents(n.history,y,z); logs::transfer(n.history,update_ack(n.history,y,z),n.current); },
                Action::Ack(_,_) => if let Message::Ack(z)=s.msgs[(y,x)][0] {
                    let k=index(n.history,z); if 1 <= k <= n.history.len() {
                        let t=Txn { ack: n.history[k-1].ack.insert(y),..n.history[k-1] };
                        logs::update_contents(n.history,k-1,t); logs::transfer(n.history,n.history.update(k-1,t),n.current);
                    }
                },
                Action::Propose(_,_) => if let Message::Propose(z,v)=s.msgs[(y,x)][0] {
                    assert(!sync::pending(s.msgs[(y,x)],s.nodes[y].current,0));
                    assert(s.nodes[y].current == n.current);
                    if next_zxid(last(n.history),z) { logs::append(n.history,Txn { zxid: z,value: v,ack: Set::empty(),epoch: n.current }); }
                },
                _ => {},
            }
        },
        Action::Restart(x) => { facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { facts(s,c,x,y); facts(s,c,i,y); disconnect_histories(s.nodes[y].ae,x); } },
        Action::Request(x) => {
            facts(s,c,i,x); let n=s.nodes[x];
            let z=Zxid { epoch: n.current,counter: if n.current == last(n.history).epoch { last(n.history).counter+1 } else { 1 } };
            logs::request(n.history,n.current,Txn { zxid: z,value: c.request_value,ack: set![x],epoch: n.current });
        },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Broadcast(x) => { facts(s,c,i,x); },
        _ => {},
    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn preserve_packet(s: LState,c: Constants,a: Action,i: int,j: int,k: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),0 <= k < apply(s,c,a).msgs[(i,j)].len()
    ensures packet(apply(s,c,a),i,apply(s,c,a).msgs[(i,j)][k])
{
    hide(update_ack);
    reveal(enabled); reveal(apply); facts(s,c,i,j); connections::channel_pair(c,i,j);
    preserve_node(s,c,a,i); preserve_node(s,c,a,j); receipts::preserve(s,c,a);
    let u=apply(s,c,a);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            facts(s,c,x,y); facts(s,c,i,x); facts(s,c,i,y); facts(s,c,j,x); facts(s,c,j,y);
        },
        Action::Restart(x) => { facts(s,c,i,x); facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { facts(s,c,x,y); facts(s,c,i,y); facts(s,c,j,y); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) => { facts(s,c,i,x); facts(s,c,j,x); },
        Action::Broadcast(x) => { facts(s,c,i,x); facts(s,c,j,x); logs::broadcast_index(s.nodes[x]); },
        _ => {},
    }
    if k < s.msgs[(i,j)].len() { assert(packet(s,i,s.msgs[(i,j)][k])); assert(phases::packet(s,c,i,j,s.msgs[(i,j)][k])); }
    if k+1 < s.msgs[(i,j)].len() { assert(packet(s,i,s.msgs[(i,j)][k+1])); assert(phases::packet(s,c,i,j,s.msgs[(i,j)][k+1])); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    sync::preserve(s,c,a); let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u.nodes[i]) by { preserve_node(s,c,a,i); }
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < u.msgs[(i,j)].len() implies #[trigger] packet(u,i,u.msgs[(i,j)][k]) by { preserve_packet(s,c,a,i,j,k); }
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
