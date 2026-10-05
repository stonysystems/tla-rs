//! An active leader only extends its log during one leadership interval.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_phases as phases;
use super::zab_receipts as receipts;
use super::zab_sessions::{self as sessions,interval};
use super::zab_epoch_origins as origins;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::temporal::Behavior;
verus! {
pub open spec fn prefix(a: Seq<Txn>,b: Seq<Txn>) -> bool {
    a.len() <= b.len() && forall |k: int| 0 <= k < a.len() ==> #[trigger] equal(a[k],b[k])
}
pub proof fn transitive(a: Seq<Txn>,b: Seq<Txn>,d: Seq<Txn>)
    requires prefix(a,b),prefix(b,d)
    ensures prefix(a,d)
{
    assert forall |k: int| 0 <= k < a.len() implies #[trigger] equal(a[k],d[k]) by { assert(equal(a[k],b[k]) && equal(b[k],d[k])); }
}
pub open spec fn epoch_prefix(a: Seq<Txn>,b: Seq<Txn>,e: int) -> bool {
    prefix(a,b) && forall |k: int| a.len() <= k < b.len() ==> (#[trigger] b[k]).zxid.epoch == e
}
pub proof fn epoch_transitive(a: Seq<Txn>,b: Seq<Txn>,d: Seq<Txn>,e: int)
    requires epoch_prefix(a,b,e),epoch_prefix(b,d,e)
    ensures epoch_prefix(a,d,e)
{
    transitive(a,b,d);
    assert forall |k: int| a.len() <= k < d.len() implies (#[trigger] d[k]).zxid.epoch == e by {
        if k < b.len() { assert(b[k].zxid.epoch == e && equal(b[k],d[k])); }
    }
}
pub proof fn append_position(a: Seq<Txn>,b: Seq<Txn>,e: int,p: int)
    requires math::shape(a),math::shape(b),epoch_prefix(a,b,e),0 <= p < b.len(),b[p].zxid.epoch == e,next_zxid(last(a),b[p].zxid)
    ensures p == a.len()
{
    let old=a.len() as int-1;
    assert(equal(a[old],b[old]));
    if p <= old { math::ordered(b,p,old); assert(false); }
    if p > a.len() {
        let first=a.len() as int;
        assert(next_zxid(b[first-1].zxid,b[first].zxid)); assert(b[first].zxid.epoch == e);
        assert(b[first].zxid == b[p].zxid); math::ordered(b,first,p); assert(false);
    }
}
pub proof fn append_prefix(a: Seq<Txn>,b: Seq<Txn>,e: int,p: int,t: Txn)
    requires math::shape(a),math::shape(b),epoch_prefix(a,b,e),0 <= p < b.len(),equal(t,b[p]),t.zxid.epoch == e,next_zxid(last(a),t.zxid)
    ensures epoch_prefix(a.push(t),b,e)
{
    append_position(a,b,e,p);
    assert forall |k: int| 0 <= k < a.push(t).len() implies #[trigger] equal(a.push(t)[k],b[k]) by { if k < a.len() { assert(equal(a[k],b[k])); } }
}
pub proof fn active_step(s: LState,c: Constants,a: Action,i: int)
    requires logs::inductive(s,c),enabled(s,c,a),c.servers.contains(i),
        s.nodes[i].role == Role::Leading,s.nodes[i].phase != Phase::Discovery,apply(s,c,a).nodes[i].role == Role::Leading
    ensures apply(s,c,a).nodes[i].phase != Phase::Discovery,
        apply(s,c,a).nodes[i].current == s.nodes[i].current,epoch_prefix(s.nodes[i].history,apply(s,c,a).nodes[i].history,s.nodes[i].current)
{
    reveal(enabled); reveal(apply); logs::facts(s,c,i,i);
    receipts::preserve(s,c,a); phases::facts(apply(s,c,a),c,i,i);
    sessions::stable_ce(s,c,a,i);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y);
            collections::disconnect_ids(s.nodes[x].ce,s.nodes[x].ae,s.nodes[x].al,y); collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x);
            let n=s.nodes[x];
            match a {
                Action::AckEpoch(_,_) => if let Message::AckEpoch(e,h)=s.msgs[(y,x)][0] {
                    collections::ae_update(n.ae,y,e,h); collections::quorum_add(ae_ids(n.ae),c,y);
                },
                Action::AckLd(_,_) => if let Message::AckLd(z)=s.msgs[(y,x)][0] { math::ack_contents(n.history,y,z); },
                Action::Ack(_,_) => if let Message::Ack(z)=s.msgs[(y,x)][0] {
                    let k=index(n.history,z); if 1 <= k <= n.history.len() {
                        let t=Txn { ack: n.history[k-1].ack.insert(y),..n.history[k-1] }; math::update_contents(n.history,k-1,t);
                    }
                },
                _ => {},
            }
        },
        Action::Restart(x) => { logs::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { logs::facts(s,c,i,x); },
        _ => {},
    }
}
pub proof fn active_interval(b: Behavior<LState>,c: Constants,i: int,left: int,right: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),interval(b,i,left,right),b[left].nodes[i].phase != Phase::Discovery
    ensures b[right].nodes[i].phase != Phase::Discovery,b[right].nodes[i].current == b[left].nodes[i].current,
        epoch_prefix(b[left].nodes[i].history,b[right].nodes[i].history,b[left].nodes[i].current)
    decreases right-left
{
    if left < right {
        let prev=right-1; active_interval(b,c,i,left,prev); let a=sessions::step(b,c,prev); logs::at(b,c,prev);
        active_step(b[prev],c,a,i); epoch_transitive(b[left].nodes[i].history,b[prev].nodes[i].history,b[right].nodes[i].history,b[left].nodes[i].current);
    }
}
pub proof fn same_epoch(b: Behavior<LState>,c: Constants,i: int,left: int,right: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),0 <= left <= right,
        b[left].nodes[i].role == Role::Leading,b[right].nodes[i].role == Role::Leading,
        b[left].nodes[i].phase != Phase::Discovery,b[right].nodes[i].phase != Phase::Discovery,
        b[left].nodes[i].current == b[right].nodes[i].current
    ensures interval(b,i,left,right),epoch_prefix(b[left].nodes[i].history,b[right].nodes[i].history,b[left].nodes[i].current)
{
    origins::same_session(b,c,i,left,right); active_interval(b,c,i,left,right);
}
pub proof fn fresh_activation(b: Behavior<LState>,c: Constants,time: int,i: int,seen: int,node: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),c.servers.contains(node),0 <= seen <= time,
        b[time].nodes[i].phase == Phase::Discovery,b[time+1].nodes[i].role == Role::Leading,b[time+1].nodes[i].phase != Phase::Discovery
    ensures b[seen].nodes[node].current != b[time+1].nodes[i].current
{
    phases::at(b,c,time+1); phases::facts(b[time+1],c,i,i);
    if b[seen].nodes[node].current == b[time+1].nodes[i].current {
        let w=origins::current_origin(b,c,seen,node);
        super::zab_elections::unique(b,c,w.0,w.1,time+1,i);
        origins::same_session(b,c,i,w.0,time+1);
        active_interval(b,c,i,w.0,time); assert(false);
    }
}
} // verus!
