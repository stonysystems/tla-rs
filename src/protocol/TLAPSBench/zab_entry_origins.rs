//! Every log-entry prefix traces to the active leader that generated its epoch.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs::{self as leader,prefix};
use super::zab_proposal_logs as proposals;
use super::zab_current_logs as current;
use super::zab_sessions as sessions;
use super::temporal::Behavior;
verus! {
pub open spec fn through(a: Seq<Txn>,d: Seq<Txn>,k: int) -> bool {
    0 <= k < a.len() && k < d.len() && forall |p: int| 0 <= p <= k ==> #[trigger] equal(a[p],d[p])
}
pub open spec fn origin(b: Behavior<LState>,c: Constants,time: int,h: Seq<Txn>,k: int,w: (int,int)) -> bool {
    0 <= w.0 <= time && c.servers.contains(w.1) && b[w.0].nodes[w.1].role == Role::Leading && b[w.0].nodes[w.1].phase != Phase::Discovery
    && b[w.0].nodes[w.1].current == h[k].zxid.epoch && through(h,b[w.0].nodes[w.1].history,k)
}
pub open spec fn entry(b: Behavior<LState>,c: Constants,time: int,h: Seq<Txn>,k: int) -> bool {
    h[k].zxid.epoch >= 0
    && (h[k].zxid.epoch == 0 ==> k == 0 && h[k].zxid == boot() && h[k].value == 0)
    && (h[k].zxid.epoch > 0 ==> exists |w: (int,int)| #[trigger] origin(b,c,time,h,k,w))
}
pub open spec fn images(b: Behavior<LState>,c: Constants,time: int,h: Seq<Txn>) -> bool {
    forall |k: int| 0 <= k < h.len() ==> #[trigger] entry(b,c,time,h,k)
}
pub proof fn copy_entry(b: Behavior<LState>,c: Constants,old: int,time: int,a: Seq<Txn>,d: Seq<Txn>,k: int)
    requires old <= time,entry(b,c,old,a,k),through(a,d,k)
    ensures entry(b,c,time,d,k)
{
    assert(equal(a[k],d[k]));
    if a[k].zxid.epoch > 0 {
        let w=choose |w: (int,int)| origin(b,c,old,a,k,w);
        assert(through(d,b[w.0].nodes[w.1].history,k)) by {
            assert forall |p: int| 0 <= p <= k implies #[trigger] equal(d[p],b[w.0].nodes[w.1].history[p]) by {
                assert(equal(a[p],d[p])); assert(equal(a[p],b[w.0].nodes[w.1].history[p]));
            }
        }
        assert(origin(b,c,time,d,k,w));
    }
}
pub proof fn copy(b: Behavior<LState>,c: Constants,old: int,time: int,a: Seq<Txn>,d: Seq<Txn>)
    requires old <= time,images(b,c,old,a),prefix(d,a)
    ensures images(b,c,time,d)
{
    assert forall |k: int| 0 <= k < d.len() implies #[trigger] entry(b,c,time,d,k) by {
        assert(through(a,d,k)) by { assert forall |p: int| 0 <= p <= k implies #[trigger] equal(a[p],d[p]) by { assert(equal(d[p],a[p])); } }
        copy_entry(b,c,old,time,a,d,k);
    }
}
pub proof fn same_copy(b: Behavior<LState>,c: Constants,old: int,time: int,a: Seq<Txn>,d: Seq<Txn>)
    requires old <= time,images(b,c,old,a),math::same(a,d)
    ensures images(b,c,time,d)
{
    assert(prefix(d,a)) by { assert forall |k: int| 0 <= k < d.len() implies #[trigger] equal(d[k],a[k]) by { assert(equal(a[k],d[k])); } }
    copy(b,c,old,time,a,d);
}
pub proof fn append(b: Behavior<LState>,c: Constants,time: int,h: Seq<Txn>,t: Txn,w: (int,int))
    requires images(b,c,time,h),t.zxid.epoch > 0,origin(b,c,time+1,h.push(t),h.len() as int,w)
    ensures images(b,c,time+1,h.push(t))
{
    let d=h.push(t);
    assert forall |k: int| 0 <= k < d.len() implies #[trigger] entry(b,c,time+1,d,k) by {
        if k < h.len() { copy_entry(b,c,time,time+1,h,d,k); }
    }
}
pub open spec fn ae_images(b: Behavior<LState>,c: Constants,time: int,q: Set<AE>) -> bool {
    forall |r: AE| (#[trigger] q.contains(r)) ==> images(b,c,time,r.history)
}
pub open spec fn node(b: Behavior<LState>,c: Constants,time: int,n: LServer) -> bool {
    images(b,c,time,n.history) && ae_images(b,c,time,n.ae)
}
pub open spec fn packet(b: Behavior<LState>,c: Constants,time: int,m: Message) -> bool {
    match m { Message::AckEpoch(_,h) | Message::NewLeader(_,h) => images(b,c,time,h),_ => true }
}
pub open spec fn inductive(b: Behavior<LState>,c: Constants,time: int) -> bool {
    (forall |i: int| c.servers.contains(i) ==> #[trigger] node(b,c,time,b[time].nodes[i]))
    && (forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < b[time].msgs[(i,j)].len() ==> #[trigger] packet(b,c,time,b[time].msgs[(i,j)][k]))
}
pub proof fn advance_node(b: Behavior<LState>,c: Constants,time: int,n: LServer)
    requires node(b,c,time,n)
    ensures node(b,c,time+1,n)
{
    copy(b,c,time,time+1,n.history,n.history);
    assert forall |r: AE| (#[trigger] n.ae.contains(r)) implies images(b,c,time+1,r.history) by { copy(b,c,time,time+1,r.history,r.history); }
}
pub proof fn advance_packet(b: Behavior<LState>,c: Constants,time: int,m: Message)
    requires packet(b,c,time,m)
    ensures packet(b,c,time+1,m)
{
    match m { Message::AckEpoch(_,h) | Message::NewLeader(_,h) => copy(b,c,time,time+1,h,h),_ => {} }
}
pub proof fn facts(b: Behavior<LState>,c: Constants,time: int,i: int,j: int)
    requires inductive(b,c,time),c.servers.contains(i),c.servers.contains(j)
    ensures node(b,c,time,b[time].nodes[i]),node(b,c,time,b[time].nodes[j]),
        b[time].msgs[(i,j)].len() > 0 ==> packet(b,c,time,b[time].msgs[(i,j)][0]),
        b[time].msgs[(j,i)].len() > 0 ==> packet(b,c,time,b[time].msgs[(j,i)][0])
{}
pub proof fn disconnect(b: Behavior<LState>,c: Constants,time: int,q: Set<AE>,i: int)
    requires ae_images(b,c,time,q)
    ensures ae_images(b,c,time,disconnect_ae(q,i))
{
    if ae_ids(q).contains(i) { let old=choose |r: AE| q.contains(r) && r.sid == i; assert(q.contains(old)); }
    assert forall |r: AE| (#[trigger] disconnect_ae(q,i).contains(r)) implies images(b,c,time,r.history) by {}
}
pub proof fn update(b: Behavior<LState>,c: Constants,time: int,q: Set<AE>,i: int,e: int,h: Seq<Txn>)
    requires ae_images(b,c,time,q),images(b,c,time,h)
    ensures ae_images(b,c,time,update_ae(q,i,e,h))
{}
pub proof fn initial_inductive(b: Behavior<LState>,c: Constants)
    requires connections::safety_spec(b,c)
    ensures inductive(b,c,0)
{
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(b,c,0,b[0].nodes[i]) by {}
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < b[0].msgs[(i,j)].len() implies #[trigger] packet(b,c,0,b[0].msgs[(i,j)][k]) by { connections::channel_pair(c,i,j); }
}
pub proof fn preserve_node(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),inductive(b,c,time)
    ensures node(b,c,time+1,b[time+1].nodes[i])
{
    let a=sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; proposals::at(b,c,time); logs::preserve(s,c,a);
    logs::facts(s,c,i,i); logs::facts(u,c,i,i); facts(b,c,time,i,i); advance_node(b,c,time,s.nodes[i]);
    reveal(enabled); reveal(apply);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); logs::facts(u,c,x,y); facts(b,c,time,x,y);
            advance_node(b,c,time,s.nodes[x]); advance_node(b,c,time,s.nodes[y]);
            disconnect(b,c,time+1,s.nodes[x].ae,y); disconnect(b,c,time+1,s.nodes[y].ae,x);
            if s.msgs[(y,x)].len() > 0 { advance_packet(b,c,time,s.msgs[(y,x)][0]); }
            let n=s.nodes[x];
            match a {
                Action::AckEpoch(_,_) => if let Message::AckEpoch(e,h)=s.msgs[(y,x)][0] {
                    update(b,c,time+1,n.ae,y,e,h); let q=update_ae(n.ae,y,e,h);
                    assert(q.contains(AE { sid: y,connected: true,epoch: e,history: h })); let r=collections::selected_origin(q);
                    math::ack_contents(r.history,x,zero()); same_copy(b,c,time+1,time+1,r.history,init_ack(r.history,x));
                },
                Action::AckLd(_,_) => if let Message::AckLd(z)=s.msgs[(y,x)][0] {
                    math::ack_contents(n.history,y,z); same_copy(b,c,time,time+1,n.history,update_ack(n.history,y,z));
                },
                Action::Ack(_,_) => if let Message::Ack(z)=s.msgs[(y,x)][0] {
                    let k=index(n.history,z); if 1 <= k <= n.history.len() {
                        let t=Txn { ack: n.history[k-1].ack.insert(y),..n.history[k-1] }; math::update_contents(n.history,k-1,t);
                        same_copy(b,c,time,time+1,n.history,n.history.update(k-1,t));
                    }
                },
                Action::Propose(_,_) => if let Message::Propose(z,v)=s.msgs[(y,x)][0] {
                    if next_zxid(last(n.history),z) {
                        assert(!super::zab_sync::pending(s.msgs[(y,x)],s.nodes[y].current,0));
                        assert(n.current == s.nodes[y].current && n.current > 0);
                        current::at(b,c,time,x); current::aligned(b,c,time,x,y);
                        assert(proposals::packet(s.nodes[y].history,s.nodes[y].current,s.msgs[(y,x)][0]));
                        let p=choose |p: int| 0 <= p < s.nodes[y].history.len() && s.nodes[y].history[p].zxid == z && s.nodes[y].history[p].value == v;
                        let t=Txn { zxid: z,value: v,ack: Set::empty(),epoch: n.current };
                        leader::append_prefix(n.history,s.nodes[y].history,n.current,p,t);
                        assert(origin(b,c,time+1,n.history.push(t),n.history.len() as int,(time,y)));
                        append(b,c,time,n.history,t,(time,y));
                    }
                },
                _ => {},
            }
        },
        Action::Restart(x) => {
            logs::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader {
                logs::facts(s,c,x,y); logs::facts(s,c,i,y); facts(b,c,time,x,y); advance_node(b,c,time,s.nodes[y]); disconnect(b,c,time+1,s.nodes[y].ae,x);
            }
        },
        Action::Request(x) => {
            logs::facts(s,c,i,x); logs::facts(u,c,x,x); facts(b,c,time,x,x); let n=s.nodes[x];
            let z=Zxid { epoch: n.current,counter: if n.current == last(n.history).epoch { last(n.history).counter+1 } else { 1 } };
            let t=Txn { zxid: z,value: c.request_value,ack: set![x],epoch: n.current };
            assert(origin(b,c,time+1,n.history.push(t),n.history.len() as int,(time+1,x))); append(b,c,time,n.history,t,(time+1,x));
        },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Broadcast(x) => { logs::facts(s,c,i,x); facts(b,c,time,x,x); advance_node(b,c,time,s.nodes[x]); },
        _ => {},
    }
}
pub proof fn preserve_packet(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,k: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),inductive(b,c,time),0 <= k < b[time+1].msgs[(i,j)].len()
    ensures packet(b,c,time+1,b[time+1].msgs[(i,j)][k])
{
    let a=sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; proposals::at(b,c,time);
    logs::facts(s,c,i,j); facts(b,c,time,i,j); connections::channel_pair(c,i,j); reveal(enabled); reveal(apply);
    match a {
        Action::AckEpoch(x,y) | Action::NewEpoch(x,y) => {
            facts(b,c,time,x,y); advance_node(b,c,time,s.nodes[x]); preserve_node(b,c,time,x);
        },
        _ => {},
    }
    if k < s.msgs[(i,j)].len() { advance_packet(b,c,time,s.msgs[(i,j)][k]); }
    if k+1 < s.msgs[(i,j)].len() { advance_packet(b,c,time,s.msgs[(i,j)][k+1]); }
}
pub proof fn preserve(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0,inductive(b,c,time)
    ensures inductive(b,c,time+1)
{
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(b,c,time+1,b[time+1].nodes[i]) by { preserve_node(b,c,time,i); }
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < b[time+1].msgs[(i,j)].len()
        implies #[trigger] packet(b,c,time+1,b[time+1].msgs[(i,j)][k]) by { preserve_packet(b,c,time,i,j,k); }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures inductive(b,c,time)
    decreases time
{
    if time == 0 { initial_inductive(b,c); }
    else { at(b,c,time-1); preserve(b,c,time-1); }
}
} // verus!
