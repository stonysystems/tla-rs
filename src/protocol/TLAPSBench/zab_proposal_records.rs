//! An entry absent from passive proposal records can only be its epoch owner's local request.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::temporal::Behavior;
verus! {
pub open spec fn owned(b: Behavior<LState>,time: int,i: int,e: int,read: int) -> bool {
    0 <= read <= time && b[read].nodes[i].role == Role::Leading && b[read].nodes[i].phase == Phase::Broadcast && b[read].nodes[i].current == e
}
pub open spec fn entry(b: Behavior<LState>,time: int,i: int,k: int) -> bool {
    let s=b[time]; let n=s.nodes[i]; proposed(s,n.history[k])
    || (n.history[k].zxid.epoch == n.current && exists |read: int| #[trigger] owned(b,time,i,n.current,read))
}
pub open spec fn all(s: LState,h: Seq<Txn>) -> bool { forall |k: int| 0 <= k < h.len() ==> #[trigger] proposed(s,h[k]) }
pub open spec fn packet(s: LState,m: Message) -> bool {
    match m {
        Message::NewLeader(_,h) => all(s,h),
        Message::Propose(z,v) => proposed(s,Txn { zxid: z,value: v,ack: Set::empty(),epoch: 0 }),
        _ => true,
    }
}
pub open spec fn inductive(b: Behavior<LState>,c: Constants,time: int) -> bool {
    (forall |i: int,k: int| c.servers.contains(i) && 0 <= k < b[time].nodes[i].history.len() ==> #[trigger] entry(b,time,i,k))
    && (forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < b[time].msgs[(i,j)].len()
        ==> #[trigger] packet(b[time],b[time].msgs[(i,j)][p]))
}
pub proof fn monotone(s: LState,c: Constants,a: Action)
    ensures s.proposals.subset_of(apply(s,c,a).proposals)
{ reveal(apply); }
pub proof fn proposed_copy(s: LState,u: LState,a: Txn,d: Txn)
    requires s.proposals.subset_of(u.proposals),proposed(s,a),equal(a,d)
    ensures proposed(u,d)
{
    let p=choose |p: Proposal| #![trigger s.proposals.contains(p)] s.proposals.contains(p) && p.zxid == a.zxid && p.value == a.value; assert(u.proposals.contains(p));
}
pub proof fn records_entry(s: LState,i: int,e: int,h: Seq<Txn>,k: int)
    requires 0 <= k < h.len(),records(i,e,h).subset_of(s.proposals)
    ensures proposed(s,h[k])
{
    let p=Proposal { source: i,epoch: e,zxid: h[k].zxid,value: h[k].value }; assert(Set::range(0,h.len() as int).contains(k)); assert(records(i,e,h).contains(p)); assert(s.proposals.contains(p));
}
pub proof fn advance_packet(s: LState,u: LState,m: Message)
    requires s.proposals.subset_of(u.proposals),packet(s,m)
    ensures packet(u,m)
{
    if let Message::NewLeader(_,h)=m {
        assert forall |k: int| 0 <= k < h.len() implies #[trigger] proposed(u,h[k]) by { proposed_copy(s,u,h[k],h[k]); }
    } else if let Message::Propose(z,v)=m { let t=Txn { zxid: z,value: v,ack: Set::empty(),epoch: 0 }; proposed_copy(s,u,t,t); }
}
pub proof fn initial_inductive(b: Behavior<LState>,c: Constants)
    requires connections::safety_spec(b,c)
    ensures inductive(b,c,0)
{
    assert forall |i: int,k: int| c.servers.contains(i) && 0 <= k < b[0].nodes[i].history.len() implies #[trigger] entry(b,0,i,k) by {
        let p=Proposal { source: i,epoch: 0,zxid: boot(),value: 0 }; assert(b[0].proposals.contains(p));
    }
    assert forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < b[0].msgs[(i,j)].len()
        implies #[trigger] packet(b[0],b[0].msgs[(i,j)][p]) by { connections::channel_pair(c,i,j); }
}
pub proof fn advance_entry(b: Behavior<LState>,time: int,i: int,k: int)
    requires entry(b,time,i,k),equal(b[time].nodes[i].history[k],b[time+1].nodes[i].history[k]),b[time].nodes[i].current == b[time+1].nodes[i].current,
        b[time].proposals.subset_of(b[time+1].proposals)
    ensures entry(b,time+1,i,k)
{
    let n=b[time].nodes[i]; let d=b[time+1].nodes[i];
    if proposed(b[time],n.history[k]) { proposed_copy(b[time],b[time+1],n.history[k],d.history[k]); }
    else { let read=choose |read: int| owned(b,time,i,n.current,read); assert(owned(b,time+1,i,d.current,read)); }
}
#[verifier::spinoff_prover]
pub proof fn preserve_entry(b: Behavior<LState>,c: Constants,time: int,i: int,k: int)
    requires connections::safety_spec(b,c),time >= 0,inductive(b,c,time),c.servers.contains(i),0 <= k < b[time+1].nodes[i].history.len()
    ensures entry(b,time+1,i,k)
{
    hide(update_ack);
    let a=super::zab_sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; logs::at(b,c,time); logs::preserve(s,c,a); monotone(s,c,a);
    logs::facts(s,c,i,i); logs::facts(u,c,i,i); reveal(enabled); reveal(apply);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); let n=s.nodes[x];
            match a {
                Action::AckEpoch(_,_) => if x == i && (n.current != u.nodes[i].current || !math::same(n.history,u.nodes[i].history)) {
                    assert(records(i,n.accepted,u.nodes[i].history).subset_of(u.proposals)); records_entry(u,i,n.accepted,u.nodes[i].history,k);
                },
                Action::NewLeader(_,_) => if let Message::NewLeader(e,h)=s.msgs[(y,x)][0] {
                    if x == i && n.accepted == e { assert(packet(s,s.msgs[(y,x)][0])); assert(proposed(s,h[k])); proposed_copy(s,u,h[k],u.nodes[i].history[k]); }
                },
                Action::Propose(_,_) => if let Message::Propose(z,v)=s.msgs[(y,x)][0] {
                    if x == i && k == n.history.len() { assert(packet(s,s.msgs[(y,x)][0])); let t=Txn { zxid: z,value: v,ack: Set::empty(),epoch: 0 }; proposed_copy(s,u,t,u.nodes[i].history[k]); }
                },
                Action::AckLd(_,_) => if let Message::AckLd(z)=s.msgs[(y,x)][0] { math::ack_contents(n.history,y,z); },
                Action::Ack(_,_) => if let Message::Ack(z)=s.msgs[(y,x)][0] { let p=index(n.history,z)-1; if 0 <= p < n.history.len() { math::update_contents(n.history,p,Txn { ack: n.history[p].ack.insert(y),..n.history[p] }); } },
                _ => {},
            }
        },
        Action::Request(x) => { logs::facts(s,c,i,x); if x == i && k == s.nodes[i].history.len() { assert(owned(b,time+1,i,u.nodes[i].current,time+1)); } },
        _ => {},
    }
    if !entry(b,time+1,i,k) {
        assert(k < s.nodes[i].history.len() && s.nodes[i].current == u.nodes[i].current && equal(s.nodes[i].history[k],u.nodes[i].history[k]));
        assert(entry(b,time,i,k)); advance_entry(b,time,i,k);
    }
}
pub proof fn preserve_packet(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,p: int)
    requires connections::safety_spec(b,c),time >= 0,inductive(b,c,time),c.servers.contains(i),c.servers.contains(j),0 <= p < b[time+1].msgs[(i,j)].len()
    ensures packet(b[time+1],b[time+1].msgs[(i,j)][p])
{
    let a=super::zab_sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; let m=u.msgs[(i,j)][p]; logs::at(b,c,time); logs::facts(s,c,i,j); monotone(s,c,a); connections::channel_pair(c,i,j);
    if p < s.msgs[(i,j)].len() { advance_packet(s,u,s.msgs[(i,j)][p]); }
    if p+1 < s.msgs[(i,j)].len() { advance_packet(s,u,s.msgs[(i,j)][p+1]); }
    if !packet(u,m) {
        reveal(enabled); reveal(apply);
        match a {
            Action::AckEpoch(x,y) => {
                logs::facts(s,c,x,y); assert(x == i); assert(exists |e: int,h: Seq<Txn>| m == Message::NewLeader(e,h));
                if let Message::NewLeader(e,h)=m {
                    assert(records(i,e,h).subset_of(u.proposals));
                    assert forall |k: int| 0 <= k < h.len() implies #[trigger] proposed(u,h[k]) by { records_entry(u,i,e,h,k); }
                }
            },
            Action::Broadcast(x) => {
                assert(x == i); let n=s.nodes[i]; let t=n.history[index(n.history,Zxid { epoch: n.current,counter: n.sent+1 })-1];
                assert(u.proposals.contains(Proposal { source: i,epoch: n.current,zxid: t.zxid,value: t.value }));
            },
            _ => { assert(false); },
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
        assert forall |i: int,k: int| c.servers.contains(i) && 0 <= k < b[time].nodes[i].history.len() implies #[trigger] entry(b,time,i,k) by { preserve_entry(b,c,prev,i,k); }
        assert forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < b[time].msgs[(i,j)].len()
            implies #[trigger] packet(b[time],b[time].msgs[(i,j)][p]) by { preserve_packet(b,c,prev,i,j,p); }
    }
}
pub proof fn history_monotone(b: Behavior<LState>,c: Constants,left: int,right: int)
    requires connections::safety_spec(b,c),0 <= left <= right
    ensures b[left].proposals.subset_of(b[right].proposals)
    decreases right-left
{
    if left < right { history_monotone(b,c,left,right-1); let a=super::zab_sessions::step(b,c,right-1); monotone(b[right-1],c,a); }
}
} // verus!
