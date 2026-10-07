//! Every acknowledgment stored by an active leader has a historical storage witness.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs as leader;
use super::zab_entry_origins::through;
use super::zab_ack_messages as messages;
use super::zab_sessions as sessions;
use super::temporal::Behavior;
verus! {
pub open spec fn witness(b: Behavior<LState>,time: int,i: int,e: int,h: Seq<Txn>,k: int,j: int,read: int) -> bool {
    0 <= read <= time && b[read].nodes[i].role == Role::Leading && b[read].nodes[i].phase != Phase::Discovery
    && b[read].nodes[i].current == e && b[read].nodes[i].learners.contains(j)
    && b[read].nodes[j].accepted == e && b[read].nodes[j].current == e && through(h,b[read].nodes[j].history,k)
}
pub open spec fn certificate(b: Behavior<LState>,c: Constants,time: int,i: int,e: int,h: Seq<Txn>,k: int,j: int) -> bool {
    c.servers.contains(j) && exists |read: int| #[trigger] witness(b,time,i,e,h,k,j,read)
}
pub proof fn copy(b: Behavior<LState>,c: Constants,old: int,time: int,i: int,e: int,a: Seq<Txn>,d: Seq<Txn>,k: int,j: int)
    requires old <= time,certificate(b,c,old,i,e,a,k,j),through(a,d,k)
    ensures certificate(b,c,time,i,e,d,k,j)
{
    let read=choose |read: int| witness(b,old,i,e,a,k,j,read);
    assert(through(d,b[read].nodes[j].history,k)) by {
        assert forall |p: int| 0 <= p <= k implies #[trigger] equal(d[p],b[read].nodes[j].history[p]) by {
            assert(equal(a[p],d[p])); assert(equal(a[p],b[read].nodes[j].history[p]));
        }
    }
    assert(witness(b,time,i,e,d,k,j,read));
}
pub proof fn own(b: Behavior<LState>,c: Constants,time: int,i: int,k: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),b[time].nodes[i].role == Role::Leading,b[time].nodes[i].phase != Phase::Discovery,
        0 <= k < b[time].nodes[i].history.len()
    ensures certificate(b,c,time,i,b[time].nodes[i].current,b[time].nodes[i].history,k,i)
{
    logs::at(b,c,time); logs::facts(b[time],c,i,i);
    assert(witness(b,time,i,b[time].nodes[i].current,b[time].nodes[i].history,k,i,time));
}
pub proof fn received(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,z: Zxid,ld: bool,k: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),b[time].msgs[(j,i)].contains(messages::message(z,ld)),
        0 <= k < index(b[time].nodes[i].history,z)
    ensures certificate(b,c,time,i,b[time].nodes[i].current,b[time].nodes[i].history,k,j)
{
    let read=messages::stored_prefix(b,c,time,i,j,z,ld); let h=b[time].nodes[i].history; let d=b[read].nodes[j].history;
    assert(through(h,d,k)) by { assert forall |p: int| 0 <= p <= k implies #[trigger] equal(h[p],d[p]) by { assert(equal(d[p],h[p])); } }
    assert(witness(b,time,i,b[time].nodes[i].current,h,k,j,read));
}
pub open spec fn inductive(b: Behavior<LState>,c: Constants,time: int) -> bool {
    forall |i: int,k: int,j: int| c.servers.contains(i) && b[time].nodes[i].role == Role::Leading && b[time].nodes[i].phase != Phase::Discovery
        && 0 <= k < b[time].nodes[i].history.len() && b[time].nodes[i].history[k].ack.contains(j)
        ==> #[trigger] certificate(b,c,time,i,b[time].nodes[i].current,b[time].nodes[i].history,k,j)
}
pub proof fn initial_inductive(b: Behavior<LState>,c: Constants)
    requires connections::safety_spec(b,c)
    ensures inductive(b,c,0)
{}
pub proof fn preserve_one(b: Behavior<LState>,c: Constants,time: int,i: int,k: int,j: int)
    requires connections::safety_spec(b,c),time >= 0,inductive(b,c,time),c.servers.contains(i),
        b[time+1].nodes[i].role == Role::Leading,b[time+1].nodes[i].phase != Phase::Discovery,
        0 <= k < b[time+1].nodes[i].history.len(),b[time+1].nodes[i].history[k].ack.contains(j)
    ensures certificate(b,c,time+1,i,b[time+1].nodes[i].current,b[time+1].nodes[i].history,k,j)
{
    let a=sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; logs::at(b,c,time); logs::preserve(s,c,a);
    logs::facts(s,c,i,i); logs::facts(u,c,i,i); reveal(enabled); reveal(apply);
    let inherited=s.nodes[i].role == Role::Leading && s.nodes[i].phase != Phase::Discovery
        && k < s.nodes[i].history.len() && s.nodes[i].history[k].ack.contains(j);
    if inherited {
        leader::active_step(s,c,a,i); assert(certificate(b,c,time,i,s.nodes[i].current,s.nodes[i].history,k,j));
        copy(b,c,time,time+1,i,s.nodes[i].current,s.nodes[i].history,u.nodes[i].history,k,j);
    } else {
        match a {
            Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
                logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); let n=s.nodes[x];
                match a {
                    Action::AckEpoch(_,_) => {
                        assert(x == i && j == i); own(b,c,time+1,i,k);
                    },
                    Action::AckLd(_,_) => if let Message::AckLd(z)=s.msgs[(y,x)][0] {
                        assert(x == i); assert(s.msgs[(y,x)].contains(messages::message(z,true)));
                        let read=messages::stored_prefix(b,c,time,x,y,z,true); let p=index(n.history,z)-1;
                        math::lookup(n.history,z); math::ack_prefix(n.history,y,p); math::ack_contents(n.history,y,z);
                        assert(j == y && k <= p);
                        received(b,c,time,i,j,z,true,k); copy(b,c,time,time+1,i,n.current,n.history,u.nodes[i].history,k,j);
                    },
                    Action::Ack(_,_) => if let Message::Ack(z)=s.msgs[(y,x)][0] {
                        assert(x == i); assert(j == y && k == index(n.history,z)-1);
                        assert(s.msgs[(y,x)].contains(messages::message(z,false))); received(b,c,time,i,j,z,false,k);
                        math::update_contents(n.history,k,Txn { ack: n.history[k].ack.insert(y),..n.history[k] });
                        copy(b,c,time,time+1,i,n.current,n.history,u.nodes[i].history,k,j);
                    },
                    _ => { assert(false); },
                }
            },
            Action::Request(x) => { assert(x == i && j == i); own(b,c,time+1,i,k); },
            _ => { assert(false); },
        }
    }
}
pub proof fn preserve(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0,inductive(b,c,time)
    ensures inductive(b,c,time+1)
{
    assert forall |i: int,k: int,j: int| c.servers.contains(i) && b[time+1].nodes[i].role == Role::Leading && b[time+1].nodes[i].phase != Phase::Discovery
        && 0 <= k < b[time+1].nodes[i].history.len() && b[time+1].nodes[i].history[k].ack.contains(j)
        implies #[trigger] certificate(b,c,time+1,i,b[time+1].nodes[i].current,b[time+1].nodes[i].history,k,j) by { preserve_one(b,c,time,i,k,j); }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures inductive(b,c,time)
    decreases time
{
    if time == 0 { initial_inductive(b,c); }
    else { at(b,c,time-1); preserve(b,c,time-1); }
}
pub proof fn domain(b: Behavior<LState>,c: Constants,time: int,i: int,k: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),b[time].nodes[i].role == Role::Leading,b[time].nodes[i].phase != Phase::Discovery,
        0 <= k < b[time].nodes[i].history.len()
    ensures b[time].nodes[i].history[k].ack.subset_of(c.servers)
{
    at(b,c,time);
    assert forall |j: int| b[time].nodes[i].history[k].ack.contains(j) implies c.servers.contains(j) by {
        assert(certificate(b,c,time,i,b[time].nodes[i].current,b[time].nodes[i].history,k,j));
    }
}
} // verus!
