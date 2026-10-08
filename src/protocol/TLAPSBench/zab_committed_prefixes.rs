//! Every committed range is in bounds and has a quorum certificate, except bootstrap.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_epochs as epochs;
use super::zab_entry_origins::through;
use super::zab_commit_certificates::{self as commits,certified};
use super::zab_certificate_copy as copy;
use super::zab_receipt_links as links;
use super::zab_log_matching as matching;
use super::temporal::Behavior;
verus! {
pub open spec fn node(b: Behavior<LState>,c: Constants,time: int,i: int) -> bool {
    let n=b[time].nodes[i]; let k=n.committed.index-1;
    n.committed.index == 0 || (0 <= k < n.history.len() && n.history[k].zxid == n.committed.zxid
        && (k == 0 || exists |e: int| 0 < e <= n.current && #[trigger] certified(b,c,time,e,n.history,k)))
}
pub open spec fn origin(b: Behavior<LState>,c: Constants,time: int,e: int,z: Zxid,w: (int,int,int)) -> bool {
    0 <= w.0 <= time && c.servers.contains(w.1) && 0 <= w.2 < b[w.0].nodes[w.1].history.len()
    && b[w.0].nodes[w.1].history[w.2].zxid == z && certified(b,c,time,e,b[w.0].nodes[w.1].history,w.2)
}
pub open spec fn backed(b: Behavior<LState>,c: Constants,time: int,e: int,z: Zxid) -> bool {
    exists |w: (int,int,int)| #[trigger] origin(b,c,time,e,z,w)
}
pub open spec fn justified(b: Behavior<LState>,c: Constants,time: int,epoch: int,z: Zxid) -> bool {
    z == boot() || exists |e: int| 0 < e <= epoch && #[trigger] backed(b,c,time,e,z)
}
pub open spec fn packet(b: Behavior<LState>,c: Constants,time: int,i: int,m: Message) -> bool {
    match m {
        Message::CommitLd(z) | Message::Commit(z) => justified(b,c,time,b[time].nodes[i].current,z),
        _ => true,
    }
}
pub open spec fn inductive(b: Behavior<LState>,c: Constants,time: int) -> bool {
    (forall |i: int| c.servers.contains(i) ==> #[trigger] node(b,c,time,i))
    && (forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < b[time].msgs[(i,j)].len()
        ==> #[trigger] packet(b,c,time,i,b[time].msgs[(i,j)][p]))
}
pub proof fn initial_inductive(b: Behavior<LState>,c: Constants)
    requires connections::safety_spec(b,c)
    ensures inductive(b,c,0)
{
    assert forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < b[0].msgs[(i,j)].len()
        implies #[trigger] packet(b,c,0,i,b[0].msgs[(i,j)][p]) by { connections::channel_pair(c,i,j); }
}
pub proof fn inherit(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),node(b,c,time,i),b[time+1].nodes[i].committed == b[time].nodes[i].committed
    ensures node(b,c,time+1,i)
{
    logs::at(b,c,time); logs::at(b,c,time+1); logs::facts(b[time],c,i,i); logs::facts(b[time+1],c,i,i); epochs::monotone(b,c,time,time+1,i);
    let n=b[time].nodes[i]; let d=b[time+1].nodes[i]; let k=n.committed.index-1;
    if n.committed.index > 0 {
        if k == 0 {} else {
            let e=choose |e: int| 0 < e <= n.current && certified(b,c,time,e,n.history,k);
            if n.current == d.current { super::zab_epoch_retention::step(b,c,time,i); }
            else { super::zab_certified_retention::higher_epoch(b,c,time,e,n.history,k,d.current); assert(through(n.history,d.history,k)); }
            assert(through(n.history,d.history,k)); assert(equal(n.history[k],d.history[k])); copy::copy(b,c,time,time+1,e,n.history,d.history,k);
        }
    }
}
pub proof fn certificate_for(b: Behavior<LState>,c: Constants,time: int,i: int) -> (e: int)
    requires node(b,c,time,i),b[time].nodes[i].committed.index > 1
    ensures 0 < e <= b[time].nodes[i].current,certified(b,c,time,e,b[time].nodes[i].history,b[time].nodes[i].committed.index-1)
{
    choose |e: int| 0 < e <= b[time].nodes[i].current && #[trigger] certified(b,c,time,e,b[time].nodes[i].history,b[time].nodes[i].committed.index-1)
}
pub proof fn source_for(b: Behavior<LState>,c: Constants,time: int,epoch: int,z: Zxid) -> (ew: (int,(int,int,int)))
    requires justified(b,c,time,epoch,z),z != boot()
    ensures 0 < ew.0 <= epoch,origin(b,c,time,ew.0,z,ew.1)
{
    let e=choose |e: int| 0 < e <= epoch && #[trigger] backed(b,c,time,e,z);
    let w=choose |w: (int,int,int)| origin(b,c,time,e,z,w); (e,w)
}
pub proof fn received_certificate(b: Behavior<LState>,c: Constants,time: int,i: int,z: Zxid,k: int,epoch: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),justified(b,c,time,epoch,z),
        0 <= k < b[time+1].nodes[i].history.len(),b[time+1].nodes[i].history[k].zxid == z
    ensures k == 0 || exists |e: int| 0 < e <= epoch && #[trigger] certified(b,c,time+1,e,b[time+1].nodes[i].history,k)
{
    let d=b[time+1].nodes[i];
    if z == boot() { logs::at(b,c,time+1); logs::facts(b[time+1],c,i,i); matching::unique_index(d.history,k,0); }
    else {
        let ew=source_for(b,c,time,epoch,z); let e=ew.0; let w=ew.1;
        matching::historical_matching(b,c,w.0,w.1,time+1,i,w.2,k);
        copy::copy(b,c,time,time+1,e,b[w.0].nodes[w.1].history,d.history,k);
    }
}
pub proof fn receive(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,z: Zxid,k: int,ld: bool)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),
        b[time].msgs[(j,i)].len() > 0,b[time].msgs[(j,i)][0] == (if ld { Message::CommitLd(z) } else { Message::Commit(z) }),
        packet(b,c,time,j,b[time].msgs[(j,i)][0]),0 <= k < b[time+1].nodes[i].history.len(),b[time+1].nodes[i].history[k].zxid == z,
        b[time+1].nodes[i].committed.index == k+1,b[time+1].nodes[i].committed.zxid == z
    ensures node(b,c,time+1,i)
{
    logs::at(b,c,time+1); logs::facts(b[time+1],c,i,i); links::at(b,c,time); super::zab_phases::at(b,c,time);
    super::zab_phases::facts(b[time],c,j,i); links::facts(b[time],c,j,i); links::connected_al(b[time],c,j,i); epochs::monotone(b,c,time,time+1,i);
    assert(justified(b,c,time,b[time].nodes[j].current,z));
    received_certificate(b,c,time,i,z,k,b[time].nodes[j].current);

}
pub proof fn preserve_node(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),inductive(b,c,time)
    ensures node(b,c,time+1,i)
{
    let a=super::zab_sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; logs::at(b,c,time); logs::preserve(s,c,a);
    logs::facts(s,c,i,i); logs::facts(u,c,i,i); assert(node(b,c,time,i));
    if u.nodes[i].committed == s.nodes[i].committed { inherit(b,c,time,i); }
    else if u.nodes[i].committed.index == 0 {}
    else if u.nodes[i].role == Role::Leading && u.nodes[i].phase != Phase::Discovery { commits::new_commit(b,c,time,i); }
    else {
        reveal(enabled); reveal(apply);
        match a {
            Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
                logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y);
                match a {
                    Action::CommitLd(_,_) => if let Message::CommitLd(z)=s.msgs[(y,x)][0] {
                        assert(x == i); super::zab_commit_delivery::head(b,c,time,y,i,z); math::lookup(s.nodes[i].history,z);
                        assert(packet(b,c,time,y,s.msgs[(y,i)][0])); receive(b,c,time,i,y,z,u.nodes[i].committed.index-1,true);
                    },
                    Action::Commit(_,_) => if let Message::Commit(z)=s.msgs[(y,x)][0] {
                        assert(x == i); assert(packet(b,c,time,y,s.msgs[(y,i)][0])); receive(b,c,time,i,y,z,u.nodes[i].committed.index-1,false);
                    },
                    _ => { assert(false); },
                }
            },
            Action::Restart(x) => { logs::facts(s,c,i,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); } assert(false); },
            _ => { assert(false); },
        }
    }
}
pub proof fn advance_packet(b: Behavior<LState>,c: Constants,time: int,i: int,m: Message)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),packet(b,c,time,i,m)
    ensures packet(b,c,time+1,i,m)
{
    epochs::monotone(b,c,time,time+1,i);
    match m {
        Message::CommitLd(z) | Message::Commit(z) => if z != boot() {
            let e=choose |e: int| 0 < e <= b[time].nodes[i].current && #[trigger] backed(b,c,time,e,z);
            let w=choose |w: (int,int,int)| origin(b,c,time,e,z,w); let h=b[w.0].nodes[w.1].history;
            copy::copy(b,c,time,time+1,e,h,h,w.2); assert(origin(b,c,time+1,e,z,w)); assert(backed(b,c,time+1,e,z)); assert(0 < e <= b[time+1].nodes[i].current); assert(justified(b,c,time+1,b[time+1].nodes[i].current,z));
        },
        _ => {},
    }
}
/// The only per-node fact `advertised` needs from the log invariant;
/// kept apart so the rest of `logs::facts` stays out of its query.
proof fn advertised_shape(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i)
    ensures logs::node(b[time].nodes[i])
{
    logs::at(b,c,time); logs::facts(b[time],c,i,i);
}
pub proof fn advertised(b: Behavior<LState>,c: Constants,time: int,i: int,z: Zxid,ld: bool)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),node(b,c,time,i),b[time].nodes[i].committed.index > 0,b[time].nodes[i].committed.zxid == z
    ensures packet(b,c,time,i,if ld { Message::CommitLd(z) } else { Message::Commit(z) })
{
    advertised_shape(b,c,time,i); let n=b[time].nodes[i]; let k=n.committed.index-1;
    if z != boot() {
        assert(k != 0); let e=choose |e: int| 0 < e <= n.current && certified(b,c,time,e,n.history,k);
        assert(origin(b,c,time,e,z,(time,i,k))); assert(backed(b,c,time,e,z)); assert(justified(b,c,time,n.current,z));
    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn preserve_packet(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,p: int)
    requires connections::safety_spec(b,c),time >= 0,inductive(b,c,time),c.servers.contains(i),c.servers.contains(j),0 <= p < b[time+1].msgs[(i,j)].len()
    ensures packet(b,c,time+1,i,b[time+1].msgs[(i,j)][p])
{
    hide(update_ack);
    let a=super::zab_sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; let m=u.msgs[(i,j)][p];
    logs::at(b,c,time); logs::preserve(s,c,a); logs::facts(s,c,i,j); logs::facts(u,c,i,j); connections::channel_pair(c,i,j);
    if p < s.msgs[(i,j)].len() { advance_packet(b,c,time,i,s.msgs[(i,j)][p]); }
    if p+1 < s.msgs[(i,j)].len() { advance_packet(b,c,time,i,s.msgs[(i,j)][p+1]); }
    if !packet(b,c,time+1,i,m) {
        preserve_node(b,c,time,i); super::zab_broadcast_commits::at(b,c,time+1); reveal(enabled); reveal(apply);
        if let Action::AckLd(x,y)=a { logs::facts(s,c,x,y); } if let Action::Ack(x,y)=a { logs::facts(s,c,x,y); }
        match m {
            Message::CommitLd(z) | Message::Commit(z) => {
                assert(u.nodes[i].role == Role::Leading && u.nodes[i].phase == Phase::Broadcast && u.nodes[i].committed.zxid == z);
                assert(super::zab_broadcast_commits::node(u.nodes[i])); advertised(b,c,time+1,i,z,m is CommitLd);
            },
            _ => {},
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
        assert forall |i: int| c.servers.contains(i) implies #[trigger] node(b,c,time,i) by { preserve_node(b,c,prev,i); }
        assert forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < b[time].msgs[(i,j)].len()
            implies #[trigger] packet(b,c,time,i,b[time].msgs[(i,j)][p]) by { preserve_packet(b,c,prev,i,j,p); }
    }
}
} // verus!
