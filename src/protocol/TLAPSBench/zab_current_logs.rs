//! Every nonzero current-epoch log is a synchronized prefix of its epoch leader.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs::{self as leader,epoch_prefix};
use super::zab_proposal_logs as proposals;
use super::zab_elections as elections;
use super::zab_sessions as sessions;
use super::temporal::Behavior;
verus! {
pub open spec fn witness(b: Behavior<LState>,c: Constants,time: int,h: Seq<Txn>,e: int,w: (int,int)) -> bool {
    0 <= w.0 <= time && c.servers.contains(w.1) && b[w.0].nodes[w.1].role == Role::Leading && b[w.0].nodes[w.1].phase != Phase::Discovery
    && b[w.0].nodes[w.1].current == e && epoch_prefix(h,b[w.0].nodes[w.1].history,e)
}
pub open spec fn image(b: Behavior<LState>,c: Constants,time: int,h: Seq<Txn>,e: int) -> bool {
    (e == 0 ==> h.len() == 1) && (e > 0 ==> exists |w: (int,int)| #[trigger] witness(b,c,time,h,e,w))
}
pub proof fn transfer(b: Behavior<LState>,c: Constants,time: int,a: Seq<Txn>,d: Seq<Txn>,e: int)
    requires image(b,c,time,a,e),math::same(a,d)
    ensures image(b,c,time+1,d,e)
{
    if e > 0 {
        let w=choose |w: (int,int)| witness(b,c,time,a,e,w);
        assert(epoch_prefix(d,a,e)) by { assert forall |k: int| 0 <= k < d.len() implies #[trigger] equal(d[k],a[k]) by { assert(equal(a[k],d[k])); } }
        leader::epoch_transitive(d,a,b[w.0].nodes[w.1].history,e);
        assert(witness(b,c,time+1,d,e,w));
    }
}
pub proof fn aligned(b: Behavior<LState>,c: Constants,time: int,i: int,j: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),
        image(b,c,time,b[time].nodes[i].history,b[time].nodes[i].current),
        b[time].nodes[j].role == Role::Leading,b[time].nodes[j].phase != Phase::Discovery,
        b[time].nodes[i].current == b[time].nodes[j].current,b[time].nodes[i].current > 0
    ensures epoch_prefix(b[time].nodes[i].history,b[time].nodes[j].history,b[time].nodes[j].current)
{
    let n=b[time].nodes[i]; let w=choose |w: (int,int)| witness(b,c,time,n.history,n.current,w);
    elections::unique(b,c,w.0,w.1,time,j); leader::same_epoch(b,c,j,w.0,time);
    leader::epoch_transitive(n.history,b[w.0].nodes[j].history,b[time].nodes[j].history,n.current);
}
pub proof fn preserve_node(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),image(b,c,time,b[time].nodes[i].history,b[time].nodes[i].current)
    ensures image(b,c,time+1,b[time+1].nodes[i].history,b[time+1].nodes[i].current)
{
    let a=sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; proposals::at(b,c,time); proposals::preserve(s,c,a);
    logs::facts(s,c,i,i); logs::facts(u,c,i,i); reveal(enabled); reveal(apply);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); logs::facts(u,c,x,y);
            let n=s.nodes[x];
            match a {
                Action::AckEpoch(_,_) => {
                    if x == i && u.nodes[i].current != n.current || x == i && !math::same(n.history,u.nodes[i].history) {
                        assert(u.nodes[i].role == Role::Leading && u.nodes[i].phase != Phase::Discovery && u.nodes[i].current > 0);
                        assert(witness(b,c,time+1,u.nodes[i].history,u.nodes[i].current,(time+1,i)));
                    }
                },
                Action::NewLeader(_,_) => if let Message::NewLeader(e,h)=s.msgs[(y,x)][0] {
                    assert(proposals::packet(s.nodes[y].history,s.nodes[y].current,s.msgs[(y,x)][0]));
                    if x == i && n.accepted == e {
                        assert(e > 0); assert(witness(b,c,time+1,h,e,(time,y)));
                    }
                },
                Action::AckLd(_,_) => if let Message::AckLd(z)=s.msgs[(y,x)][0] { math::ack_contents(n.history,y,z); },
                Action::Ack(_,_) => if let Message::Ack(z)=s.msgs[(y,x)][0] {
                    let k=index(n.history,z); if 1 <= k <= n.history.len() {
                        math::update_contents(n.history,k-1,Txn { ack: n.history[k-1].ack.insert(y),..n.history[k-1] });
                    }
                },
                Action::Propose(_,_) => if let Message::Propose(z,v)=s.msgs[(y,x)][0] {
                    if x == i && next_zxid(last(n.history),z) {
                        assert(!super::zab_sync::pending(s.msgs[(y,x)],s.nodes[y].current,0));
                        assert(n.current == s.nodes[y].current && n.current > 0);
                        aligned(b,c,time,i,y);
                        assert(proposals::packet(s.nodes[y].history,s.nodes[y].current,s.msgs[(y,x)][0]));
                        let p=choose |p: int| 0 <= p < s.nodes[y].history.len() && s.nodes[y].history[p].zxid == z && s.nodes[y].history[p].value == v;
                        let t=Txn { zxid: z,value: v,ack: Set::empty(),epoch: n.current };
                        leader::append_prefix(n.history,s.nodes[y].history,n.current,p,t);
                        assert(witness(b,c,time+1,n.history.push(t),n.current,(time,y)));
                    }
                },
                _ => {},
            }
        },
        Action::Request(x) => {
            logs::facts(s,c,i,x); if x == i {
                assert(u.nodes[i].current > 0); assert(witness(b,c,time+1,u.nodes[i].history,u.nodes[i].current,(time+1,i)));
            }
        },
        _ => {},
    }
    if math::same(s.nodes[i].history,u.nodes[i].history) && s.nodes[i].current == u.nodes[i].current {
        transfer(b,c,time,s.nodes[i].history,u.nodes[i].history,s.nodes[i].current);
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i)
    ensures image(b,c,time,b[time].nodes[i].history,b[time].nodes[i].current)
    decreases time
{
    if time > 0 { at(b,c,time-1,i); preserve_node(b,c,time-1,i); }
}
} // verus!
