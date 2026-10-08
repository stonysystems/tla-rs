//! A server cannot lose log contents while its current epoch remains unchanged.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_epochs as epochs;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs::{self as leader,prefix};
use super::zab_sync_prefixes as sync;
use super::zab_sessions as sessions;
use super::temporal::Behavior;
verus! {
#[verifier::spinoff_prover]
pub proof fn step(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),b[time].nodes[i].current == b[time+1].nodes[i].current
    ensures prefix(b[time].nodes[i].history,b[time+1].nodes[i].history)
{
    hide(update_ack);
    let a=sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; logs::at(b,c,time); sync::at(b,c,time);
    logs::preserve(s,c,a); logs::facts(s,c,i,i); logs::facts(u,c,i,i); reveal(enabled); reveal(apply);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); logs::facts(u,c,x,y);
            let n=s.nodes[x];
            match a {
                Action::AckEpoch(_,_) => {
                    if x == i && !quorum(ae_ids(n.ae),c) && u.nodes[x].phase != Phase::Discovery {
                        leader::fresh_activation(b,c,time,x,time,x); assert(false);
                    }
                },
                Action::NewLeader(_,_) => { assert(sync::awaiting(s.nodes[x],s.msgs[(y,x)][0])); },
                Action::AckLd(_,_) => if let Message::AckLd(z)=s.msgs[(y,x)][0] { math::ack_contents(n.history,y,z); },
                Action::Ack(_,_) => if let Message::Ack(z)=s.msgs[(y,x)][0] {
                    let k=index(n.history,z); if 1 <= k <= n.history.len() { math::update_contents(n.history,k-1,Txn { ack: n.history[k-1].ack.insert(y),..n.history[k-1] }); }
                },
                _ => {},
            }
        },
        _ => {},
    }
}
pub proof fn between(b: Behavior<LState>,c: Constants,left: int,right: int,i: int)
    requires connections::safety_spec(b,c),0 <= left <= right,c.servers.contains(i),b[left].nodes[i].current == b[right].nodes[i].current
    ensures prefix(b[left].nodes[i].history,b[right].nodes[i].history)
    decreases right-left
{
    if left < right {
        let prev=right-1; epochs::monotone(b,c,left,prev,i); epochs::monotone(b,c,prev,right,i);
        between(b,c,left,prev,i); step(b,c,prev,i); leader::transitive(b[left].nodes[i].history,b[prev].nodes[i].history,b[right].nodes[i].history);
    }
}
} // verus!
