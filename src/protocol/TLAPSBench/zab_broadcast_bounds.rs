//! The broadcast counter is zero before broadcast and never exceeds the log counter.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::temporal::Behavior;
verus! {
pub open spec fn node(n: LServer) -> bool {
    n.role == Role::Leading ==> (n.phase != Phase::Broadcast ==> n.sent == 0)
        && (n.phase != Phase::Discovery ==> n.sent <= counter(n))
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    logs::inductive(s,c) && forall |i: int| c.servers.contains(i) ==> #[trigger] node(s.nodes[i])
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{ logs::initial_inductive(c); }
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a).nodes[i])
{
    reveal(enabled); reveal(apply); logs::facts(s,c,i,i); logs::preserve_node(s,c,a,i); assert(node(s.nodes[i]));
    let u=apply(s,c,a); assert(u.nodes[i].history[u.nodes[i].history.len() as int-1].zxid.counter > 0);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); let n=s.nodes[x];
            match a {
                Action::AckLd(_,_) => if let Message::AckLd(z)=s.msgs[(y,x)][0] { math::ack_contents(n.history,y,z); math::same_last(n.history,update_ack(n.history,y,z)); },
                Action::Ack(_,_) => if let Message::Ack(z)=s.msgs[(y,x)][0] {
                    let k=index(n.history,z)-1; if 0 <= k < n.history.len() {
                        let t=Txn { ack: n.history[k].ack.insert(y),..n.history[k] }; math::update_contents(n.history,k,t); math::same_last(n.history,n.history.update(k,t));
                    }
                },
                _ => {},
            }
        },
        Action::Request(x) | Action::Broadcast(x) => { logs::facts(s,c,i,x); },
        _ => {},
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    logs::preserve(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(apply(s,c,a).nodes[i]) by { preserve_node(s,c,a,i); }
}
#[verifier::spinoff_prover]
pub proof fn was_broadcast(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].role == Role::Leading,
        apply(s,c,a).nodes[i].phase == Phase::Broadcast,apply(s,c,a).nodes[i].sent > 0
    ensures s.nodes[i].role == Role::Leading,s.nodes[i].phase == Phase::Broadcast,s.nodes[i].current == apply(s,c,a).nodes[i].current
{
    reveal(enabled); reveal(apply); logs::facts(s,c,i,i); assert(node(s.nodes[i]));
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y);
        },
        _ => {},
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures inductive(b[time],c)
    decreases time
{
    if time == 0 { initial_inductive(c); }
    else { at(b,c,time-1); let a=super::zab_sessions::step(b,c,time-1); preserve(b[time-1],c,a); }
}
} // verus!
