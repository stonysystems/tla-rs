//! Proposal and acknowledgment identifiers never exceed their leader's broadcast counter.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_broadcast_bounds as bounds;
use super::temporal::Behavior;
verus! {
pub open spec fn packet(s: LState,i: int,j: int,m: Message) -> bool {
    match m {
        Message::Propose(z,_) => z.epoch == s.nodes[i].current && z.counter <= s.nodes[i].sent,
        Message::Ack(z) => z.epoch == s.nodes[j].current && z.counter <= s.nodes[j].sent,
        _ => true,
    }
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    bounds::inductive(s,c)
    && forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < s.msgs[(i,j)].len() ==> #[trigger] packet(s,i,j,s.msgs[(i,j)][k])
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{
    bounds::initial_inductive(c);
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= k < initial(c).msgs[(i,j)].len()
        implies #[trigger] packet(initial(c),i,j,initial(c).msgs[(i,j)][k]) by { connections::channel_pair(c,i,j); }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn preserve_packet(s: LState,c: Constants,a: Action,i: int,j: int,k: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),0 <= k < apply(s,c,a).msgs[(i,j)].len()
    ensures packet(apply(s,c,a),i,j,apply(s,c,a).msgs[(i,j)][k])
{
    hide(update_ack);
    reveal(enabled); reveal(apply); logs::facts(s,c,i,j); connections::channel_pair(c,i,j);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y); logs::facts(s,c,j,x); logs::facts(s,c,j,y);
            if a == Action::Propose(x,y) { assert(packet(s,y,x,s.msgs[(y,x)][0])); }
        },
        Action::Restart(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { logs::facts(s,c,x,y); logs::facts(s,c,i,y); logs::facts(s,c,j,y); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); },
        Action::Broadcast(x) => { logs::facts(s,c,i,x); logs::facts(s,c,j,x); math::broadcast_index(s.nodes[x]); },
        _ => {},
    }
    if k < s.msgs[(i,j)].len() { assert(packet(s,i,j,s.msgs[(i,j)][k])); assert(super::zab_phases::packet(s,c,i,j,s.msgs[(i,j)][k])); }
    if k+1 < s.msgs[(i,j)].len() { assert(packet(s,i,j,s.msgs[(i,j)][k+1])); assert(super::zab_phases::packet(s,c,i,j,s.msgs[(i,j)][k+1])); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    bounds::preserve(s,c,a); let u=apply(s,c,a);
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
} // verus!
