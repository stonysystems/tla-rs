//! A follower's synchronization buffers remain empty until its leader starts forwarding.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{Role,Phase};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_ready as ready;
use super::zookeeper_forwarding as forwarding;
use super::zookeeper_session_frames as session;
use super::zookeeper_single_sync as single;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn used(n: LServer) -> bool { n.pending.len() > 0 || n.commits.len() > 0 || n.mode != Mode::None || n.received_leader || n.phase == Phase::Broadcast }
pub open spec fn clean(n: LServer) -> bool { n.pending.len() == 0 && n.commits.len() == 0 && n.mode == Mode::None && !n.received_leader }
pub open spec fn node(s: LState,c: Constants,i: int) -> bool {
    (s.nodes[i].mode != Mode::None ==> s.election.nodes[i].role == Role::Following)
    && (s.election.nodes[i].role == Role::Following && used(s.nodes[i]) ==>
        s.nodes[i].leader is Some && s.nodes[s.nodes[i].leader.unwrap()].forwarding.contains(i))
}
pub open spec fn safe(s: LState,c: Constants) -> bool { forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,c,i) }
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(initial(c),c,i) by {}
}
pub proof fn mode_role(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures apply(s,c,a).nodes[i].mode != Mode::None ==> apply(s,c,a).election.nodes[i].role == Role::Following
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(a); assert(node(s,c,i));
    if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
    if a is Crash { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); } }
    match a { Action::Partition(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); },_ => {}, }
}
pub proof fn first_use_protocol(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),forwarding::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        apply(s,c,a).election.nodes[i].role == Role::Following,used(apply(s,c,a).nodes[i]),!(s.election.nodes[i].role == Role::Following && used(s.nodes[i]))
    ensures apply(s,c,a).nodes[i].leader is Some,apply(s,c,a).nodes[apply(s,c,a).nodes[i].leader.unwrap()].forwarding.contains(i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); assert(node(s,c,i)); assert(forwarding::node(s,c,i));
    if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); assert(forwarding::node(s,c,x)); }
    assert(a is SyncMessage || a is ProposalSync || a is CommitSync || a is NewLeader || a is UpToDate);
    match a {
        Action::SyncMessage(x,y) | Action::ProposalSync(x,y) | Action::CommitSync(x,y) | Action::NewLeader(x,y) | Action::UpToDate(x,y) => {
            channels::facts(s,c,x,y); forwarding::head(s,c,y,x); ready::head(s,c,y,x); forwarding::retained(s,c,a,y,x);
        },_ => {},
    }
}
pub proof fn first_use_election(s: LState,c: Constants,ea: fle::Action,i: int)
    requires channels::safe(s,c),forwarding::safe(s,c),safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i),
        !(s.election.nodes[i].role == Role::Following && used(s.nodes[i]))
    ensures !(apply(s,c,Action::Election(ea)).election.nodes[i].role == Role::Following && used(apply(s,c,Action::Election(ea)).nodes[i]))
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x);
    assert(node(s,c,i)); assert(node(s,c,x)); assert(forwarding::node(s,c,i)); assert(forwarding::node(s,c,x));
}
pub proof fn first_use(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),forwarding::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,used(apply(s,c,a).nodes[i]),!(s.election.nodes[i].role == Role::Following && used(s.nodes[i]))
    ensures apply(s,c,a).nodes[i].leader is Some,apply(s,c,a).nodes[apply(s,c,a).nodes[i].leader.unwrap()].forwarding.contains(i)
{
    if let Action::Election(ea)=a { first_use_election(s,c,ea,i); }
    else { first_use_protocol(s,c,a,i); }
}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),forwarding::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a),c,i)
{
    let u=apply(s,c,a); mode_role(s,c,a,i); assert(node(s,c,i));
    if u.election.nodes[i].role == Role::Following && used(u.nodes[i]) {
        if s.election.nodes[i].role == Role::Following && used(s.nodes[i]) {
            let j=s.nodes[i].leader.unwrap(); channels::facts(s,c,i,i); assert(c.servers.contains(j));
            session::follower_step(s,c,a,i); channels::facts(s,c,i,j); channels::facts(u,c,i,j); forwarding::retained(s,c,a,j,i);
        } else { first_use(s,c,a,i); }
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires channels::safe(s,c),ready::safe(s,c),forwarding::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    channels::preserve(s,c,a); let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,c,i) by { preserve_node(s,c,a,i); }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else { at(b,c,tick-1); channels::at(b,c,tick-1); ready::at(b,c,tick-1); forwarding::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
pub proof fn before_sync(s: LState,c: Constants,i: int,j: int)
    requires channels::safe(s,c),ready::safe(s,c),single::safe(s,c),safe(s,c),enabled(s,c,Action::Sync(i,j))
    ensures clean(s.nodes[j]),s.nodes[j].phase == Phase::Synchronization
{
    single::before_sync(s,c,i,j); reveal(enabled); channels::facts(s,c,i,j); assert(node(s,c,j));
    let r=choose |r: Electing| s.nodes[i].electing.contains(r) && r.sid == j && r.zxid != unset() && s.nodes[i].learners.contains(j);
    assert(super::zookeeper_receipt_links::electing(s.nodes[i].electing,j)); assert(ready::pair(s,c,i,j));
}
pub proof fn discovery_clean(s: LState,c: Constants,i: int)
    requires channels::safe(s,c),ready::safe(s,c),safe(s,c),c.servers.contains(i),s.election.nodes[i].role == Role::Following,s.nodes[i].phase == Phase::Discovery
    ensures clean(s.nodes[i])
{
    assert(node(s,c,i)); channels::facts(s,c,i,i);
    if used(s.nodes[i]) { let j=s.nodes[i].leader.unwrap(); assert(c.servers.contains(j)); channels::facts(s,c,j,i); assert(ready::pair(s,c,j,i)); assert(false); }
}
} // verus!
