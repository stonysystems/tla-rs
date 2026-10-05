//! A leader's proposed epoch is its own strict epoch-acceptance event.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_receipts as receipts;
use super::zookeeper_receipt_sets as sets;
use super::zookeeper_epochs as epochs;
use super::zookeeper_leader_frame as leader;
use super::zookeeper_epoch_votes as votes;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn node(b: Behavior<LState>,c: Constants,time: int,i: int) -> bool {
    b[time].election.nodes[i].role == Role::Leading && formed(c,i,z::al_ids(b[time].nodes[i].connecting)) ==>
        votes::voted(b,c,time,i,i,b[time].nodes[i].accepted)
}
pub open spec fn safe(b: Behavior<LState>,c: Constants,time: int) -> bool {
    forall |i: int| c.servers.contains(i) ==> #[trigger] node(b,c,time,i)
}
pub proof fn initial_safe(b: Behavior<LState>,c: Constants)
    requires b[0] == initial(c)
    ensures safe(b,c,0)
{
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(b,c,0,i) by {}
}
pub proof fn fresh_election(s: LState,c: Constants,ea: fle::Action,i: int)
    requires channels::safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i),c.servers.len() > 1,
        apply(s,c,Action::Election(ea)).election.nodes[i].role == Role::Leading,
        formed(c,i,z::al_ids(apply(s,c,Action::Election(ea)).nodes[i].connecting))
    ensures s.election.nodes[i].role == Role::Leading,formed(c,i,z::al_ids(s.nodes[i].connecting))
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x); sets::singletons(c,x);
    let qa=set![z::AL { sid: x,connected: true }]; assert(qa.contains(z::AL { sid: x,connected: true }));
    qa.lemma_map_contains(|r: z::AL| r.sid,x); assert(z::al_ids(qa).contains(x)); assert(z::al_ids(qa) =~= set![x]);
    assert(set![x].len() == 1);
}
pub proof fn crash_quorum(s: LState,c: Constants,x: int,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,Action::Crash(x)),c.servers.contains(i),apply(s,c,Action::Crash(x)).election.nodes[i].role == Role::Leading
    ensures s.election.nodes[i].role == Role::Leading,z::al_ids(apply(s,c,Action::Crash(x)).nodes[i].connecting) == z::al_ids(s.nodes[i].connecting)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x);
    if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); sets::al_disconnect(s.nodes[y].connecting,c,x); }
}
pub proof fn partition_quorum(s: LState,c: Constants,x: int,y: int,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,Action::Partition(x,y)),c.servers.contains(i),apply(s,c,Action::Partition(x,y)).election.nodes[i].role == Role::Leading
    ensures s.election.nodes[i].role == Role::Leading,z::al_ids(apply(s,c,Action::Partition(x,y)).nodes[i].connecting) == z::al_ids(s.nodes[i].connecting)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y);
    assert(receipts::node(s,c,x)); sets::al_disconnect(s.nodes[x].connecting,c,y);
}
pub proof fn leader_info_quorum(s: LState,c: Constants,x: int,y: int,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,Action::LeaderInfo(x,y)),c.servers.contains(i),apply(s,c,Action::LeaderInfo(x,y)).election.nodes[i].role == Role::Leading
    ensures s.election.nodes[i].role == Role::Leading,z::al_ids(apply(s,c,Action::LeaderInfo(x,y)).nodes[i].connecting) == z::al_ids(s.nodes[i].connecting)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y);
    assert(receipts::node(s,c,y)); sets::al_disconnect(s.nodes[y].connecting,c,x);
}
pub proof fn other_quorum(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),epochs::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),!(a is FollowerInfo),
        apply(s,c,a).election.nodes[i].role == Role::Leading
    ensures s.election.nodes[i].role == Role::Leading,z::al_ids(apply(s,c,a).nodes[i].connecting) == z::al_ids(s.nodes[i].connecting)
{
    match a {
        Action::Crash(x) => { crash_quorum(s,c,x,i); },
        Action::Partition(x,y) => { partition_quorum(s,c,x,y,i); },
        Action::LeaderInfo(x,y) => { leader_info_quorum(s,c,x,y,i); },
        _ => {
            reveal(enabled); reveal(apply); let x=receiver(a); if a != Action::Stutter { channels::facts(s,c,i,x); }
            if let Action::AckEpoch(_,y)=a { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }
        },
    }
}
pub proof fn first_quorum(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),epochs::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        apply(s,c,a).election.nodes[i].role == Role::Leading,formed(c,i,z::al_ids(apply(s,c,a).nodes[i].connecting)),
        !(s.election.nodes[i].role == Role::Leading && formed(c,i,z::al_ids(s.nodes[i].connecting)))
    ensures votes::cast(s,c,a,i,i,apply(s,c,a).nodes[i].accepted)
{
    if let Action::FollowerInfo(x,y)=a {
        reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(epochs::node(s,c,i));
    } else { other_quorum(s,c,a,i); }
}
pub proof fn preserve_node(b: Behavior<LState>,c: Constants,time: int,a: Action,i: int)
    requires time >= 0,c.servers.len() > 1,channels::safe(b[time],c),receipts::safe(b[time],c),epochs::safe(b[time],c),safe(b,c,time),
        enabled(b[time],c,a),b[time+1] == apply(b[time],c,a),c.servers.contains(i)
    ensures node(b,c,time+1,i)
{
    let s=b[time]; let u=b[time+1];
    if u.election.nodes[i].role == Role::Leading && formed(c,i,z::al_ids(u.nodes[i].connecting)) {
        if let Action::Election(ea)=a { fresh_election(s,c,ea,i); }
        if s.election.nodes[i].role == Role::Leading && formed(c,i,z::al_ids(s.nodes[i].connecting)) {
            leader::step(s,c,a,i); assert(node(b,c,time,i)); votes::retained(b,c,time,time+1,i,i,s.nodes[i].accepted);
        } else { first_quorum(s,c,a,i); votes::record_step(b,c,time,a,i,i,u.nodes[i].accepted); }
    }
}
pub proof fn preserve(b: Behavior<LState>,c: Constants,time: int,a: Action)
    requires time >= 0,c.servers.len() > 1,channels::safe(b[time],c),receipts::safe(b[time],c),epochs::safe(b[time],c),safe(b,c,time),enabled(b[time],c,a),b[time+1] == apply(b[time],c,a)
    ensures safe(b,c,time+1)
{
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(b,c,time+1,i) by { preserve_node(b,c,time,a,i); }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),c.servers.len() > 1,tick >= 0
    ensures safe(b,c,tick)
    decreases tick
{
    if tick == 0 { initial_safe(b,c); }
    else { at(b,c,tick-1); channels::at(b,c,tick-1); receipts::at(b,c,tick-1); epochs::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b,c,tick-1,a); }
}
} // verus!
