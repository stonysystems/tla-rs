//! A completed discovery quorum consists of actual votes for its leader's accepted epoch.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role};
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_receipts as receipts;
use super::zookeeper_leader_frame as leader;
use super::zookeeper_epoch_messages as messages;
use super::zookeeper_epoch_votes as votes;
use super::zookeeper_ack_votes as acks;
use super::zookeeper_self_votes as own;
use super::zookeeper_quorum_receipts as quorum;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn cell(b: Behavior<LState>,c: Constants,time: int,i: int,j: int) -> bool {
    b[time].election.nodes[i].role == Role::Leading && quorum::member(b[time].nodes[i].electing,j) && j != i ==>
        formed(c,i,z::al_ids(b[time].nodes[i].connecting)) && votes::voted(b,c,time,j,i,b[time].nodes[i].accepted)
}
pub open spec fn safe(b: Behavior<LState>,c: Constants,time: int) -> bool {
    forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] cell(b,c,time,i,j)
}
pub proof fn initial_safe(b: Behavior<LState>,c: Constants)
    requires b[0] == initial(c)
    ensures safe(b,c,0)
{
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(b,c,0,i,j) by {}
}
pub proof fn preserve_cell(b: Behavior<LState>,c: Constants,time: int,a: Action,i: int,j: int)
    requires time >= 0,channels::safe(b[time],c),receipts::safe(b[time],c),messages::safe(b[time],c),acks::safe(b,c,time),safe(b,c,time),
        enabled(b[time],c,a),b[time+1] == apply(b[time],c,a),c.servers.contains(i),c.servers.contains(j)
    ensures cell(b,c,time+1,i,j)
{
    let s=b[time]; let u=b[time+1];
    if u.election.nodes[i].role == Role::Leading && quorum::member(u.nodes[i].electing,j) && j != i {
        quorum::step(s,c,a,i,j);
        if quorum::member(s.nodes[i].electing,j) {
            assert(cell(b,c,time,i,j));
        } else { reveal(enabled); messages::head(s,c,j,i); acks::head(b,c,time,j,i); }
        leader::step(s,c,a,i); votes::retained(b,c,time,time+1,j,i,s.nodes[i].accepted);
    }
}
pub proof fn preserve(b: Behavior<LState>,c: Constants,time: int,a: Action)
    requires time >= 0,channels::safe(b[time],c),receipts::safe(b[time],c),messages::safe(b[time],c),acks::safe(b,c,time),safe(b,c,time),enabled(b[time],c,a),b[time+1] == apply(b[time],c,a)
    ensures safe(b,c,time+1)
{
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(b,c,time+1,i,j) by { preserve_cell(b,c,time,a,i,j); }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b,c,tick)
    decreases tick
{
    if tick == 0 { initial_safe(b,c); }
    else { at(b,c,tick-1); channels::at(b,c,tick-1); receipts::at(b,c,tick-1); messages::at(b,c,tick-1); acks::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b,c,tick-1,a); }
}
pub proof fn finished_certificate(b: Behavior<LState>,c: Constants,tick: int,i: int)
    requires support::safety_spec(b,c),tick >= 0,c.servers.contains(i),c.servers.len() > 1,
        b[tick].election.nodes[i].role == Role::Leading,election_finished(b[tick],c,i)
    ensures votes::certified(b,c,tick,i,b[tick].nodes[i].accepted)
{
    at(b,c,tick); own::at(b,c,tick); let s=b[tick]; let q=quorum::ids(s.nodes[i].electing);
    if q.subset_of(set![i]) { vstd::set_lib::lemma_len_subset(q,set![i]); assert(false); }
    let j=choose |j: int| q.contains(j) && j != i; quorum::membership(s.nodes[i].electing,j); assert(cell(b,c,tick,i,j));
    assert(own::node(b,c,tick,i));
    assert forall |j: int| q.contains(j) implies #[trigger] votes::voted(b,c,tick,j,i,s.nodes[i].accepted) by {
        if j != i { quorum::membership(s.nodes[i].electing,j); assert(cell(b,c,tick,i,j)); }
    }
}
} // verus!
