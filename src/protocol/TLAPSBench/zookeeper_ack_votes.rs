//! A positive epoch acknowledgment records the sender's actual epoch acceptance.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::Role;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_receipts as receipts;
use super::zookeeper_leader_frame as leader;
use super::zookeeper_message_frames as frames;
use super::zookeeper_epoch_messages as messages;
use super::zookeeper_epoch_votes as votes;
use super::zab_connections::channel_pair;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn packet(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,m: Message) -> bool {
    match m { Message::AckEpoch(_,report) => report >= 0 ==> votes::voted(b,c,time,i,j,b[time].nodes[j].accepted),_ => true }
}
pub open spec fn cell(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,m: Message) -> bool {
    b[time].msgs[(i,j)].contains(m) ==> packet(b,c,time,i,j,m)
}
pub open spec fn safe(b: Behavior<LState>,c: Constants,time: int) -> bool {
    forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] cell(b,c,time,i,j,m)
}
pub proof fn initial_safe(b: Behavior<LState>,c: Constants)
    requires b[0] == initial(c)
    ensures safe(b,c,0)
{
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(b,c,0,i,j,m) by { channel_pair(c,i,j); }
}
pub proof fn head(b: Behavior<LState>,c: Constants,time: int,i: int,j: int)
    requires safe(b,c,time),c.servers.contains(i),c.servers.contains(j),b[time].msgs[(i,j)].len() > 0
    ensures packet(b,c,time,i,j,b[time].msgs[(i,j)][0])
{
    assert(b[time].msgs[(i,j)].contains(b[time].msgs[(i,j)][0])); assert(cell(b,c,time,i,j,b[time].msgs[(i,j)][0]));
}
pub proof fn preserve_packet(b: Behavior<LState>,c: Constants,time: int,a: Action,i: int,j: int,m: Message)
    requires time >= 0,channels::safe(b[time],c),receipts::safe(b[time],c),messages::safe(b[time],c),safe(b,c,time),
        enabled(b[time],c,a),b[time+1] == apply(b[time],c,a),c.servers.contains(i),c.servers.contains(j),b[time+1].msgs[(i,j)].contains(m)
    ensures packet(b,c,time+1,i,j,m)
{
    let s=b[time]; let u=b[time+1];
    if let Message::AckEpoch(_,report)=m {
        if report >= 0 {
            frames::epoch_origin(s,c,a,i,j,m);
            if s.msgs[(i,j)].contains(m) {
                assert(messages::cell(s,c,i,j,m)); assert(cell(b,c,time,i,j,m));
                frames::step_roles(s,c,a,i,j); leader::step(s,c,a,j);
                votes::retained(b,c,time,time+1,i,j,s.nodes[j].accepted);
            } else {
                reveal(enabled); reveal(apply); messages::head(s,c,j,i); channels::facts(s,c,i,j);
                leader::step(s,c,a,j);
                assert(s.nodes[i].accepted < u.nodes[i].accepted);
                assert(votes::cast(s,c,a,i,j,u.nodes[j].accepted));
                votes::record_step(b,c,time,a,i,j,u.nodes[j].accepted);
            }
        }
    }
}
pub proof fn preserve(b: Behavior<LState>,c: Constants,time: int,a: Action)
    requires time >= 0,channels::safe(b[time],c),receipts::safe(b[time],c),messages::safe(b[time],c),safe(b,c,time),enabled(b[time],c,a),b[time+1] == apply(b[time],c,a)
    ensures safe(b,c,time+1)
{
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(b,c,time+1,i,j,m) by {
        if b[time+1].msgs[(i,j)].contains(m) { preserve_packet(b,c,time,a,i,j,m); }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b,c,tick)
    decreases tick
{
    if tick == 0 { initial_safe(b,c); }
    else { at(b,c,tick-1); channels::at(b,c,tick-1); receipts::at(b,c,tick-1); messages::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b,c,tick-1,a); }
}
} // verus!
