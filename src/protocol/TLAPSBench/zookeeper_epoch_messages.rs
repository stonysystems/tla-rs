//! Discovery messages carry the proposed epoch of their connected leader.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role};
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_receipts as receipts;
use super::zookeeper_leader_frame as leader;
use super::zookeeper_message_frames as frames;
use super::zab_connections::channel_pair;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn packet(s: LState,c: Constants,i: int,j: int,m: Message) -> bool {
    match m {
        Message::LeaderInfo(zxid) => s.election.nodes[i].role == Role::Leading
            && formed(c,i,z::al_ids(s.nodes[i].connecting)) && zxid.epoch == s.nodes[i].accepted,
        Message::AckEpoch(_,_) => s.election.nodes[j].role == Role::Leading && formed(c,j,z::al_ids(s.nodes[j].connecting)),
        _ => true,
    }
}
pub open spec fn cell(s: LState,c: Constants,i: int,j: int,m: Message) -> bool { s.msgs[(i,j)].contains(m) ==> packet(s,c,i,j,m) }
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] cell(s,c,i,j,m)
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    let s=initial(c);
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(s,c,i,j,m) by { channel_pair(c,i,j); }
}
pub proof fn head(s: LState,c: Constants,i: int,j: int)
    requires safe(s,c),c.servers.contains(i),c.servers.contains(j),s.msgs[(i,j)].len() > 0
    ensures packet(s,c,i,j,s.msgs[(i,j)][0])
{
    assert(s.msgs[(i,j)].contains(s.msgs[(i,j)][0])); assert(cell(s,c,i,j,s.msgs[(i,j)][0]));
}
pub proof fn retained(s: LState,c: Constants,a: Action,i: int,j: int,m: Message)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),packet(s,c,i,j,m),
        s.msgs[(i,j)].contains(m),apply(s,c,a).msgs[(i,j)].contains(m)
    ensures packet(apply(s,c,a),c,i,j,m)
{
    frames::step_roles(s,c,a,i,j); let u=apply(s,c,a);
    if let Message::LeaderInfo(zxid)=m { leader::step(s,c,a,i); }
    if m is AckEpoch { leader::step(s,c,a,j); }
}
pub proof fn fresh(s: LState,c: Constants,a: Action,i: int,j: int,m: Message)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),frames::fresh_epoch(s,c,a,i,j,m)
    ensures packet(apply(s,c,a),c,i,j,m)
{
    if let (Action::LeaderInfo(x,y),Message::AckEpoch(_,report))=(a,m) {
        reveal(enabled); reveal(apply); head(s,c,j,i); channels::facts(s,c,i,j);
        leader::step(s,c,a,j);
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a);
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(u,c,i,j,m) by {
        if u.msgs[(i,j)].contains(m) && frames::epoch_message(m) {
            frames::epoch_origin(s,c,a,i,j,m);
            if s.msgs[(i,j)].contains(m) { assert(cell(s,c,i,j,m)); retained(s,c,a,i,j,m); }
            else { fresh(s,c,a,i,j,m); }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else { at(b,c,tick-1); channels::at(b,c,tick-1); receipts::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
} // verus!
