//! A continuing leader retains its receipt identities and fixes its proposed epoch after a quorum.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_receipts as receipts;
use super::zookeeper_receipt_sets as sets;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn stable(s: LState,u: LState,c: Constants,i: int) -> bool {
    z::al_ids(s.nodes[i].connecting).subset_of(z::al_ids(u.nodes[i].connecting))
    && z::al_ids(s.nodes[i].ackld).subset_of(z::al_ids(u.nodes[i].ackld))
    && (formed(c,i,z::al_ids(s.nodes[i].connecting)) ==> u.nodes[i].accepted == s.nodes[i].accepted)
}
pub proof fn election_step(s: LState,c: Constants,ea: fle::Action,i: int)
    requires channels::safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i),s.election.nodes[i].role == Role::Leading,
        apply(s,c,Action::Election(ea)).election.nodes[i].role == Role::Leading
    ensures stable(s,apply(s,c,Action::Election(ea)),c,i)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x);
}
pub proof fn protocol_step(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),s.election.nodes[i].role == Role::Leading,
        apply(s,c,a).election.nodes[i].role == Role::Leading,!(a is Election)
    ensures stable(s,apply(s,c,a),c,i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); assert(receipts::node(s,c,i));
    if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a {
        Action::Crash(_) => {
            if let Some(y)=s.nodes[x].leader {
                channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y));
                sets::al_disconnect(s.nodes[y].connecting,c,x); sets::al_disconnect(s.nodes[y].ackld,c,x);
            }
        },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y));
            sets::al_disconnect(s.nodes[x].connecting,c,y); sets::al_disconnect(s.nodes[x].ackld,c,y);
            sets::al_disconnect(s.nodes[y].connecting,c,x); sets::al_disconnect(s.nodes[y].ackld,c,x);
            if a is FollowerInfo { sets::al_update(s.nodes[x].connecting,c,y); }
            if a is AckLd { sets::al_update(s.nodes[x].ackld,c,y); }
        },
        _ => {},
    }
}
pub proof fn step(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),s.election.nodes[i].role == Role::Leading,
        apply(s,c,a).election.nodes[i].role == Role::Leading
    ensures stable(s,apply(s,c,a),c,i),formed(c,i,z::al_ids(s.nodes[i].connecting)) ==> formed(c,i,z::al_ids(apply(s,c,a).nodes[i].connecting))
{
    match a { Action::Election(ea) => { election_step(s,c,ea,i); },_ => { protocol_step(s,c,a,i); } }
    if formed(c,i,z::al_ids(s.nodes[i].connecting)) {
        receipts::preserve(s,c,a); let u=apply(s,c,a); assert(receipts::node(u,c,i));
        super::zab_collections::quorum_superset(z::al_ids(s.nodes[i].connecting),z::al_ids(u.nodes[i].connecting),c);
    }
}
pub open spec fn interval(b: Behavior<LState>,i: int,left: int,right: int) -> bool {
    0 <= left <= right && forall |tick: int| left <= tick <= right ==> (#[trigger] b[tick]).election.nodes[i].role == Role::Leading
}
pub proof fn between(b: Behavior<LState>,c: Constants,i: int,left: int,right: int)
    requires support::safety_spec(b,c),c.servers.contains(i),interval(b,i,left,right)
    ensures stable(b[left],b[right],c,i),formed(c,i,z::al_ids(b[left].nodes[i].connecting)) ==> formed(c,i,z::al_ids(b[right].nodes[i].connecting))
    decreases right-left
{
    if left < right {
        between(b,c,i,left,right-1); channels::at(b,c,right-1); receipts::at(b,c,right-1); let a=support::step(b,c,right-1); step(b[right-1],c,a,i);
        assert(z::al_ids(b[left].nodes[i].connecting).subset_of(z::al_ids(b[right].nodes[i].connecting)));
        assert(z::al_ids(b[left].nodes[i].ackld).subset_of(z::al_ids(b[right].nodes[i].ackld)));
    }
}
} // verus!
