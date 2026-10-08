//! Reachable receipt collections have unique server identities and retain the leader's own receipt.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role,AL};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_receipt_sets as sets;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn node(s: LState,c: Constants,i: int) -> bool {
    let n=s.nodes[i]; sets::al(n.connecting,c) && sets::al(n.ackld,c) && sets::electing(n.electing,c)
    && (s.election.nodes[i].role == Role::Leading ==> n.connecting.contains(AL { sid: i,connected: true })
        && n.ackld.contains(AL { sid: i,connected: true }) && n.electing.contains(Electing { sid: i,zxid: unset(),quorum: true }))
}
pub open spec fn safe(s: LState,c: Constants) -> bool { forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,c,i) }
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    let s=initial(c);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(s,c,i) by {
        assert(z::al_ids(s.nodes[i].connecting) =~= Set::empty()); assert(z::al_ids(s.nodes[i].ackld) =~= Set::empty()); assert(sets::ids(s.nodes[i].electing) =~= Set::empty());
    }
}
pub proof fn disconnect(n: LServer,c: Constants,i: int,j: int)
    requires sets::al(n.connecting,c),sets::al(n.ackld,c),sets::electing(n.electing,c)
    ensures sets::al(z::disconnect_al(n.connecting,j),c),sets::al(z::disconnect_al(n.ackld,j),c),sets::electing(disconnect_e(n.electing,j),c),
        i != j ==> (n.connecting.contains(AL { sid: i,connected: true }) ==> z::disconnect_al(n.connecting,j).contains(AL { sid: i,connected: true }))
        && (n.ackld.contains(AL { sid: i,connected: true }) ==> z::disconnect_al(n.ackld,j).contains(AL { sid: i,connected: true }))
        && (n.electing.contains(Electing { sid: i,zxid: unset(),quorum: true }) ==> disconnect_e(n.electing,j).contains(Electing { sid: i,zxid: unset(),quorum: true }))
{
    sets::al_disconnect(n.connecting,c,j); sets::al_disconnect(n.ackld,c,j); sets::electing_disconnect(n.electing,c,j);
}
pub proof fn election_node(s: LState,c: Constants,ea: fle::Action,i: int)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Election(ea)),c,i)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x); assert(node(s,c,i));
    sets::singletons(c,x);
}
#[verifier::spinoff_prover]
pub proof fn crash_node(s: LState,c: Constants,x: int,i: int)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,Action::Crash(x)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Crash(x)),c,i)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); assert(node(s,c,i)); assert(node(s,c,x));
    if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,c,y)); disconnect(s.nodes[y],c,y,x); }
}
pub proof fn sync_node(s: LState,c: Constants,x: int,y: int,i: int)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,Action::Sync(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Sync(x,y)),c,i)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,c,i)); assert(node(s,c,x));
    let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    if x == y { assert(r.zxid == unset()); assert(false); }
    sets::electing_replace(s.nodes[x].electing,c,r,Electing { zxid: unset(),..r });
}
pub proof fn ackepoch_node(s: LState,c: Constants,x: int,y: int,i: int)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,Action::AckEpoch(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::AckEpoch(x,y)),c,i)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,c,i)); assert(node(s,c,x)); assert(x != y);
    if let Message::AckEpoch(zxid,e)=s.msgs[(y,x)][0] {
        let finished=election_finished(s,c,x); let en=s.election.nodes[x]; let ok=!(e > en.current || e == en.current && z::newer(zxid,en.processed.zxid));
        sets::electing_update(s.nodes[x].electing,c,y,zxid,!finished && e > -1 && ok);
    }
}
pub proof fn protocol_node(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),!(a is Crash),!(a is Sync),!(a is AckEpoch)
    ensures node(apply(s,c,a),c,i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
    match a {
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,c,y)); disconnect(s.nodes[x],c,x,y); disconnect(s.nodes[y],c,y,x);
            if a is FollowerInfo { sets::al_update(s.nodes[x].connecting,c,y); }
            if a is AckLd { sets::al_update(s.nodes[x].ackld,c,y); }

        },
        _ => {},
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,c,i) by {
        match a { Action::Election(ea) => { election_node(s,c,ea,i); },Action::Crash(x) => { crash_node(s,c,x,i); },Action::Sync(x,y) => { sync_node(s,c,x,y,i); },Action::AckEpoch(x,y) => { ackepoch_node(s,c,x,y,i); },_ => { protocol_node(s,c,a,i); } }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else { at(b,c,tick-1); channels::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
} // verus!
