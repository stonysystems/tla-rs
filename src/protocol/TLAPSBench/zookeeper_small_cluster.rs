//! With at most one server, no protocol channel can complete synchronization.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::Phase;
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::temporal::Behavior;
verus! {
broadcast use vstd::set_lib::group_set_lib_default;
pub open spec fn node(s: LState,i: int) -> bool { s.nodes[i].phase == Phase::Election || s.nodes[i].phase == Phase::Discovery }
pub open spec fn safe(s: LState,c: Constants) -> bool { forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,i) }
pub proof fn same_server(c: Constants,i: int,j: int)
    requires c.servers.len() <= 1,c.servers.contains(i),c.servers.contains(j)
    ensures i == j
{
    if i != j { assert(set![i,j].subset_of(c.servers)); vstd::set_lib::lemma_len_subset(set![i,j],c.servers); }
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(initial(c),i) by {}
}
pub proof fn no_request(s: LState,c: Constants,i: int)
    requires safe(s,c)
    ensures !enabled(s,c,Action::Request(i))
{
    reveal(enabled); if c.servers.contains(i) { assert(node(s,i)); }
}
pub proof fn election_node(s: LState,c: Constants,ea: fle::Action,i: int)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Election(ea)),i)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x); assert(node(s,i));
}
pub proof fn protocol_node(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.len() <= 1,!(a is Election)
    ensures node(apply(s,c,a),i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); assert(node(s,i)); if a != Action::Stutter { channels::facts(s,c,i,x); same_server(c,i,x); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,x,y); same_server(c,x,y);
            if a is Sync {
                let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y); assert(r.zxid == unset()); assert(false);
            }
        },_ => {},
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.len() <= 1
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,i) by {
        if let Action::Election(ea)=a { election_node(s,c,ea,i); } else { protocol_node(s,c,a,i); }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0,c.servers.len() <= 1
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else { at(b,c,tick-1); channels::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
} // verus!
