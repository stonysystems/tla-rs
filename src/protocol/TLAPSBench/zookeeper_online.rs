//! A crashed server returns to election before it can restart or rejoin a protocol connection.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::Role;
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::temporal::Behavior;
verus! {
pub open spec fn node(s: LState,i: int) -> bool { !s.nodes[i].online ==> s.election.nodes[i].role == Role::Looking }
pub open spec fn safe(s: LState,c: Constants) -> bool { forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,i) }
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(initial(c),i) by {}
}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a),i)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(a); assert(node(s,i));
    if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,x)); }
    if a is Crash { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); } }
    match a { Action::Partition(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); },_ => {}, }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,i) by { preserve_node(s,c,a,i); }
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
