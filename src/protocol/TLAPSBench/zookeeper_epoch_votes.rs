//! Strict accepted-epoch increases certify one leader choice per voter and epoch.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role};
use super::zookeeper_support as support;
use super::zookeeper_epochs as epochs;
use super::temporal::Behavior;
verus! {
pub open spec fn cast(s: LState,c: Constants,a: Action,i: int,leader: int,epoch: int) -> bool {
    c.servers.contains(i) && c.servers.contains(leader) && enabled(s,c,a)
    && s.nodes[i].accepted < epoch && apply(s,c,a).nodes[i].accepted == epoch
    && match a { Action::FollowerInfo(x,_) => x == i && leader == i,Action::LeaderInfo(x,j) => x == i && leader == j,_ => false }
}
pub open spec fn witness(b: Behavior<LState>,c: Constants,time: int,i: int,leader: int,epoch: int,p: (int,Action)) -> bool {
    let at=p.0; let a=p.1; 0 <= at < time && cast(b[at],c,a,i,leader,epoch) && b[at+1] == apply(b[at],c,a)
}
pub open spec fn voted(b: Behavior<LState>,c: Constants,time: int,i: int,leader: int,epoch: int) -> bool {
    exists |p: (int,Action)| #[trigger] witness(b,c,time,i,leader,epoch,p)
}
pub proof fn same_step(s: LState,c: Constants,a: Action,d: Action,i: int,leader: int,other: int,epoch: int)
    requires cast(s,c,a,i,leader,epoch),cast(s,c,d,i,other,epoch)
    ensures leader == other
{
    reveal(enabled);
}
pub proof fn retained(b: Behavior<LState>,c: Constants,left: int,right: int,i: int,leader: int,epoch: int)
    requires left <= right,voted(b,c,left,i,leader,epoch)
    ensures voted(b,c,right,i,leader,epoch)
{
    let (at,a)=choose |p: (int,Action)| witness(b,c,left,i,leader,epoch,p);
    assert(witness(b,c,right,i,leader,epoch,(at,a)));
}
pub proof fn unique(b: Behavior<LState>,c: Constants,left: int,right: int,i: int,leader: int,other: int,epoch: int)
    requires support::safety_spec(b,c),voted(b,c,left,i,leader,epoch),voted(b,c,right,i,other,epoch)
    ensures leader == other
{
    let (first,a)=choose |p: (int,Action)| witness(b,c,left,i,leader,epoch,p);
    let (last,d)=choose |p: (int,Action)| witness(b,c,right,i,other,epoch,p);
    if first == last { same_step(b[first],c,a,d,i,leader,other,epoch); }
    else if first < last { epochs::between(b,c,first+1,last,i); assert(false); }
    else { epochs::between(b,c,last+1,first,i); assert(false); }
}
pub proof fn record_step(b: Behavior<LState>,c: Constants,time: int,a: Action,i: int,leader: int,epoch: int)
    requires time >= 0,cast(b[time],c,a,i,leader,epoch),b[time+1] == apply(b[time],c,a)
    ensures voted(b,c,time+1,i,leader,epoch)
{
    assert(witness(b,c,time+1,i,leader,epoch,(time,a)));
}
pub open spec fn certified(b: Behavior<LState>,c: Constants,time: int,leader: int,epoch: int) -> bool {
    exists |q: Set<int>| z::quorum(q,c) && forall |i: int| q.contains(i) ==> #[trigger] voted(b,c,time,i,leader,epoch)
}
pub proof fn certified_unique(b: Behavior<LState>,c: Constants,left: int,right: int,leader: int,other: int,epoch: int)
    requires support::safety_spec(b,c),certified(b,c,left,leader,epoch),certified(b,c,right,other,epoch)
    ensures leader == other
{
    let q=choose |q: Set<int>| z::quorum(q,c) && forall |i: int| q.contains(i) ==> #[trigger] voted(b,c,left,i,leader,epoch);
    let r=choose |r: Set<int>| z::quorum(r,c) && forall |i: int| r.contains(i) ==> #[trigger] voted(b,c,right,i,other,epoch);
    let i=super::zab_collections::intersect_quorums(q,r,c); assert(voted(b,c,left,i,leader,epoch)); assert(voted(b,c,right,i,other,epoch));
    unique(b,c,left,right,i,leader,other,epoch);
}
} // verus!
