//! A leader's quorum remains connected or has moved beyond its proposed epoch.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_epochs as epochs;
use super::zab_receipts as receipts;
use super::temporal::Behavior;
verus! {
pub open spec fn above(s: LState,c: Constants,e: int) -> Set<int> {
    c.servers.filter(|j: int| s.nodes[j].accepted > e)
}
pub open spec fn support(s: LState,c: Constants,i: int) -> Set<int> {
    s.nodes[i].learners.union(above(s,c,s.nodes[i].accepted))
}
pub open spec fn node(s: LState,c: Constants,i: int) -> bool {
    s.nodes[i].role == Role::Leading ==> if quorum(ce_ids(s.nodes[i].ce),c) { quorum(support(s,c,i),c) }
        else { ce_ids(s.nodes[i].ce).subset_of(s.nodes[i].learners) || quorum(s.nodes[i].learners,c) }
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    receipts::inductive(s,c) && forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,c,i)
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{ receipts::initial_inductive(c); }
pub proof fn above_grows(s: LState,c: Constants,a: Action,e: int)
    requires epochs::inductive(s,c),enabled(s,c,a)
    ensures above(s,c,e).subset_of(above(apply(s,c,a),c,e))
{
    assert forall |j: int| #![trigger above(s,c,e).contains(j)] above(s,c,e).contains(j) implies above(apply(s,c,a),c,e).contains(j) by { epochs::preserve_node(s,c,a,j); }
}
pub proof fn fresh_ids(n: LServer,i: int)
    ensures ce_ids(lead(n,i).ce) =~= lead(n,i).learners
{
    let r=CE { sid: i,connected: true,epoch: n.accepted };
    assert(lead(n,i).ce.contains(r)); assert(ce_ids(lead(n,i).ce).contains(i));
}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a),c,i)
{
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i); assert(node(s,c,i));
    above_grows(s,c,a,s.nodes[i].accepted); connections::preserve_node(s,c,a,i);
    let u=apply(s,c,a); let n=s.nodes[i]; let v=u.nodes[i];
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            receipts::facts(s,c,x,y); receipts::facts(s,c,i,x); receipts::facts(s,c,i,y);
            collections::disconnect_ids(s.nodes[x].ce,s.nodes[x].ae,s.nodes[x].al,y);
            collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x);
            if a == Action::CEpoch(x,y) { if let Message::CEpoch(e)=s.msgs[(y,x)][0] {
                collections::ce_update(s.nodes[x].ce,y,e); collections::quorum_add(ce_ids(s.nodes[x].ce),c,y);
                if i == x && !quorum(ce_ids(n.ce),c) && quorum(ce_ids(v.ce),c) {
                    if ce_ids(n.ce).subset_of(n.learners) {
                        assert(ce_ids(v.ce).subset_of(n.learners)); collections::quorum_superset(ce_ids(v.ce),n.learners,c);
                    }
                    assert(quorum(v.learners,c));
                }
            } }
            if a == Action::NewLeader(x,y) { assert(s.nodes[x].accepted == s.nodes[y].accepted); }
        },
        Action::Restart(x) => {
            receipts::facts(s,c,i,x);
            if let Some(y)=s.nodes[x].leader { receipts::facts(s,c,x,y); receipts::facts(s,c,i,y); collections::disconnect_ids(s.nodes[y].ce,s.nodes[y].ae,s.nodes[y].al,x); }
        },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { receipts::facts(s,c,i,x); fresh_ids(s.nodes[x],x); },
        _ => {},
    }
    if v.role == Role::Leading && quorum(ce_ids(v.ce),c) {
        if quorum(v.learners,c) {
            assert(v.learners.subset_of(support(u,c,i))); collections::quorum_superset(v.learners,support(u,c,i),c);
        } else {
            assert(n.role == Role::Leading && quorum(ce_ids(n.ce),c));
            assert(n.accepted == v.accepted);
            assert(support(s,c,i).subset_of(support(u,c,i)));
            collections::quorum_superset(support(s,c,i),support(u,c,i),c);
        }
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    receipts::preserve(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(apply(s,c,a),c,i) by { preserve_node(s,c,a,i); }
}
pub proof fn at(b: Behavior<LState>,c: Constants,k: int)
    requires connections::safety_spec(b,c),k >= 0
    ensures inductive(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c); }
    else {
        at(b,c,k-1); let time=k-1; assert(next(b[time],b[time+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[time],c,a) && b[time+1] == apply(b[time],c,a);
        preserve(b[time],c,a);
    }
}
} // verus!
