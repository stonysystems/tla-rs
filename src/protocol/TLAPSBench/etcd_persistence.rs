//! Commit counters and same-term disk prefixes needed for delayed acknowledgments.
use vstd::prelude::*;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::etcd_logs as logs;
use super::etcd_sent as sent;
use super::temporal::Behavior;
verus! {
pub open spec fn foreign(s: LState,c: Constants,t: nat,i: int) -> bool {
    exists |j: int| j != i && origins::certificate(s,c,t,j)
}
pub open spec fn node(s: LState,c: Constants,i: int) -> bool {
    let n=s.nodes[i];
    n.disk.commit <= n.commit
    && (n.disk.term == n.term ==> logs::prefix_of(n.disk.log,n.log) || foreign(s,c,n.term,i))
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    sent::inductive(s,c) && forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,c,i)
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(initial(c),c)
{ sent::initial_inductive(c); }
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a),c,i)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    let u=apply(s,c,a); let n=s.nodes[i]; assert(node(s,c,i)); assert(election::node_inv(s,c,i));
    assert(s.votes.subset_of(u.votes));
    if foreign(s,c,n.term,i) {
        let j=choose |j: int| j != i && origins::certificate(s,c,n.term,j);
        origins::certificate_monotone(s,u,c,n.term,j);
    }
    if a == Action::ClientRequest(i) && logs::prefix_of(n.disk.log,n.log) {
        assert(logs::prefix_of(n.log,n.log.push(n.term))); logs::prefix_transitive(n.disk.log,n.log,n.log.push(n.term));
    }
    if let Action::Receive { m,how } = a {
        if m.dest == i && (how == Receive::AppendConflict || how == Receive::AppendExtend) {
            assert(sent::authority(s,c,m)); origins::certificate_monotone(s,u,c,m.term,m.source);
            assert(foreign(u,c,m.term,i));
        }
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    sent::preserve(s,c,a); let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,c,i) by { preserve_node(s,c,a,i); }
}
pub proof fn certified_prefix(s: LState,c: Constants,t: nat,i: int)
    requires inductive(s,c),c.servers.contains(i),origins::certificate(s,c,t,i),s.nodes[i].term == t,s.nodes[i].disk.term == t
    ensures logs::prefix_of(s.nodes[i].disk.log,s.nodes[i].log)
{
    assert(node(s,c,i));
    if foreign(s,c,t,i) {
        let j=choose |j: int| j != i && origins::certificate(s,c,t,j);
        origins::unique_certificate(s,c,t,i,j);
    }
}
pub proof fn commit_monotone(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures s.nodes[i].disk.commit <= apply(s,c,a).nodes[i].disk.commit,
        a != Action::Restart(i) ==> s.nodes[i].commit <= apply(s,c,a).nodes[i].commit
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive); assert(node(s,c,i));
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires election::safety_spec(b,c),k >= 0
    ensures inductive(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c); }
    else {
        safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve(b[i],c,a);
    }
}
} // verus!
