//! A leader cannot forget its own decision while remaining leader in that term.
use vstd::prelude::*;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::etcd_order as order;
use super::etcd_logs as logs;
use super::etcd_ack_history as acks;
use super::etcd_commit_history::{self as history,ProofState,Decision,state,advance};
use super::temporal::Behavior;
verus! {
pub open spec fn retained(g: ProofState,d: Decision) -> bool {
    let n=state(g).nodes[d.leader];
    n.term == d.term && n.role == Role::Leader ==> d.log.len() <= n.commit
}
pub open spec fn inductive(g: ProofState,c: Constants) -> bool {
    acks::inductive(g,c) && forall |d: Decision| g.decisions.contains(d) ==> #[trigger] retained(g,d)
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(history::initial_proof(c),c)
{ acks::initial_inductive(c); }
pub proof fn preserve_decision(g: ProofState,c: Constants,a: Action,d: Decision)
    requires inductive(g,c),enabled(state(g),c,a),advance(g,c,a).decisions.contains(d)
    ensures retained(advance(g,c,a),d)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    let s=state(g); let u=advance(g,c,a);
    if g.decisions.contains(d) { assert(retained(g,d)); assert(history::decision_valid(g,c,d)); }
    else if let Action::AdvanceCommit(i) = a {}
}
pub proof fn preserve(g: ProofState,c: Constants,a: Action)
    requires inductive(g,c),enabled(state(g),c,a)
    ensures inductive(advance(g,c,a),c)
{
    acks::preserve(g,c,a); let u=advance(g,c,a);
    assert forall |d: Decision| u.decisions.contains(d) implies #[trigger] retained(u,d) by { preserve_decision(g,c,a,d); }
}
pub proof fn prior_lower_term(g: ProofState,c: Constants,i: int) -> (d: Decision)
    requires inductive(g,c),enabled(state(g),c,Action::AdvanceCommit(i)),
        apply(state(g),c,Action::AdvanceCommit(i)).nodes[i].commit > state(g).nodes[i].commit,
        apply(state(g),c,Action::AdvanceCommit(i)).nodes[i].commit > state(g).nodes[i].disk.log.len()
    ensures g.decisions.contains(d),d.term < state(g).nodes[i].term,
        d.log.len() >= apply(state(g),c,Action::AdvanceCommit(i)).nodes[i].commit
{
    let s=state(g); let d=acks::prior_decision(g,c,i); reveal(enabled);
    assert(history::decision_valid(g,c,d)); assert(retained(g,d));
    if d.term == s.nodes[i].term {
        origins::leader_persisted(s,c,i); origins::unique_certificate(s,c,d.term,i,d.leader);
    }
    d
}
// This implication isolates the remaining cross-term obligation. Its prefix
// premise is not yet established by the reachable-state invariant above.
pub proof fn advance_durable_if_lower_decisions_retained(g: ProofState,c: Constants,i: int)
    requires inductive(g,c),enabled(state(g),c,Action::AdvanceCommit(i)),
        state(g).nodes[i].commit <= state(g).nodes[i].disk.log.len(),
        forall |d: Decision| g.decisions.contains(d) && d.term < state(g).nodes[i].term ==> #[trigger] logs::prefix_of(d.log,state(g).nodes[i].log)
    ensures apply(state(g),c,Action::AdvanceCommit(i)).nodes[i].commit <= state(g).nodes[i].disk.log.len()
{
    let s=state(g); let a=Action::AdvanceCommit(i); let n=s.nodes[i]; let u=apply(s,c,a);
    if u.nodes[i].commit > n.disk.log.len() {
        let d=prior_lower_term(g,c,i); assert(history::decision_valid(g,c,d));
        reveal(enabled); reveal(apply); let agreed=agreed_indices(n,c); assert(!agreed.is_empty()); origins::maximum_correct(agreed);
        let k=u.nodes[i].commit as int; assert(n.log[k-1] == n.term);
        assert(logs::prefix_of(d.log,n.log)); assert(d.log[k-1] == n.log[k-1]);
        assert(d.log[k-1] <= d.term); assert(false);
    }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int) -> (g: ProofState)
    requires election::safety_spec(b,c),k >= 0
    ensures state(g) == b[k],inductive(g,c)
    decreases k
{
    if k == 0 { initial_inductive(c); history::initial_proof(c) }
    else {
        let old=safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve(old,c,a); advance(old,c,a)
    }
}
} // verus!
