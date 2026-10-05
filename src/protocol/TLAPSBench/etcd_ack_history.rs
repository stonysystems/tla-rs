//! Acknowledgment bounds refer to prior decisions at or below their own term.
use vstd::prelude::*;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::etcd_order as order;
use super::etcd_sent as sent;
use super::etcd_acknowledgments as acks;
use super::etcd_commit_history::{self as history,ProofState,state,advance,has_commit};
use super::temporal::Behavior;
verus! {
pub open spec fn delivered(g: ProofState,m: Message) -> bool {
    acks::success(m) && m.term == state(g).nodes[m.dest].disk.term ==>
        m.body->AppendResponse_matched <= state(g).nodes[m.dest].disk.log.len()
        || has_commit(g,m.term,m.body->AppendResponse_matched)
}
pub open spec fn pending(g: ProofState,m: Message) -> bool {
    m.source != m.dest ==> delivered(g,m)
}
pub open spec fn matched(g: ProofState,c: Constants,i: int) -> bool {
    let n=state(g).nodes[i];
    n.role == Role::Leader ==> forall |j: int| c.servers.contains(j) ==>
        #[trigger] n.matched[j] <= n.disk.log.len() || has_commit(g,n.term,n.matched[j])
}
pub open spec fn inductive(g: ProofState,c: Constants) -> bool {
    history::inductive(g,c)
    && (forall |m: Message| #[trigger] state(g).pending.count(m) > 0 ==> pending(g,m))
    && (forall |m: Message| #[trigger] state(g).messages.count(m) > 0 ==> delivered(g,m))
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] matched(g,c,i))
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(history::initial_proof(c),c)
{ history::initial_inductive(c); broadcast use vstd::multiset::group_multiset_axioms; }
pub proof fn preserve_pending(g: ProofState,c: Constants,a: Action,m: Message)
    requires inductive(g,c),enabled(state(g),c,a),state(advance(g,c,a)).pending.count(m) > 0
    ensures pending(advance(g,c,a),m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    let s=state(g); let u=advance(g,c,a); let v=state(u); let k=m.body->AppendResponse_matched;
    assert(g.decisions.subset_of(u.decisions));
    if m.source != m.dest && acks::success(m) && m.term == v.nodes[m.dest].disk.term {
        if s.pending.count(m) > 0 {
            assert(pending(g,m)); assert(acks::authority(s,c,m)); assert(election::pending_inv(s,c,m));
            acks::stable_disk_bound(s,c,a,m.term,m.dest);
            if has_commit(g,m.term,k) { history::commit_monotone(g,u,m.term,k,m.term,k); }
        } else if let Action::Receive { m: packet,how } = a {
            assert(sent::durable(s,packet)); assert(sent::authority(s,c,packet));
            assert(history::node(g,m.source));
            if k > v.nodes[m.dest].disk.log.len() {
                history::commit_monotone(g,u,s.nodes[m.source].term,s.nodes[m.source].commit,m.term,k);
            }
        }
    }
}
pub proof fn preserve_delivered(g: ProofState,c: Constants,a: Action,m: Message)
    requires inductive(g,c),enabled(state(g),c,a),state(advance(g,c,a)).messages.count(m) > 0
    ensures delivered(advance(g,c,a),m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    let s=state(g); let u=advance(g,c,a); let v=state(u); let k=m.body->AppendResponse_matched;
    assert(g.decisions.subset_of(u.decisions));
    if acks::success(m) && m.term == v.nodes[m.dest].disk.term {
        if s.messages.count(m) > 0 {
            assert(delivered(g,m)); assert(acks::authority(s,c,m)); assert(election::message_wf(m,c));
            acks::stable_disk_bound(s,c,a,m.term,m.dest);
            if has_commit(g,m.term,k) { history::commit_monotone(g,u,m.term,k,m.term,k); }
        } else {
            assert(s.pending.count(m) > 0); assert(pending(g,m)); assert(acks::pending_bound(s,m));
            if has_commit(g,m.term,k) { history::commit_monotone(g,u,m.term,k,m.term,k); }
            if let Action::Ready(i) = a {} else { assert(false); }
        }
    }
}
pub proof fn preserve_matched(g: ProofState,c: Constants,a: Action,i: int)
    requires inductive(g,c),enabled(state(g),c,a),c.servers.contains(i)
    ensures matched(advance(g,c,a),c,i)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    let s=state(g); let u=advance(g,c,a); let n=s.nodes[i]; let v=state(u).nodes[i];
    assert(matched(g,c,i)); assert(order::node_order(n)); assert(g.decisions.subset_of(u.decisions));
    if n.role == Role::Leader { origins::leader_persisted(s,c,i); }
    if a == Action::BecomeLeader(i) { order::candidate_persisted(s,c,i); }
    if let Action::Receive { m,how } = a { assert(delivered(g,m)); }
    assert forall |j: int| c.servers.contains(j) && v.role == Role::Leader implies
        #[trigger] v.matched[j] <= v.disk.log.len() || has_commit(u,v.term,v.matched[j]) by {
        assert(n.role == Role::Leader ==> n.matched[j] <= n.disk.log.len() || has_commit(g,n.term,n.matched[j]));
        if v.matched[j] > v.disk.log.len() {
            if v.matched[j] == n.matched[j] {
                history::commit_monotone(g,u,n.term,n.matched[j],v.term,v.matched[j]);
            } else if let Action::Receive { m,how } = a {
                history::commit_monotone(g,u,m.term,m.body->AppendResponse_matched,v.term,v.matched[j]);
            }
        }
    }
}
pub proof fn preserve(g: ProofState,c: Constants,a: Action)
    requires inductive(g,c),enabled(state(g),c,a)
    ensures inductive(advance(g,c,a),c)
{
    history::preserve(g,c,a); let u=advance(g,c,a);
    assert forall |m: Message| #[trigger] state(u).pending.count(m) > 0 implies pending(u,m) by { preserve_pending(g,c,a,m); }
    assert forall |m: Message| #[trigger] state(u).messages.count(m) > 0 implies delivered(u,m) by { preserve_delivered(g,c,a,m); }
    assert forall |i: int| c.servers.contains(i) implies #[trigger] matched(u,c,i) by { preserve_matched(g,c,a,i); }
}
pub proof fn prior_decision(g: ProofState,c: Constants,i: int) -> (d: history::Decision)
    requires inductive(g,c),enabled(state(g),c,Action::AdvanceCommit(i)),
        apply(state(g),c,Action::AdvanceCommit(i)).nodes[i].commit > state(g).nodes[i].commit,
        apply(state(g),c,Action::AdvanceCommit(i)).nodes[i].commit > state(g).nodes[i].disk.log.len()
    ensures g.decisions.contains(d),d.term <= state(g).nodes[i].term,
        d.log.len() >= apply(state(g),c,Action::AdvanceCommit(i)).nodes[i].commit
{
    reveal(enabled); reveal(apply); let n=state(g).nodes[i]; let agreed=agreed_indices(n,c);
    assert(matched(g,c,i)); assert(!agreed.is_empty()); origins::maximum_correct(agreed);
    let k=maximum(agreed); let q=c.voters.filter(|j: int| n.matched[j] >= k);
    assert(quorum(q,c)); assert(!q.is_empty()); let j=q.choose(); assert(c.servers.contains(j));
    assert(n.matched[j] <= n.disk.log.len() || has_commit(g,n.term,n.matched[j]));
    choose |d: history::Decision| g.decisions.contains(d) && d.term <= n.term && d.log.len() >= n.matched[j]
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
