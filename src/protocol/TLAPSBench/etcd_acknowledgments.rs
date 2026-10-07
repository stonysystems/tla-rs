//! Delayed acknowledgments are bounded by persisted logs or persisted commits.
use vstd::prelude::*;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::etcd_order as order;
use super::etcd_sent as sent;
use super::etcd_persistence as persistence;
use super::temporal::Behavior;
verus! {
pub open spec fn success(m: Message) -> bool { m.body is AppendResponse && m.body->AppendResponse_success }
pub open spec fn authority(s: LState,c: Constants,m: Message) -> bool {
    success(m) ==> m.term > 0 && origins::certificate(s,c,m.term,m.dest)
        && m.term <= s.nodes[m.dest].disk.term
        && (m.term == s.nodes[m.dest].term ==> s.nodes[m.dest].role != Role::Candidate)
}
pub open spec fn pending_bound(s: LState,m: Message) -> bool {
    success(m) ==> if m.source == m.dest {
        m.term == s.nodes[m.source].term ==> m.body->AppendResponse_matched <= s.nodes[m.source].log.len()
    } else {
        m.term == s.nodes[m.dest].disk.term ==> m.body->AppendResponse_matched <= s.nodes[m.dest].disk.log.len()
            || m.body->AppendResponse_matched <= s.nodes[m.source].commit
    }
}
pub open spec fn delivered_bound(s: LState,m: Message) -> bool {
    success(m) && m.term == s.nodes[m.dest].disk.term ==> m.body->AppendResponse_matched <= s.nodes[m.dest].disk.log.len()
        || m.body->AppendResponse_matched <= s.nodes[m.source].disk.commit
}
pub open spec fn matched(s: LState,c: Constants,i: int) -> bool {
    s.nodes[i].matched.dom() == c.servers
    && (s.nodes[i].role == Role::Leader ==> forall |j: int| c.servers.contains(j) ==>
        #[trigger] s.nodes[i].matched[j] <= s.nodes[i].disk.log.len()
        || s.nodes[i].matched[j] <= s.nodes[j].disk.commit)
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    persistence::inductive(s,c)
    && (forall |m: Message| #[trigger] s.pending.count(m) > 0 ==> authority(s,c,m) && pending_bound(s,m))
    && (forall |m: Message| #[trigger] s.messages.count(m) > 0 ==> authority(s,c,m) && delivered_bound(s,m))
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] matched(s,c,i))
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(initial(c),c)
{ persistence::initial_inductive(c); broadcast use vstd::multiset::group_multiset_axioms; }
pub proof fn stable_disk_bound(s: LState,c: Constants,a: Action,t: nat,i: int)
    requires persistence::inductive(s,c),enabled(s,c,a),c.servers.contains(i),origins::certificate(s,c,t,i),
        t <= s.nodes[i].disk.term,t == apply(s,c,a).nodes[i].disk.term
    ensures t == s.nodes[i].disk.term,s.nodes[i].disk.log.len() <= apply(s,c,a).nodes[i].disk.log.len()
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    assert(election::node_inv(s,c,i));
    if a == Action::Ready(i) { persistence::certified_prefix(s,c,t,i); }
}
pub proof fn preserve_authority(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),apply(s,c,a).pending.count(m) > 0 || apply(s,c,a).messages.count(m) > 0
    ensures authority(apply(s,c,a),c,m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    let u=apply(s,c,a); assert(s.votes.subset_of(u.votes));
    if success(m) {
        if s.pending.count(m) > 0 || s.messages.count(m) > 0 {
            assert(authority(s,c,m)); assert(election::node_inv(s,c,m.dest));
            origins::certificate_monotone(s,u,c,m.term,m.dest);
        } else {
            if let Action::SelfAppend(i) = a {
                origins::leader_persisted(s,c,i); assert(order::node_order(s.nodes[i]));
            } else if let Action::Receive { m: packet,how } = a { assert(sent::authority(s,c,packet)); }
            origins::certificate_monotone(s,u,c,m.term,m.dest);
        }
    }
}
pub proof fn old_pending(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),s.pending.count(m) > 0,apply(s,c,a).pending.count(m) > 0
    ensures pending_bound(apply(s,c,a),m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    let u=apply(s,c,a); assert(pending_bound(s,m)); assert(authority(s,c,m));
    assert(election::pending_inv(s,c,m)); assert(election::node_inv(s,c,m.dest));
    persistence::commit_monotone(s,c,a,m.source);
    if success(m) {
        if m.source != m.dest && m.term == u.nodes[m.dest].disk.term { stable_disk_bound(s,c,a,m.term,m.dest); }
        if m.source == m.dest && m.term == u.nodes[m.source].term {
            if let Action::Receive { m: packet,how } = a {
                if packet.dest == m.source && (how == Receive::AppendConflict || how == Receive::AppendExtend) {
                    assert(sent::authority(s,c,packet)); origins::unique_certificate(s,c,m.term,m.dest,packet.source);
                }
            }
        }
    }
}
pub proof fn new_pending(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),s.pending.count(m) == 0,apply(s,c,a).pending.count(m) > 0
    ensures pending_bound(apply(s,c,a),m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    if success(m) {
        if let Action::Receive { m: packet,how } = a {
            assert(sent::authority(s,c,packet)); assert(sent::durable(s,packet));
        }
    }
}
pub proof fn preserve_pending(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),apply(s,c,a).pending.count(m) > 0
    ensures pending_bound(apply(s,c,a),m)
{
    if s.pending.count(m) > 0 { old_pending(s,c,a,m); } else { new_pending(s,c,a,m); }
}
pub proof fn preserve_delivered(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),apply(s,c,a).messages.count(m) > 0
    ensures delivered_bound(apply(s,c,a),m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    let u=apply(s,c,a);
    if s.messages.count(m) > 0 {
        assert(authority(s,c,m)); assert(delivered_bound(s,m)); assert(election::message_wf(m,c));
        persistence::commit_monotone(s,c,a,m.source);
        if success(m) && m.term == u.nodes[m.dest].disk.term { stable_disk_bound(s,c,a,m.term,m.dest); }
    } else {
        assert(s.pending.count(m) > 0); assert(pending_bound(s,m)); assert(authority(s,c,m));
        if let Action::Ready(i) = a {} else { assert(false); }
    }
}
pub proof fn preserve_matched(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures matched(apply(s,c,a),c,i)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    let u=apply(s,c,a); let n=s.nodes[i]; assert(matched(s,c,i)); assert(order::node_order(n));
    if let Action::Receive { m,how } = a { assert(election::message_wf(m,c)); assert(delivered_bound(s,m)); }
    if n.role == Role::Leader { origins::leader_persisted(s,c,i); }
    if a == Action::BecomeLeader(i) { order::candidate_persisted(s,c,i); }
    assert(u.nodes[i].matched.dom() =~= c.servers);
    assert forall |j: int| c.servers.contains(j) && u.nodes[i].role == Role::Leader implies
        #[trigger] u.nodes[i].matched[j] <= u.nodes[i].disk.log.len() || u.nodes[i].matched[j] <= u.nodes[j].disk.commit by {
        persistence::commit_monotone(s,c,a,j);
        assert(n.role == Role::Leader ==> n.matched[j] <= n.disk.log.len() || n.matched[j] <= s.nodes[j].disk.commit);
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    persistence::preserve(s,c,a); let u=apply(s,c,a);
    assert forall |m: Message| #[trigger] u.pending.count(m) > 0 implies authority(u,c,m) && pending_bound(u,m) by { preserve_authority(s,c,a,m); preserve_pending(s,c,a,m); }
    assert forall |m: Message| #[trigger] u.messages.count(m) > 0 implies authority(u,c,m) && delivered_bound(u,m) by { preserve_authority(s,c,a,m); preserve_delivered(s,c,a,m); }
    assert forall |i: int| c.servers.contains(i) implies #[trigger] matched(u,c,i) by { preserve_matched(s,c,a,i); }
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
pub proof fn advance_beyond_disk(s: LState,c: Constants,i: int)
    requires inductive(s,c),enabled(s,c,Action::AdvanceCommit(i)),
        apply(s,c,Action::AdvanceCommit(i)).nodes[i].commit > s.nodes[i].commit,
        apply(s,c,Action::AdvanceCommit(i)).nodes[i].commit > s.nodes[i].disk.log.len()
    ensures quorum(c.voters.filter(|j: int| s.nodes[j].disk.commit >= apply(s,c,Action::AdvanceCommit(i)).nodes[i].commit),c)
{
    reveal(enabled); reveal(apply); let n=s.nodes[i]; let agreed=agreed_indices(n,c);
    assert(matched(s,c,i)); assert(!agreed.is_empty()); origins::maximum_correct(agreed);
    let k=maximum(agreed); let a=c.voters.filter(|j: int| n.matched[j] >= k);
    let b=c.voters.filter(|j: int| s.nodes[j].disk.commit >= k);
    assert(quorum(a,c));
    assert(a.subset_of(b)) by {
        assert forall |j: int| a.contains(j) implies b.contains(j) by {
            assert(c.servers.contains(j));
            assert(n.matched[j] <= n.disk.log.len() || n.matched[j] <= s.nodes[j].disk.commit);
        }
    }
    vstd::set_lib::lemma_len_subset(a,b);
}
} // verus!
