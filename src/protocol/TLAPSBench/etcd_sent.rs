//! Append requests retain their sender's elected authority and persisted segment.
//! The facts are conditional on the corresponding live or durable term, so old
//! messages remain permitted after their sender has advanced to a later term.
use vstd::prelude::*;
use super::etcd::{*,sub};
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::etcd_logs as logs;
use super::etcd_order as order;
use super::temporal::Behavior;
verus! {
pub open spec fn authority(s: LState,c: Constants,m: Message) -> bool {
    m.body is AppendRequest ==> m.source != m.dest && m.term > 0
        && origins::certificate(s,c,m.term,m.source)
        && m.term <= s.nodes[m.source].disk.term
        && (m.term == s.nodes[m.source].term ==> s.nodes[m.source].role != Role::Candidate)
}
pub open spec fn live(s: LState,m: Message) -> bool {
    m.body is AppendRequest && m.term == s.nodes[m.source].term ==> logs::segment(m,s.nodes[m.source].log)
}
pub open spec fn durable(s: LState,m: Message) -> bool {
    m.body is AppendRequest && m.term == s.nodes[m.source].disk.term ==> logs::segment(m,s.nodes[m.source].disk.log)
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    order::inductive(s,c)
    && (forall |m: Message| #[trigger] s.pending.count(m) > 0 ==> authority(s,c,m) && live(s,m))
    && (forall |m: Message| #[trigger] s.messages.count(m) > 0 ==> authority(s,c,m) && live(s,m) && durable(s,m))
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(initial(c),c)
{ order::initial_inductive(c); broadcast use vstd::multiset::group_multiset_axioms; }
pub proof fn segment_prefix(m: Message,h: Seq<nat>,v: Seq<nat>)
    requires logs::segment(m,h),logs::prefix_of(h,v)
    ensures logs::segment(m,v)
{
    if let Body::AppendRequest { prev,entries,.. } = m.body {
        if prev > 0 { assert(h[prev-1] == v[prev-1]); }
        assert forall |k: int| 0 <= k < entries.len() implies #[trigger] entries[k] == #[trigger] v[prev+k] by {
            assert(entries[k] == h[prev+k]); assert(h[prev+k] == v[prev+k]);
        }
    }
}
pub proof fn no_competing_append(s: LState,c: Constants,old: Message,m: Message)
    requires inductive(s,c),authority(s,c,old),old.body is AppendRequest,
        s.messages.count(m) > 0,m.body is AppendRequest,m.dest == old.source,
        m.term == old.term,m.term == s.nodes[old.source].term
    ensures false
{
    assert(authority(s,c,m));
    origins::unique_certificate(s,c,m.term,m.source,old.source);
}
pub proof fn preserve_authority(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),
        apply(s,c,a).pending.count(m) > 0 || apply(s,c,a).messages.count(m) > 0
    ensures authority(apply(s,c,a),c,m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    let u=apply(s,c,a);
    if m.body is AppendRequest {
        if u.pending.count(m) > 0 { election::preserve_pending(s,c,a,m); }
        else { election::preserve_message(s,c,a,m); }
        assert(s.votes.subset_of(u.votes));
        if s.pending.count(m) > 0 || s.messages.count(m) > 0 {
            assert(authority(s,c,m)); assert(election::node_inv(s,c,m.source));
            origins::certificate_monotone(s,u,c,m.term,m.source);
        } else {
            assert(s.nodes[m.source].role == Role::Leader);
            assert(order::node_order(s.nodes[m.source]));
            origins::leader_persisted(s,c,m.source);
            origins::certificate_monotone(s,u,c,m.term,m.source);
        }
    }
}
pub proof fn old_live(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),
        s.pending.count(m) > 0 || s.messages.count(m) > 0,
        apply(s,c,a).pending.count(m) > 0 || apply(s,c,a).messages.count(m) > 0
    ensures live(apply(s,c,a),m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    let u=apply(s,c,a); let n=s.nodes[m.source];
    assert(authority(s,c,m)); assert(live(s,m)); assert(election::node_inv(s,c,m.source));
    if m.body is AppendRequest && m.term == u.nodes[m.source].term {
        if a == Action::Restart(m.source) {
            assert(s.messages.count(m) > 0); assert(durable(s,m));
        } else if a == Action::ClientRequest(m.source) {
            assert(logs::prefix_of(n.log,n.log.push(n.term))); segment_prefix(m,n.log,n.log.push(n.term));
        } else if let Action::Receive { m: packet,how } = a {
            if packet.dest == m.source && (how == Receive::AppendConflict || how == Receive::AppendExtend) {
                no_competing_append(s,c,m,packet);
            }
        }
    }
}
pub proof fn new_live(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),s.pending.count(m) == 0,s.messages.count(m) == 0,
        apply(s,c,a).pending.count(m) > 0 || apply(s,c,a).messages.count(m) > 0
    ensures live(apply(s,c,a),m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    if m.body is AppendRequest {
        assert(logs::segment(m,s.nodes[m.source].log));
    }
}
pub proof fn preserve_live(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),
        apply(s,c,a).pending.count(m) > 0 || apply(s,c,a).messages.count(m) > 0
    ensures live(apply(s,c,a),m)
{
    if s.pending.count(m) > 0 || s.messages.count(m) > 0 { old_live(s,c,a,m); }
    else { new_live(s,c,a,m); }
}
pub proof fn preserve_durable(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),apply(s,c,a).messages.count(m) > 0
    ensures durable(apply(s,c,a),m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    let u=apply(s,c,a);
    if s.messages.count(m) > 0 { assert(durable(s,m)); assert(live(s,m)); }
    else { assert(s.pending.count(m) > 0); assert(live(s,m)); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    order::preserve_inductive(s,c,a); let u=apply(s,c,a);
    assert forall |m: Message| #[trigger] u.pending.count(m) > 0 implies authority(u,c,m) && live(u,m) by {
        preserve_authority(s,c,a,m); preserve_live(s,c,a,m);
    }
    assert forall |m: Message| #[trigger] u.messages.count(m) > 0 implies authority(u,c,m) && live(u,m) && durable(u,m) by {
        preserve_authority(s,c,a,m); preserve_live(s,c,a,m); preserve_durable(s,c,a,m);
    }
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
