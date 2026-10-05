//! Proof-only histories of leader-created log prefixes establish log matching.
//! These histories do not change the protocol state or its transition relation.
use vstd::prelude::*;
use super::etcd::{*,sub};
use super::etcd_origins as origins;
use super::etcd_election as election;
use super::temporal::Behavior;
verus! {
pub struct ProofState { pub state: LState,pub created: Set<Seq<nat>> }
pub open spec fn prefix_of(a: Seq<nat>,b: Seq<nat>) -> bool {
    a.len() <= b.len() && forall |k: int| 0 <= k < a.len() ==> #[trigger] a[k] == #[trigger] b[k]
}
pub open spec fn matching(a: Seq<nat>,b: Seq<nat>) -> bool {
    forall |k: int| 0 <= k < a.len() && k < b.len() && #[trigger] a[k] == #[trigger] b[k] ==>
        forall |j: int| 0 <= j <= k ==> #[trigger] a[j] == #[trigger] b[j]
}
pub open spec fn represented(g: ProofState,h: Seq<nat>) -> bool {
    exists |a: Seq<nat>| g.created.contains(a) && #[trigger] prefix_of(h,a)
}
pub open spec fn segment(m: Message,h: Seq<nat>) -> bool {
    match m.body {
        Body::AppendRequest { prev,prev_term,entries,.. } => prev <= h.len() && prev+entries.len() <= h.len()
            && prev_term == if prev == 0 { 0 } else { h[prev-1] }
            && forall |k: int| 0 <= k < entries.len() ==> #[trigger] entries[k] == #[trigger] h[prev+k],
        _ => true,
    }
}
pub open spec fn message_rep(g: ProofState,m: Message) -> bool {
    exists |h: Seq<nat>| g.created.contains(h) && #[trigger] segment(m,h)
}
pub open spec fn inductive(g: ProofState,c: Constants) -> bool {
    origins::inductive(g.state,c)
    && (forall |h: Seq<nat>| g.created.contains(h) ==> #[trigger] origins::log_origins(g.state,c,h,0))
    && (forall |a: Seq<nat>,b: Seq<nat>| g.created.contains(a) && g.created.contains(b) ==> #[trigger] matching(a,b))
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] represented(g,g.state.nodes[i].log))
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] represented(g,g.state.nodes[i].disk.log))
    && (forall |m: Message| #[trigger] g.state.pending.count(m) > 0 ==> message_rep(g,m))
    && (forall |m: Message| #[trigger] g.state.messages.count(m) > 0 ==> message_rep(g,m))
}
pub open spec fn initial_proof(c: Constants) -> ProofState {
    ProofState { state: initial(c),created: set![Seq::<nat>::empty()] }
}
pub open spec fn advance(g: ProofState,c: Constants,a: Action) -> ProofState {
    let state=apply(g.state,c,a);
    ProofState { state,created: match a { Action::ClientRequest(i) => g.created.insert(state.nodes[i].log),_ => g.created } }
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(initial_proof(c),c)
{
    origins::initial_inductive(c); broadcast use vstd::multiset::group_multiset_axioms;
    let g=initial_proof(c);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] represented(g,g.state.nodes[i].log) by {
        assert(prefix_of(g.state.nodes[i].log,Seq::empty()));
    }
    assert forall |i: int| c.servers.contains(i) implies #[trigger] represented(g,g.state.nodes[i].disk.log) by {
        assert(prefix_of(g.state.nodes[i].disk.log,Seq::empty()));
    }
}
pub proof fn representing(g: ProofState,h: Seq<nat>) -> (a: Seq<nat>)
    requires represented(g,h)
    ensures g.created.contains(a),prefix_of(h,a)
{ choose |a: Seq<nat>| g.created.contains(a) && #[trigger] prefix_of(h,a) }
pub proof fn representing_message(g: ProofState,m: Message) -> (h: Seq<nat>)
    requires message_rep(g,m)
    ensures g.created.contains(h),segment(m,h)
{ choose |h: Seq<nat>| g.created.contains(h) && #[trigger] segment(m,h) }
pub proof fn prefix_transitive(a: Seq<nat>,b: Seq<nat>,c: Seq<nat>)
    requires prefix_of(a,b),prefix_of(b,c)
    ensures prefix_of(a,c)
{
    assert forall |k: int| 0 <= k < a.len() implies #[trigger] a[k] == #[trigger] c[k] by {
        assert(a[k] == b[k]); assert(b[k] == c[k]);
    }
}
pub proof fn matching_prefix(a: Seq<nat>,b: Seq<nat>,h: Seq<nat>,v: Seq<nat>)
    requires prefix_of(a,h),prefix_of(b,v),matching(h,v)
    ensures matching(a,b)
{
    assert forall |k: int| 0 <= k < a.len() && k < b.len() && #[trigger] a[k] == #[trigger] b[k] implies
        forall |j: int| 0 <= j <= k ==> #[trigger] a[j] == #[trigger] b[j] by {
        assert(a[k] == h[k]); assert(b[k] == v[k]);
        assert forall |j: int| 0 <= j <= k implies #[trigger] a[j] == #[trigger] b[j] by {
            assert(a[j] == h[j]); assert(b[j] == v[j]); assert(h[j] == v[j]);
        }
    }
}
pub proof fn history_entry_at_leader(g: ProofState,c: Constants,i: int,h: Seq<nat>,k: int)
    requires inductive(g,c),c.servers.contains(i),g.state.nodes[i].role == Role::Leader,
        g.created.contains(h),0 <= k < h.len(),h[k] == g.state.nodes[i].term
    ensures k < g.state.nodes[i].log.len()
{
    let s=g.state; let t=s.nodes[i].term;
    origins::leader_persisted(s,c,i);
    assert(origins::log_origins(s,c,h,0)); assert(origins::origin(s,c,t,k+1));
    let o=choose |o: int| #[trigger] origins::owner(s,c,t,k+1,o);
    origins::unique_certificate(s,c,t,i,o);
}
pub proof fn extension_matches(g: ProofState,c: Constants,i: int,h: Seq<nat>)
    requires inductive(g,c),c.servers.contains(i),g.state.nodes[i].role == Role::Leader,g.created.contains(h)
    ensures matching(h,g.state.nodes[i].log.push(g.state.nodes[i].term)),
        matching(g.state.nodes[i].log.push(g.state.nodes[i].term),h)
{
    let log=g.state.nodes[i].log; let t=g.state.nodes[i].term;
    let old=representing(g,log); assert(matching(h,old));
    assert(prefix_of(h,h)); matching_prefix(h,log,h,old);
    let new=log.push(t);
    assert forall |k: int| 0 <= k < h.len() && k < new.len() && #[trigger] h[k] == #[trigger] new[k] implies
        forall |j: int| 0 <= j <= k ==> #[trigger] h[j] == #[trigger] new[j] by {
        if k == log.len() { history_entry_at_leader(g,c,i,h,k); assert(false); }
        else { assert(h[k] == log[k]); }
    }
    assert(matching(h,new));
}
pub proof fn preserve_created_pair(g: ProofState,c: Constants,a: Action,h: Seq<nat>,v: Seq<nat>)
    requires inductive(g,c),enabled(g.state,c,a),advance(g,c,a).created.contains(h),advance(g,c,a).created.contains(v)
    ensures matching(h,v)
{
    reveal(apply);
    if g.created.contains(h) && g.created.contains(v) { assert(matching(h,v)); }
    else if let Action::ClientRequest(i) = a {
        reveal(enabled);
        if g.created.contains(h) { extension_matches(g,c,i,h); }
        else if g.created.contains(v) { extension_matches(g,c,i,v); }
    }
}
pub proof fn preserve_created_origin(g: ProofState,c: Constants,a: Action,h: Seq<nat>)
    requires inductive(g,c),enabled(g.state,c,a),advance(g,c,a).created.contains(h)
    ensures origins::log_origins(advance(g,c,a).state,c,h,0)
{
    let u=advance(g,c,a);
    if g.created.contains(h) {
        assert(origins::log_origins(g.state,c,h,0));
        assert forall |k: int| 0 <= k < h.len() implies origins::origin(u.state,c,#[trigger] h[k],k+1) by {
            origins::preserve_origin(g.state,c,a,h[k],k+1);
        }
    } else if let Action::ClientRequest(i) = a {
        origins::preserve_inductive(g.state,c,a);
        reveal(enabled);
        assert(origins::log_origins(u.state,c,u.state.nodes[i].log,0));
    }
}
pub proof fn append_extends_canonical(g: ProofState,c: Constants,m: Message,h: Seq<nat>)
    requires inductive(g,c),receive_enabled(g.state,m,Receive::AppendExtend),message_rep(g,m),
        election::message_wf(m,c),g.created.contains(h),segment(m,h),m.body is AppendRequest,
        m.body->AppendRequest_prev+m.body->AppendRequest_entries.len() > g.state.nodes[m.dest].log.len()
    ensures prefix_of(receive(g.state,m,Receive::AppendExtend).nodes[m.dest].log,h)
{
    reveal(receive_enabled); reveal(receive);
    let old=g.state.nodes[m.dest].log; let canonical=representing(g,old);
    assert(matching(canonical,h));
    let prev=m.body->AppendRequest_prev;
    let entries=m.body->AppendRequest_entries;
    let u=receive(g.state,m,Receive::AppendExtend).nodes[m.dest].log;
    if prev+entries.len() <= old.len() {
        // This receive action may also take a duplicate, fully overlapping append.
        assert(u =~= old);
        // Only the received prefix need match h; old may have a longer suffix.
    } else {
        assert(u.len() == prev+entries.len());
        if prev > 0 { assert(canonical[prev-1] == h[prev-1]); }
        assert forall |k: int| 0 <= k < u.len() implies #[trigger] u[k] == #[trigger] h[k] by {
            if k < prev { assert(canonical[k] == h[k]); }
            else {
                assert(entries[k-prev] == h[k]);
                if k < old.len() { assert(old[k] == entries[k-prev]); }
            }
        }
    }
}
pub proof fn preserve_log_rep(g: ProofState,c: Constants,a: Action,i: int,disk: bool)
    requires inductive(g,c),enabled(g.state,c,a),c.servers.contains(i)
    ensures represented(advance(g,c,a),if disk { advance(g,c,a).state.nodes[i].disk.log } else { advance(g,c,a).state.nodes[i].log })
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    let s=g.state; let u=advance(g,c,a); let h=if disk { u.state.nodes[i].disk.log } else { u.state.nodes[i].log };
    let old=representing(g,s.nodes[i].log); let old_disk=representing(g,s.nodes[i].disk.log);
    if !disk && a == Action::ClientRequest(i) { assert(u.created.contains(h)); assert(prefix_of(h,h)); }
    else if disk { if a == Action::Ready(i) { assert(prefix_of(h,old)); } else { assert(prefix_of(h,old_disk)); } }
    else if a == Action::Restart(i) { assert(prefix_of(h,old_disk)); }
    else if let Action::Receive { m,how: Receive::AppendExtend } = a {
        if m.dest == i {
            assert(message_rep(g,m)); let canonical=representing_message(g,m);
            election::preserve_message(s,c,Action::Stutter,m);
            if m.body->AppendRequest_prev+m.body->AppendRequest_entries.len() > s.nodes[i].log.len() {
                append_extends_canonical(g,c,m,canonical);
                assert(prefix_of(h,canonical));
            } else { assert(h =~= s.nodes[i].log); assert(prefix_of(h,old)); }
        } else { assert(prefix_of(h,old)); }
    } else { assert(prefix_of(h,old)); }
}
pub proof fn preserve_message_rep(g: ProofState,c: Constants,a: Action,m: Message)
    requires inductive(g,c),enabled(g.state,c,a),advance(g,c,a).state.pending.count(m) > 0 || advance(g,c,a).state.messages.count(m) > 0
    ensures message_rep(advance(g,c,a),m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    let s=g.state; let u=advance(g,c,a);
    if s.pending.count(m) > 0 || s.messages.count(m) > 0 { let h=representing_message(g,m); assert(u.created.contains(h)); }
    else if m.body is AppendRequest {
        assert(c.servers.contains(m.source)); let h=representing(g,s.nodes[m.source].log);
        assert(segment(m,h)); assert(u.created.contains(h));
    } else {
        let h=representing(g,s.nodes[m.source].log);
        assert(segment(m,h)); assert(u.created.contains(h));
    }
}
pub proof fn preserve_inductive(g: ProofState,c: Constants,a: Action)
    requires inductive(g,c),enabled(g.state,c,a)
    ensures inductive(advance(g,c,a),c)
{
    origins::preserve_inductive(g.state,c,a); let u=advance(g,c,a);
    assert forall |h: Seq<nat>| u.created.contains(h) implies #[trigger] origins::log_origins(u.state,c,h,0) by { preserve_created_origin(g,c,a,h); }
    assert forall |h: Seq<nat>,v: Seq<nat>| u.created.contains(h) && u.created.contains(v) implies #[trigger] matching(h,v) by { preserve_created_pair(g,c,a,h,v); }
    assert forall |i: int| c.servers.contains(i) implies #[trigger] represented(u,u.state.nodes[i].log) by { preserve_log_rep(g,c,a,i,false); }
    assert forall |i: int| c.servers.contains(i) implies #[trigger] represented(u,u.state.nodes[i].disk.log) by { preserve_log_rep(g,c,a,i,true); }
    assert forall |m: Message| #[trigger] u.state.pending.count(m) > 0 implies message_rep(u,m) by { preserve_message_rep(g,c,a,m); }
    assert forall |m: Message| #[trigger] u.state.messages.count(m) > 0 implies message_rep(u,m) by { preserve_message_rep(g,c,a,m); }
}
pub proof fn log_matching_from_inductive(g: ProofState,c: Constants)
    requires inductive(g,c)
    ensures log_matching(g.state,c)
{
    let s=g.state;
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 1 <= k <= s.nodes[i].log.len() && k <= s.nodes[j].log.len()
        && s.nodes[i].log[k-1] == s.nodes[j].log[k-1] implies sub(s.nodes[i].log,1,k) == sub(s.nodes[j].log,1,k) by {
        let a=representing(g,s.nodes[i].log); let b=representing(g,s.nodes[j].log);
        assert(matching(a,b)); matching_prefix(s.nodes[i].log,s.nodes[j].log,a,b);
        assert(sub(s.nodes[i].log,1,k) =~= sub(s.nodes[j].log,1,k));
    }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int) -> (g: ProofState)
    requires election::safety_spec(b,c),k >= 0
    ensures g.state == b[k],inductive(g,c),log_matching(b[k],c)
    decreases k
{
    let g=if k == 0 { initial_inductive(c); initial_proof(c) }
    else {
        let old=safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve_inductive(old,c,a); advance(old,c,a)
    };
    log_matching_from_inductive(g,c); g
}
pub proof fn log_matching_correct(b: Behavior<LState>,c: Constants)
    requires election::safety_spec(b,c)
    ensures forall |k: int| k >= 0 ==> #[trigger] log_matching(b[k],c)
{
    assert forall |k: int| k >= 0 implies #[trigger] log_matching(b[k],c) by { safety_at(b,c,k); }
}
} // verus!
