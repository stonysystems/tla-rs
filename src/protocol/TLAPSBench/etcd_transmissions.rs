//! Trace witnesses for message creation, release, and the order of later votes.
use vstd::prelude::*;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::temporal::Behavior;
verus! {
pub open spec fn step(b: Behavior<LState>,c: Constants,k: int) -> Action {
    choose |a: Action| enabled(b[k],c,a) && b[k+1] == apply(b[k],c,a)
}
pub proof fn step_valid(b: Behavior<LState>,c: Constants,k: int)
    requires election::safety_spec(b,c),k >= 0
    ensures enabled(b[k],c,step(b,c,k)),b[k+1] == apply(b[k],c,step(b,c,k))
{ assert(next(b[k],b[k+1],c)); reveal(next); }
pub proof fn pending_creation(s: LState,c: Constants,a: Action,m: Message)
    requires enabled(s,c,a),s.pending.count(m) == 0,apply(s,c,a).pending.count(m) > 0
    ensures m.term == s.nodes[m.source].term
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
}
pub proof fn delivery_creation(s: LState,c: Constants,a: Action,m: Message)
    requires enabled(s,c,a),s.messages.count(m) == 0,apply(s,c,a).messages.count(m) > 0
    ensures a == Action::Ready(m.source),s.pending.count(m) > 0
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
}
pub proof fn pending_survives(s: LState,c: Constants,a: Action,m: Message)
    requires apply(s,c,a).pending.count(m) > 0
    ensures a != Action::Restart(m.source),a != Action::Ready(m.source)
{ reveal(apply); broadcast use vstd::multiset::group_multiset_axioms; }
pub proof fn pending_origin(b: Behavior<LState>,c: Constants,k: int,m: Message) -> (j: int)
    requires election::safety_spec(b,c),k >= 0,b[k].pending.count(m) > 0
    ensures 0 <= j < k,b[j].pending.count(m) == 0,b[j].nodes[m.source].term == m.term,
        forall |r: int| j < r <= k ==> #[trigger] b[r].pending.count(m) > 0
    decreases k
{
    broadcast use vstd::multiset::group_multiset_axioms;
    if k == 0 { assert(false); arbitrary() }
    else {
        let p=k-1; step_valid(b,c,p);
        if b[p].pending.count(m) > 0 {
            let j=pending_origin(b,c,p,m);
            assert forall |r: int| j < r <= k implies #[trigger] b[r].pending.count(m) > 0 by { if r < k { assert(b[r].pending.count(m) > 0); } }
            j
        } else { pending_creation(b[p],c,step(b,c,p),m); p }
    }
}
pub proof fn release_origin(b: Behavior<LState>,c: Constants,k: int,m: Message) -> (r: int)
    requires election::safety_spec(b,c),k >= 0,b[k].messages.count(m) > 0
    ensures 0 <= r < k,b[r].pending.count(m) > 0,step(b,c,r) == Action::Ready(m.source)
    decreases k
{
    broadcast use vstd::multiset::group_multiset_axioms;
    if k == 0 { assert(false); arbitrary() }
    else {
        let p=k-1; step_valid(b,c,p);
        if b[p].messages.count(m) > 0 { release_origin(b,c,p,m) }
        else { delivery_creation(b[p],c,step(b,c,p),m); p }
    }
}
pub proof fn vote_origin(b: Behavior<LState>,c: Constants,k: int,v: Ballot) -> (w: (int,Message))
    requires election::safety_spec(b,c),k >= 0,b[k].votes.contains(v)
    ensures 0 <= w.0 < k,b[w.0].pending.count(w.1) > 0,positive(w.1),ballot(w.1) == v,
        step(b,c,w.0) == Action::Ready(v.voter),b[w.0+1].votes.contains(v)
    decreases k
{
    if k == 0 { assert(false); arbitrary() }
    else {
        let p=k-1; step_valid(b,c,p); let a=step(b,c,p);
        if b[p].votes.contains(v) { vote_origin(b,c,p,v) }
        else {
            reveal(apply); reveal(receive); assert(a is Ready); let i=a->Ready_0;
            assert(released_votes(b[p],i).contains(v)); let m=election::released_origin(b[p],i,v);
            (p,m)
        }
    }
}
pub proof fn disk_term_step(s: LState,c: Constants,a: Action,i: int)
    requires election::inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures s.nodes[i].disk.term <= apply(s,c,a).nodes[i].disk.term
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive); assert(election::node_inv(s,c,i));
}
pub proof fn disk_term_interval(b: Behavior<LState>,c: Constants,i: int,lo: int,hi: int)
    requires election::safety_spec(b,c),c.servers.contains(i),0 <= lo <= hi
    ensures b[lo].nodes[i].disk.term <= b[hi].nodes[i].disk.term
    decreases hi-lo
{
    if hi > lo {
        disk_term_interval(b,c,i,lo,hi-1); step_valid(b,c,hi-1); election::safety_at(b,c,hi-1);
        disk_term_step(b[hi-1],c,step(b,c,hi-1),i);
    }
}
pub proof fn votes_monotone(b: Behavior<LState>,c: Constants,lo: int,hi: int)
    requires election::safety_spec(b,c),0 <= lo <= hi
    ensures b[lo].votes.subset_of(b[hi].votes)
    decreases hi-lo
{
    if hi > lo {
        votes_monotone(b,c,lo,hi-1); step_valid(b,c,hi-1);
        reveal(apply); reveal(receive);
        assert(b[hi-1].votes.subset_of(b[hi].votes));
    }
}
pub proof fn released_term(b: Behavior<LState>,c: Constants,m: Message,release: int,k: int)
    requires election::safety_spec(b,c),0 <= release < k,b[release].pending.count(m) > 0,
        step(b,c,release) == Action::Ready(m.source)
    ensures c.servers.contains(m.source),m.term <= b[k].nodes[m.source].disk.term,m.term <= b[k].nodes[m.source].term
{
    origins::safety_at(b,c,release); assert(origins::pending_terms(b[release],m));
    assert(election::pending_inv(b[release],c,m)); step_valid(b,c,release); reveal(apply);
    disk_term_interval(b,c,m.source,release+1,k); election::safety_at(b,c,k); assert(election::node_inv(b[k],c,m.source));
}
pub proof fn creation_precedes_grant(b: Behavior<LState>,c: Constants,create: int,grant: int,release: int,m: Message,v: Message)
    requires election::safety_spec(b,c),create >= 0,0 <= grant < release,m.source == v.source,m.term < v.term,
        b[create].nodes[m.source].term == m.term,b[grant].nodes[v.source].term == v.term,
        step(b,c,release) == Action::Ready(v.source),
        forall |r: int| grant < r <= release ==> #[trigger] b[r].pending.count(v) > 0
    ensures create < grant
{
    if create == grant { assert(false); }
    else if grant < create <= release {
        assert(b[create].pending.count(v) > 0); origins::safety_at(b,c,create); assert(origins::pending_terms(b[create],v));
    } else if create > release {
        assert(b[release].pending.count(v) > 0); released_term(b,c,v,release,create);
    }
}
// The old message was created before the grant of a subsequently released vote.
// This also covers an acknowledgment released after that vote: its creation
// still precedes the grant, because it could not survive a sender restart.
pub proof fn older_message_precedes_vote(b: Behavior<LState>,c: Constants,k: int,m: Message,v: Ballot) -> (w: (int,int,int,Message))
    requires election::safety_spec(b,c),k >= 0,b[k].messages.count(m) > 0,b[k].votes.contains(v),m.source == v.voter,m.term < v.term
    ensures 0 <= w.0 < w.1 < w.2 < k,b[w.0].nodes[m.source].term == m.term,
        positive(w.3),ballot(w.3) == v,b[w.1].nodes[v.voter].term == v.term,
        b[w.2].pending.count(w.3) > 0,step(b,c,w.2) == Action::Ready(v.voter),
        forall |r: int| w.1 < r <= w.2 ==> #[trigger] b[r].pending.count(w.3) > 0
{
    let r=release_origin(b,c,k,m); let j=pending_origin(b,c,r,m);
    let vr=vote_origin(b,c,k,v); let q=pending_origin(b,c,vr.0,vr.1);
    election::safety_at(b,c,k); assert(election::history_inv(b[k],c,v));
    if j >= q {
        if j == q { assert(false); }
        else if j <= vr.0 {
            assert(b[j].pending.count(vr.1) > 0); origins::safety_at(b,c,j);
            assert(origins::pending_terms(b[j],vr.1)); assert(false);
        } else {
            election::safety_at(b,c,vr.0+1); assert(election::history_inv(b[vr.0+1],c,v));
            disk_term_interval(b,c,v.voter,vr.0+1,j); election::safety_at(b,c,j);
            assert(election::node_inv(b[j],c,v.voter)); assert(false);
        }
    }
    (j,q,vr.0,vr.1)
}
} // verus!
