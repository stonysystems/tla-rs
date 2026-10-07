//! Exact historical prefixes and comparability of logs ending in the same term.
use vstd::prelude::*;
use super::etcd::{*,sub};
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::etcd_logs::{self as logs,ProofState};
use super::etcd_order as order;
use super::temporal::Behavior;
verus! {
pub open spec fn closed(g: ProofState) -> bool {
    forall |h: Seq<nat>,k: int| g.created.contains(h) && 0 <= k <= h.len() ==> g.created.contains(#[trigger] sub(h,1,k))
}
pub open spec fn same_term(a: Seq<nat>,b: Seq<nat>) -> bool {
    last_term(a) == last_term(b) && a.len() <= b.len() ==> logs::prefix_of(a,b)
}
pub open spec fn inductive(g: ProofState,c: Constants) -> bool {
    logs::inductive(g,c) && closed(g)
    && forall |a: Seq<nat>,b: Seq<nat>| g.created.contains(a) && g.created.contains(b) ==> #[trigger] same_term(a,b)
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(logs::initial_proof(c),c)
{
    logs::initial_inductive(c); let g=logs::initial_proof(c);
    assert forall |h: Seq<nat>,k: int| g.created.contains(h) && 0 <= k <= h.len() implies g.created.contains(#[trigger] sub(h,1,k)) by { assert(sub(h,1,k) =~= h); }
}
pub proof fn represented_is_created(g: ProofState,h: Seq<nat>)
    requires closed(g),logs::represented(g,h)
    ensures g.created.contains(h)
{
    let a=logs::representing(g,h); assert(g.created.contains(sub(a,1,h.len() as int)));
    assert(h =~= sub(a,1,h.len() as int));
}
pub proof fn preserve_closed(g: ProofState,c: Constants,a: Action,h: Seq<nat>,k: int)
    requires inductive(g,c),enabled(g.state,c,a),logs::advance(g,c,a).created.contains(h),0 <= k <= h.len()
    ensures logs::advance(g,c,a).created.contains(sub(h,1,k))
{
    let u=logs::advance(g,c,a); reveal(apply);
    if g.created.contains(h) { assert(g.created.contains(sub(h,1,k))); }
    else if let Action::ClientRequest(i) = a {
        reveal(enabled); let old=g.state.nodes[i].log;
        if k == h.len() { assert(sub(h,1,k) =~= h); }
        else {
            assert(logs::represented(g,old)); represented_is_created(g,old);
            assert(g.created.contains(sub(old,1,k))); assert(sub(h,1,k) =~= sub(old,1,k));
        }
    }
}
pub proof fn old_term_prefix(g: ProofState,c: Constants,i: int,h: Seq<nat>)
    requires logs::inductive(g,c),c.servers.contains(i),g.state.nodes[i].role == Role::Leader,
        g.created.contains(h),h.len() > 0,h.last() == g.state.nodes[i].term
    ensures logs::prefix_of(h,g.state.nodes[i].log)
{
    let s=g.state; let t=s.nodes[i].term; let k=h.len() as int;
    origins::leader_persisted(s,c,i); assert(origins::log_origins(s,c,h,0));
    assert(origins::origin(s,c,t,k));
    let j=choose |j: int| #[trigger] origins::owner(s,c,t,k,j);
    origins::unique_certificate(s,c,t,i,j);
    assert(k <= s.nodes[i].log.len() && s.nodes[i].log[k-1] == t);
    let a=logs::representing(g,s.nodes[i].log); assert(logs::matching(h,a));
    assert(a[k-1] == h[k-1]);
    assert forall |r: int| 0 <= r < h.len() implies #[trigger] h[r] == #[trigger] s.nodes[i].log[r] by {
        assert(h[r] == a[r]); assert(a[r] == s.nodes[i].log[r]);
    }
}
pub proof fn preserve_same_term(g: ProofState,c: Constants,a: Action,h: Seq<nat>,v: Seq<nat>)
    requires inductive(g,c),enabled(g.state,c,a),logs::advance(g,c,a).created.contains(h),logs::advance(g,c,a).created.contains(v)
    ensures same_term(h,v)
{
    reveal(enabled); reveal(apply);
    if g.created.contains(h) && g.created.contains(v) { assert(same_term(h,v)); }
    else if let Action::ClientRequest(i) = a {
        let old=g.state.nodes[i].log; let t=g.state.nodes[i].term;
        if last_term(h) == last_term(v) && h.len() <= v.len() {
            if h.len() == 0 { assert(logs::prefix_of(h,v)); }
            else if g.created.contains(h) {
                old_term_prefix(g,c,i,h); assert(logs::prefix_of(old,old.push(t))); logs::prefix_transitive(h,old,old.push(t));
            } else if g.created.contains(v) {
                old_term_prefix(g,c,i,v); assert(false);
            }
        }
    }
}
pub proof fn preserve(g: ProofState,c: Constants,a: Action)
    requires inductive(g,c),enabled(g.state,c,a)
    ensures inductive(logs::advance(g,c,a),c)
{
    logs::preserve_inductive(g,c,a); let u=logs::advance(g,c,a);
    assert forall |h: Seq<nat>,k: int| u.created.contains(h) && 0 <= k <= h.len() implies u.created.contains(#[trigger] sub(h,1,k)) by { preserve_closed(g,c,a,h,k); }
    assert forall |h: Seq<nat>,v: Seq<nat>| u.created.contains(h) && u.created.contains(v) implies #[trigger] same_term(h,v) by { preserve_same_term(g,c,a,h,v); }
}
pub proof fn represented_same_term(g: ProofState,c: Constants,a: Seq<nat>,b: Seq<nat>)
    requires inductive(g,c),logs::represented(g,a),logs::represented(g,b),last_term(a) == last_term(b),a.len() <= b.len()
    ensures logs::prefix_of(a,b)
{
    represented_is_created(g,a); represented_is_created(g,b); assert(same_term(a,b));
}
pub proof fn up_to_date_retains(g: ProofState,c: Constants,committed: Seq<nat>,voter: Seq<nat>,candidate: Seq<nat>,term: nat)
    requires inductive(g,c),committed.len() > 0,logs::represented(g,committed),logs::represented(g,candidate),
        logs::prefix_of(committed,voter),order::ordered(voter),last_term(candidate) < term,
        last_term(candidate) > last_term(voter) || last_term(candidate) == last_term(voter) && candidate.len() >= voter.len(),
        forall |h: Seq<nat>| g.created.contains(h) && last_term(committed) < last_term(h) < term ==> #[trigger] logs::prefix_of(committed,h)
    ensures logs::prefix_of(committed,candidate)
{
    represented_is_created(g,candidate);
    assert(voter.len() > 0 && voter[committed.len()-1] == committed.last());
    assert(voter[committed.len()-1] <= voter[voter.len()-1]);
    assert(last_term(committed) <= last_term(voter));
    if last_term(committed) < last_term(candidate) { assert(logs::prefix_of(committed,candidate)); }
    else { represented_same_term(g,c,committed,candidate); }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int) -> (g: ProofState)
    requires election::safety_spec(b,c),k >= 0
    ensures g.state == b[k],inductive(g,c)
    decreases k
{
    if k == 0 { initial_inductive(c); logs::initial_proof(c) }
    else {
        let old=safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve(old,c,a); logs::advance(old,c,a)
    }
}
} // verus!
