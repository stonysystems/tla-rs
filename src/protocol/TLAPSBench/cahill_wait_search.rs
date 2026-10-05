//! The source's successor walk terminates and agrees with the simple deadlock path.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_support as support;
use super::cahill_wait_edges::{self as waits,edges,waiting};
use super::cahill_wait_graph as graph;
use super::temporal::Behavior;
verus! {
pub open spec fn path(f: spec_fn(int) -> Option<int>,t: int,p: Seq<int>) -> bool {
    p.len() > 0 && p[0] == t && p.no_duplicates() && forall |k: int| 0 <= k < p.len()-1 ==> #[trigger] f(p[k]) == Some(p[k+1])
}
pub open spec fn prefix(a: Seq<int>,d: Seq<int>) -> bool { a.len() <= d.len() && forall |k: int| 0 <= k < a.len() ==> #[trigger] a[k] == d[k] }
pub proof fn fresh(f: spec_fn(int) -> Option<int>,g: spec_fn(int) -> Option<int>,t: int,p: Seq<int>,n: int)
    requires graph::acyclic(f),forall |x: int| x != t ==> #[trigger] g(x) == f(x),path(g,t,p),g(p.last()) == Some(n),n != t
    ensures !p.contains(n)
{
    if p.contains(n) {
        let i=choose |i: int| 0 <= i < p.len() && p[i] == n; assert(i > 0); let q=p.skip(i);
        assert(q.no_duplicates()); assert(q[0] == n); assert(q.last() == p.last()); assert(p.last() != t);
        assert forall |k: int| 0 <= k < q.len()-1 implies #[trigger] f(q[k]) == Some(q[k+1]) by {
            assert(q[k] == p[k+i]); assert(p[k+i] != p[0]); assert(g(p[k+i]) == Some(p[k+i+1]));
        }
        assert(graph::cycle(f,q)); assert(false);
    }
}
pub proof fn extend(g: spec_fn(int) -> Option<int>,t: int,p: Seq<int>,n: int)
    requires path(g,t,p),!p.contains(n),g(p.last()) == Some(n)
    ensures path(g,t,p.push(n))
{
    assert(p.push(n).no_duplicates());
    assert forall |k: int| 0 <= k < p.push(n).len()-1 implies #[trigger] g(p.push(n)[k]) == Some(p.push(n)[k+1]) by {
        if k+1 < p.len() { assert(g(p[k]) == Some(p[k+1])); } else { assert(p[k] == p.last()); }
    }
}
pub open spec fn walk(g: spec_fn(int) -> Option<int>,t: int,p: Seq<int>,left: Set<int>) -> Seq<int>
    decreases left.len()
{
    match g(p.last()) {
        None => p,
        Some(n) => if n == t || !left.contains(n) { p } else { walk(g,t,p.push(n),left.remove(n)) },
    }
}
pub proof fn complete(f: spec_fn(int) -> Option<int>,g: spec_fn(int) -> Option<int>,t: int,p: Seq<int>,q: Set<int>,left: Set<int>)
    requires graph::acyclic(f),forall |x: int| x != t ==> #[trigger] g(x) == f(x),path(g,t,p),p.to_set().subset_of(q),left == q.difference(p.to_set()),
        forall |x: int| q.contains(x) && #[trigger] g(x) is Some ==> q.contains(g(x).unwrap())
    ensures path(g,t,walk(g,t,p,left)),prefix(p,walk(g,t,p,left)),walk(g,t,p,left).to_set().subset_of(q),
        g(walk(g,t,p,left).last()) == None || g(walk(g,t,p,left).last()) == Some(t)
    decreases left.len()
{
    p.to_set_ensures();
    if let Some(n)=g(p.last()) {
        if n != t {
            fresh(f,g,t,p,n); assert(q.contains(p.last())); assert(q.contains(n)); assert(!p.to_set().contains(n)); assert(left.contains(n));
            extend(g,t,p,n); let next=p.push(n); next.to_set_ensures(); p.lemma_push_to_set_commute(n); assert(next.to_set() =~= p.to_set().insert(n));
            assert(left.remove(n) =~= q.difference(next.to_set())); assert(next.to_set().subset_of(q)); complete(f,g,t,next,q,left.remove(n));
            let r=walk(g,t,next,left.remove(n)); assert forall |k: int| 0 <= k < p.len() implies #[trigger] p[k] == r[k] by { assert(next[k] == r[k]); }
        }
    }
}
pub proof fn matches_cycle(g: spec_fn(int) -> Option<int>,t: int,p: Seq<int>,q: Seq<int>,k: int)
    requires path(g,t,p),graph::cycle(g,q),q[0] == t,0 <= k < p.len(),k < q.len()
    ensures p[k] == q[k]
    decreases k
{
    if k > 0 { matches_cycle(g,t,p,q,k-1); graph::successor(g,q,k-1); assert(g(p[k-1]) == Some(p[k])); }
}
pub proof fn no_dead_end(g: spec_fn(int) -> Option<int>,t: int,p: Seq<int>,q: Seq<int>)
    requires path(g,t,p),graph::cycle(g,q),q[0] == t
    ensures g(p.last()) is Some
{
    if p.len() > q.len() {
        let k=q.len() as int-1; matches_cycle(g,t,p,q,k); graph::successor(g,q,k); assert(g(p[k]) == Some(p[k+1])); assert(p[k+1] == p[0]); assert(false);
    } else { let k=p.len() as int-1; matches_cycle(g,t,p,q,k); graph::successor(g,q,k); assert(p.last() == p[k]); }
}
pub proof fn correspondence(b: Behavior<LState>,c: Constants,time: int,t: int,k: int)
    requires support::safety_spec(b,c),time >= 0,active(b[time].history).contains(t),c.keys.contains(k)
    ensures {
        let s=b[time]; let f=edges(waiting(s,t,k),c); let r=walk(f,t,seq![t],active(s.history).remove(t));
        path(f,t,r) && r.len() <= active(s.history).len()
        && (f(r.last()) == None || f(r.last()) == Some(t))
        && (deadlocked(s,c,t,k) <==> f(r.last()) == Some(t))
        && (deadlocked(s,c,t,k) ==> deadlock_path(s,c,t,k,r))
        && forall |p: Seq<int>| #[trigger] deadlock_path(s,c,t,k,p) ==> p == r
    },
{
    support::at(b,c,time); super::cahill_deadlocks::at(b,c,time); let s=b[time]; let d=waiting(s,t,k); let old=edges(s,c); let f=edges(d,c); let q=active(s.history);
    let p=seq![t]; p.to_set_ensures(); assert(p.to_set() =~= set![t]); assert(q.difference(p.to_set()) =~= q.remove(t)); waits::changed(s,c,t,k);
    assert forall |x: int| q.contains(x) && #[trigger] f(x) is Some implies q.contains(f(x).unwrap()) by {
        let key=d.txns[x].waiting.unwrap(); waits::owner_member(d,key,f(x).unwrap());
    }
    complete(old,f,t,p,q,q.remove(t)); let r=walk(f,t,p,q.remove(t)); r.unique_seq_to_set(); vstd::set_lib::lemma_len_subset(r.to_set(),q);
    waits::path_equivalent(s,c,t,k,r);
    if deadlocked(s,c,t,k) { let target=choose |target: Seq<int>| deadlock_path(s,c,t,k,target); waits::path_equivalent(s,c,t,k,target); no_dead_end(f,t,r,target); }
    if f(r.last()) == Some(t) { assert(graph::cycle(f,r)); assert(deadlock_path(s,c,t,k,r)); }
    assert forall |target: Seq<int>| #[trigger] deadlock_path(s,c,t,k,target) implies target == r by {
        assert(deadlocked(s,c,t,k)); waits::path_equivalent(s,c,t,k,target); graph::same_start(f,target,r);
    }
}
} // verus!
