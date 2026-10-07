//! Simple cycles in a functional wait graph and the effect of aborting a cycle member.
use vstd::prelude::*;
verus! {
pub open spec fn cycle(f: spec_fn(int) -> Option<int>,p: Seq<int>) -> bool {
    p.len() > 0 && p.no_duplicates()
    && (forall |k: int| 0 <= k < p.len()-1 ==> #[trigger] f(p[k]) == Some(p[k+1]))
    && f(p.last()) == Some(p[0])
}
pub open spec fn acyclic(f: spec_fn(int) -> Option<int>) -> bool { forall |p: Seq<int>| !#[trigger] cycle(f,p) }
pub open spec fn rotation(p: Seq<int>,k: int) -> Seq<int> { p.skip(k)+p.take(k) }
pub open spec fn rotated_index(len: int,k: int,j: int) -> int { if j < len-k { k+j } else { j-(len-k) } }
pub proof fn rotation_index(p: Seq<int>,k: int,j: int)
    requires 0 <= k < p.len(),0 <= j < p.len()
    ensures 0 <= rotated_index(p.len() as int,k,j) < p.len(),rotation(p,k).len() == p.len(),rotation(p,k)[j] == p[rotated_index(p.len() as int,k,j)]
{}
pub proof fn successor(f: spec_fn(int) -> Option<int>,p: Seq<int>,k: int)
    requires cycle(f,p),0 <= k < p.len()
    ensures f(p[k]) == Some(p[if k+1 < p.len() { k+1 } else { 0 }])
{ if k+1 == p.len() { assert(p[k] == p.last()); } }
pub proof fn rotate(f: spec_fn(int) -> Option<int>,p: Seq<int>,k: int)
    requires cycle(f,p),0 <= k < p.len()
    ensures cycle(f,rotation(p,k)),rotation(p,k)[0] == p[k],rotation(p,k).to_set() =~= p.to_set()
{
    let q=rotation(p,k); rotation_index(p,k,0);
    assert forall |i: int,j: int| 0 <= i < j < q.len() implies q[i] != q[j] by {
        rotation_index(p,k,i); rotation_index(p,k,j); let x=rotated_index(p.len() as int,k,i); let y=rotated_index(p.len() as int,k,j);
        assert(x != y); assert(p[x] != p[y]);
    }
    assert(q.no_duplicates());
    assert forall |j: int| 0 <= j < q.len()-1 implies #[trigger] f(q[j]) == Some(q[j+1]) by {
        rotation_index(p,k,j); rotation_index(p,k,j+1); let x=rotated_index(p.len() as int,k,j); successor(f,p,x);
    }
    rotation_index(p,k,q.len() as int-1); successor(f,p,rotated_index(p.len() as int,k,q.len() as int-1));
    assert(q.to_set() =~= p.to_set()) by {
        assert forall |x: int| q.contains(x) <==> p.contains(x) by {
            if q.contains(x) { let j=choose |j: int| 0 <= j < q.len() && q[j] == x; rotation_index(p,k,j); }
            if p.contains(x) { let j=choose |j: int| 0 <= j < p.len() && p[j] == x; let at=if j >= k { j-k } else { p.len() as int-k+j }; rotation_index(p,k,at); assert(q[at] == x); }
        }
    }
}
pub proof fn matching_position(f: spec_fn(int) -> Option<int>,p: Seq<int>,q: Seq<int>,k: int)
    requires cycle(f,p),cycle(f,q),p[0] == q[0],0 <= k < p.len(),k < q.len()
    ensures p[k] == q[k]
    decreases k
{
    if k > 0 { matching_position(f,p,q,k-1); successor(f,p,k-1); successor(f,q,k-1); }
}
pub proof fn same_start(f: spec_fn(int) -> Option<int>,p: Seq<int>,q: Seq<int>)
    requires cycle(f,p),cycle(f,q),p[0] == q[0]
    ensures p =~= q
{
    if p.len() < q.len() {
        let k=p.len() as int-1; matching_position(f,p,q,k); successor(f,p,k); successor(f,q,k); assert(q[k+1] == q[0]); assert(false);
    } else if q.len() < p.len() {
        let k=q.len() as int-1; matching_position(f,p,q,k); successor(f,p,k); successor(f,q,k); assert(p[k+1] == p[0]); assert(false);
    }
    assert forall |k: int| 0 <= k < p.len() implies p[k] == q[k] by { matching_position(f,p,q,k); }
}
pub proof fn same_member(f: spec_fn(int) -> Option<int>,p: Seq<int>,q: Seq<int>,t: int)
    requires cycle(f,p),cycle(f,q),p.contains(t),q.contains(t)
    ensures p.to_set() =~= q.to_set()
{
    let i=choose |i: int| 0 <= i < p.len() && p[i] == t; let j=choose |j: int| 0 <= j < q.len() && q[j] == t;
    rotate(f,p,i); rotate(f,q,j); same_start(f,rotation(p,i),rotation(q,j));
}
pub proof fn cycle_member(f: spec_fn(int) -> Option<int>,p: Seq<int>,t: int)
    requires cycle(f,p),p.contains(t)
    ensures f(t) is Some,p.contains(f(t).unwrap())
{
    let i=choose |i: int| 0 <= i < p.len() && p[i] == t; successor(f,p,i);
}
pub open spec fn subgraph(f: spec_fn(int) -> Option<int>,g: spec_fn(int) -> Option<int>) -> bool {
    forall |t: int| #[trigger] g(t) is Some ==> f(t) == g(t)
}
pub proof fn copy_cycle(f: spec_fn(int) -> Option<int>,g: spec_fn(int) -> Option<int>,p: Seq<int>)
    requires cycle(g,p),forall |t: int| p.contains(t) ==> #[trigger] f(t) == g(t)
    ensures cycle(f,p)
{
    assert forall |k: int| 0 <= k < p.len()-1 implies #[trigger] f(p[k]) == Some(p[k+1]) by { assert(p.contains(p[k])); }
    assert(p.contains(p.last()));
}
pub proof fn subgraph_acyclic(f: spec_fn(int) -> Option<int>,g: spec_fn(int) -> Option<int>)
    requires acyclic(f),subgraph(f,g)
    ensures acyclic(g)
{
    assert forall |p: Seq<int>| !#[trigger] cycle(g,p) by {
        if cycle(g,p) { assert forall |t: int| p.contains(t) implies #[trigger] f(t) == g(t) by { cycle_member(g,p,t); } copy_cycle(f,g,p); }
    }
}
pub proof fn changed_member(f: spec_fn(int) -> Option<int>,g: spec_fn(int) -> Option<int>,p: Seq<int>,t: int)
    requires acyclic(f),cycle(g,p),forall |x: int| x != t && #[trigger] g(x) is Some ==> f(x) == g(x)
    ensures p.contains(t)
{
    if !p.contains(t) {
        assert forall |x: int| p.contains(x) implies #[trigger] f(x) == g(x) by { cycle_member(g,p,x); }
        copy_cycle(f,g,p);
    }
}
pub proof fn abort_member(f: spec_fn(int) -> Option<int>,g: spec_fn(int) -> Option<int>,u: spec_fn(int) -> Option<int>,t: int,q: Seq<int>,victim: int)
    requires acyclic(f),forall |x: int| x != t && #[trigger] g(x) is Some ==> f(x) == g(x),cycle(g,q),q.contains(t),q.contains(victim),subgraph(g,u),u(victim) == None
    ensures acyclic(u)
{
    assert forall |p: Seq<int>| !#[trigger] cycle(u,p) by {
        if cycle(u,p) {
            assert forall |x: int| p.contains(x) implies #[trigger] g(x) == u(x) by { cycle_member(u,p,x); }
            copy_cycle(g,u,p); changed_member(f,g,p,t); same_member(g,p,q,t); p.to_set_ensures(); q.to_set_ensures(); assert(q.to_set().contains(victim)); assert(p.to_set().contains(victim)); assert(p.contains(victim)); cycle_member(u,p,victim); assert(false);
        }
    }
}
pub proof fn sink_extension(f: spec_fn(int) -> Option<int>,g: spec_fn(int) -> Option<int>,t: int)
    requires acyclic(f),g(t) == None,forall |x: int| #[trigger] g(x) is Some ==> f(x) == g(x) || g(x) == Some(t)
    ensures acyclic(g)
{
    assert forall |p: Seq<int>| !#[trigger] cycle(g,p) by {
        if cycle(g,p) {
            if p.contains(t) { cycle_member(g,p,t); assert(false); }
            assert forall |x: int| p.contains(x) implies #[trigger] f(x) == g(x) by { cycle_member(g,p,x); }
            copy_cycle(f,g,p);
        }
    }
}
} // verus!
