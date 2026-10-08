//! The benchmark's finite recursive cycle search returns no cycle nodes.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_serializable as serial;
use super::cahill_support as support;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::set_lib::group_set_lib_default, vstd::set::Set::lemma_map_contains, vstd::set::Set::lemma_flatten_contains };
pub open spec fn nodes(edges: Set<(int,int)>) -> Set<int> { edges.map(|p: (int,int)| p.0).union(edges.map(|p: (int,int)| p.1)) }
pub open spec fn neighbors(edges: Set<(int,int)>,n: int) -> Set<int> { edges.filter(|p: (int,int)| p.0 == n).map(|p: (int,int)| p.1) }
pub open spec fn search(edges: Set<(int,int)>,n: int,remaining: Set<int>) -> Set<int>
    decreases remaining.len(),0nat,0nat
{
    if !remaining.contains(n) { set![n] }
    else { children(edges,remaining.remove(n),neighbors(edges,n)) }
}
pub open spec fn children(edges: Set<(int,int)>,remaining: Set<int>,todo: Set<int>) -> Set<int>
    decreases remaining.len(),1nat,todo.len()
{
    if todo.is_empty() { Set::empty() }
    else {
        let n=choose |n: int| todo.contains(n);
        search(edges,n,remaining).union(children(edges,remaining,todo.remove(n)))
    }
}
pub proof fn children_map(edges: Set<(int,int)>,remaining: Set<int>,todo: Set<int>)
    ensures children(edges,remaining,todo) == todo.map(|n: int| search(edges,n,remaining)).flatten()
    decreases todo.len()
{
    let results=todo.map(|n: int| search(edges,n,remaining));
    if todo.is_empty() { assert(results =~= Set::<Set<int>>::empty()); assert(results.flatten() =~= Set::<int>::empty()); }
    else {
        let n=choose |n: int| todo.contains(n); children_map(edges,remaining,todo.remove(n));
        let tail=todo.remove(n).map(|n: int| search(edges,n,remaining));
        assert forall |v: int| #![trigger results.flatten().contains(v)] results.flatten().contains(v) <==> search(edges,n,remaining).union(tail.flatten()).contains(v) by {
            if results.flatten().contains(v) {
                let q=choose |q: Set<int>| #![trigger results.contains(q)] results.contains(q) && q.contains(v);
                let w=choose |w: int| todo.contains(w) && search(edges,w,remaining) == q;
                if w != n { assert(todo.remove(n).contains(w)); assert(tail.contains(q)); }
            }
            if search(edges,n,remaining).contains(v) { assert(results.contains(search(edges,n,remaining))); }
            if tail.flatten().contains(v) {
                let q=choose |q: Set<int>| #![trigger tail.contains(q)] tail.contains(q) && q.contains(v);
                let w=choose |w: int| #![trigger search(edges,w,remaining)] todo.remove(n).contains(w) && search(edges,w,remaining) == q;
                assert(results.contains(q));
            }
        }
    }
}
pub proof fn source_equation(edges: Set<(int,int)>,n: int,visited: Set<int>)
    requires nodes(edges).contains(n)
    ensures search(edges,n,nodes(edges).difference(visited)) ==
        if visited.contains(n) { set![n] } else {
            neighbors(edges,n).map(|w: int| search(edges,w,nodes(edges).difference(visited.insert(n)))).flatten()
        }
{
    assert(nodes(edges).difference(visited).remove(n) =~= nodes(edges).difference(visited.insert(n)));
    children_map(edges,nodes(edges).difference(visited.insert(n)),neighbors(edges,n));
}
pub proof fn neighbor(edges: Set<(int,int)>,n: int,w: int)
    requires neighbors(edges,n).contains(w)
    ensures edges.contains((n,w)),nodes(edges).contains(n),nodes(edges).contains(w)
{
    let p=choose |p: (int,int)| #![trigger edges.contains(p)] edges.contains(p) && p.0 == n && p.1 == w; assert(p == (n,w));
    assert(edges.map(|p: (int,int)| p.0).contains(n)); assert(edges.map(|p: (int,int)| p.1).contains(w));
}
pub proof fn empty_search(edges: Set<(int,int)>,n: int,remaining: Set<int>,rank: spec_fn(int) -> int)
    requires nodes(edges).contains(n),remaining.subset_of(nodes(edges)),
        forall |p: (int,int)| #![trigger edges.contains(p)] edges.contains(p) ==> rank(p.0) < rank(p.1),
        forall |v: int| nodes(edges).difference(remaining).contains(v) ==> rank(v) < rank(n)
    ensures search(edges,n,remaining).is_empty()
    decreases remaining.len()
{
    if !remaining.contains(n) { assert(nodes(edges).difference(remaining).contains(n)); assert(false); }
    assert(remaining.contains(n)); let next=neighbors(edges,n); let rest=remaining.remove(n);
    assert forall |w: int| next.contains(w) implies #[trigger] search(edges,w,rest).is_empty() by {
        neighbor(edges,n,w); assert(rank(n) < rank(w));
        assert forall |v: int| nodes(edges).difference(rest).contains(v) implies rank(v) < rank(w) by {
            if v != n { assert(nodes(edges).difference(remaining).contains(v)); }
        }
        empty_search(edges,w,rest,rank);
    }
    let results=next.map(|w: int| search(edges,w,rest));
    children_map(edges,rest,next);
    assert(search(edges,n,remaining) == results.flatten());
    assert forall |v: int| !results.flatten().contains(v) by {
        if results.flatten().contains(v) {
            let q=choose |q: Set<int>| #![trigger results.contains(q)] results.contains(q) && q.contains(v);
            let w=choose |w: int| next.contains(w) && search(edges,w,rest) == q;
            assert(search(edges,w,rest).is_empty());
        }
    }
}
pub open spec fn edges(h: Seq<Event>,c: Constants) -> Set<(int,int)> {
    let ct=committed(h); ct.map(|t: int| ct.map(|w: int| (t,w))).flatten().filter(|p: (int,int)| dependency(h,c,p.0,p.1))
}
pub proof fn edge_member(h: Seq<Event>,c: Constants,t: int,w: int)
    ensures edges(h,c).contains((t,w)) <==> dependency(h,c,t,w)
{
    if dependency(h,c,t,w) {
        let ct=committed(h); let row=ct.map(|w: int| (t,w)); assert(row.contains((t,w)));
        assert(ct.map(|t: int| ct.map(|w: int| (t,w))).contains(row));
        assert(ct.map(|t: int| ct.map(|w: int| (t,w))).flatten().contains((t,w)));
    }
}
pub open spec fn cycle_nodes(h: Seq<Event>,c: Constants) -> Set<int> {
    let es=edges(h,c); es.map(|p: (int,int)| p.0).map(|n: int| search(es,n,nodes(es))).flatten()
}
pub proof fn empty_nodes(h: Seq<Event>,c: Constants,rank: spec_fn(int) -> int)
    requires forall |p: (int,int)| #![trigger edges(h,c).contains(p)] edges(h,c).contains(p) ==> rank(p.0) < rank(p.1)
    ensures cycle_nodes(h,c).is_empty()
{
    let es=edges(h,c); let starts=es.map(|p: (int,int)| p.0);
    assert forall |n: int| starts.contains(n) implies #[trigger] search(es,n,nodes(es)).is_empty() by {
        empty_search(es,n,nodes(es),rank);
    }
    let results=starts.map(|n: int| search(es,n,nodes(es)));
    assert forall |v: int| !results.flatten().contains(v) by {
        if results.flatten().contains(v) {
            let q=choose |q: Set<int>| #![trigger results.contains(q)] results.contains(q) && q.contains(v);
            let n=choose |n: int| #![trigger starts.contains(n)] starts.contains(n) && search(es,n,nodes(es)) == q;
            assert(search(es,n,nodes(es)).is_empty());
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures cycle_nodes(b[time].history,c).is_empty(),serializable(b[time],c)
{
    support::at(b,c,time); super::cahill_lifecycle::at(b,c,time); super::cahill_unique::at(b,c,time);
    super::cahill_writer_intervals::at(b,c,time); super::cahill_conflicts::at(b,c,time); super::cahill_overlap_safety::at(b,c,time);
    let s=b[time]; let rank=|t: int| serial::rank(s,t);
    assert forall |p: (int,int)| #![trigger edges(s.history,c).contains(p)] edges(s.history,c).contains(p) implies rank(p.0) < rank(p.1) by { serial::dependency_rank(s,c,p.0,p.1); }
    empty_nodes(s.history,c,rank); serial::acyclic(s,c);
}
pub proof fn benchmark_serializable(b: Behavior<LState>,c: Constants)
    requires support::safety_spec(b,c)
    ensures forall |time: int| time >= 0 ==> #[trigger] cycle_nodes(b[time].history,c).is_empty(),
        forall |time: int| time >= 0 ==> #[trigger] serializable(b[time],c)
{
    assert forall |time: int| time >= 0 implies #[trigger] cycle_nodes(b[time].history,c).is_empty() by { at(b,c,time); }
    serial::benchmark_serializable(b,c);
}
} // verus!
