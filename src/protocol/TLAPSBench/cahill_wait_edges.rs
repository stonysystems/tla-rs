//! Relate the protocol's selected lock owner to a functional wait graph.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_support as support;
use super::cahill_locks as locks;
use super::cahill_wait_graph as graph;
verus! {
pub open spec fn next_wait(s: LState,c: Constants,t: int) -> Option<int> {
    if active(s.history).contains(t) && s.txns[t].waiting is Some && c.keys.contains(s.txns[t].waiting.unwrap()) { owner(s,s.txns[t].waiting.unwrap()) } else { None }
}
pub open spec fn edges(s: LState,c: Constants) -> spec_fn(int) -> Option<int> { |t: int| next_wait(s,c,t) }
pub open spec fn waiting(s: LState,t: int,k: int) -> LState { LState { txns: s.txns.insert(t,LTxn { waiting: Some(k),..s.txns[t] }),..s } }
pub proof fn owner_member(s: LState,k: int,t: int)
    requires owner(s,k) == Some(t)
    ensures active(s.history).contains(t),s.txns[t].xlocks.contains(k)
{
    let q=active(s.history).filter(|r: int| s.txns[r].xlocks.contains(k)); assert(!q.is_empty());
    let r=choose |r: int| q.contains(r); assert(r == t);
}
pub proof fn waiting_support(s: LState,c: Constants,t: int,k: int)
    requires support::inductive(s,c),c.txns.contains(t),active(s.history).contains(t),c.keys.contains(k)
    ensures support::inductive(waiting(s,t,k),c),locks::retains(s,waiting(s,t,k),c),locks::exclusive(s,c) ==> locks::exclusive(waiting(s,t,k),c)
{
    let u=waiting(s,t,k); assert(u.txns.dom() =~= c.txns);
    assert forall |r: int| c.txns.contains(r) implies #[trigger] support::node(u,c,r) by { assert(support::node(s,c,r)); }
}
pub proof fn waiting_owner(s: LState,t: int,k: int,key: int)
    ensures owner(waiting(s,t,k),key) == owner(s,key)
{
    assert(active(waiting(s,t,k).history).filter(|r: int| waiting(s,t,k).txns[r].xlocks.contains(key)) =~= active(s.history).filter(|r: int| s.txns[r].xlocks.contains(key)));
}
pub proof fn changed(s: LState,c: Constants,t: int,k: int)
    ensures forall |x: int| x != t ==> #[trigger] next_wait(waiting(s,t,k),c,x) == next_wait(s,c,x)
{
    assert forall |x: int| x != t implies #[trigger] next_wait(waiting(s,t,k),c,x) == next_wait(s,c,x) by { waiting_owner(s,t,k,s.txns[x].waiting.unwrap()); }
}
pub proof fn edge_equivalent(s: LState,c: Constants,t: int,k: int,x: int,y: int)
    ensures wait_edge(s,c,t,k,x,y) <==> next_wait(waiting(s,t,k),c,x) == Some(y)
{
    let key=if x == t { k } else { s.txns[x].waiting.unwrap() }; waiting_owner(s,t,k,key);
    if next_wait(waiting(s,t,k),c,x) == Some(y) { owner_member(s,key,y); }
}
pub proof fn path_equivalent(s: LState,c: Constants,t: int,k: int,p: Seq<int>)
    ensures deadlock_path(s,c,t,k,p) <==> graph::cycle(edges(waiting(s,t,k),c),p) && p[0] == t
{
    let f=edges(waiting(s,t,k),c);
    if deadlock_path(s,c,t,k,p) {
        edge_equivalent(s,c,t,k,p.last(),t);
        assert forall |i: int| 0 <= i < p.len()-1 implies #[trigger] f(p[i]) == Some(p[i+1]) by { assert(wait_edge(s,c,t,k,p[i],p[i+1])); edge_equivalent(s,c,t,k,p[i],p[i+1]); }
        assert(graph::cycle(f,p));
    }
    if graph::cycle(f,p) && p[0] == t {
        edge_equivalent(s,c,t,k,p.last(),t);
        assert forall |i: int| 0 <= i < p.len()-1 implies #[trigger] wait_edge(s,c,t,k,p[i],p[i+1]) by { assert(f(p[i]) == Some(p[i+1])); edge_equivalent(s,c,t,k,p[i],p[i+1]); }
    }

}
pub proof fn owner_retained(s: LState,u: LState,c: Constants,k: int)
    requires support::inductive(s,c),support::inductive(u,c),locks::exclusive(s,c),locks::retains(s,u,c),owner(u,k) is Some
    ensures owner(s,k) == owner(u,k)
{
    let t=owner(u,k).unwrap(); owner_member(u,k,t); assert(c.txns.contains(t)); assert(u.txns[t].xlocks.subset_of(s.txns[t].xlocks)); locks::owner_correct(s,c,k,t);
}
pub proof fn retained(s: LState,u: LState,c: Constants)
    requires support::inductive(s,c),support::inductive(u,c),locks::exclusive(s,c),locks::retains(s,u,c),
        forall |x: int| #[trigger] next_wait(u,c,x) is Some ==> active(s.history).contains(x) && u.txns[x].waiting == s.txns[x].waiting
    ensures graph::subgraph(edges(s,c),edges(u,c))
{
    assert forall |x: int| #[trigger] next_wait(u,c,x) is Some implies next_wait(s,c,x) == next_wait(u,c,x) by {
        let k=u.txns[x].waiting.unwrap(); owner_retained(s,u,c,k);
    }
}
pub proof fn no_return(s: LState,c: Constants,t: int,k: int)
    requires graph::acyclic(edges(s,c)),!deadlocked(s,c,t,k)
    ensures graph::acyclic(edges(waiting(s,t,k),c))
{
    let f=edges(s,c); let g=edges(waiting(s,t,k),c); changed(s,c,t,k);
    assert forall |p: Seq<int>| !#[trigger] graph::cycle(g,p) by {
        if graph::cycle(g,p) {
            graph::changed_member(f,g,p,t); let i=choose |i: int| 0 <= i < p.len() && p[i] == t;
            graph::rotate(g,p,i); path_equivalent(s,c,t,k,graph::rotation(p,i)); assert(deadlock_path(s,c,t,k,graph::rotation(p,i))); assert(false);
        }
    }
}
} // verus!
