//! Speculative Paxos Section 4.2: prefix certificates and reconciliation.
//! History contains each replica's final log in each installed normal view.
//! A reconciliation snapshot fences all earlier views at that replica. The
//! merge computes a longest prefix held by a strict majority of the highest
//! normal-view snapshots, then appends the remaining requests. Hashes are exact
//! prefixes here, so collision freedom is an explicit implementation boundary.
use vstd::prelude::*;
use vstd::set_lib::{lemma_len_subset, lemma_set_intersect_union_lens};
verus! {
pub struct Config { pub nodes: Set<int>, pub f: nat }
pub struct Recovery { pub nodes: Set<int>, pub previous: Map<int,int>, pub maximum: int, pub winner: Seq<int> }
pub struct History {
    pub initial: Map<int,Seq<int>>,
    pub logs: Map<(int,int),Seq<int>>,
    pub recoveries: Map<int,Recovery>,
}
pub open spec fn config_ok(c:Config) -> bool { c.nodes.len() == 2*c.f+1 }
pub open spec fn threshold(c:Config) -> nat { (c.f+1)/2+1 }
pub open spec fn fast_size(c:Config) -> nat { c.f+threshold(c) }
pub open spec fn quorum(c:Config,q:Set<int>) -> bool { q.subset_of(c.nodes) && q.len() == c.f+1 }
pub open spec fn prefix(p:Seq<int>,q:Seq<int>) -> bool {
    p.len() <= q.len() && forall|i:int| 0 <= i < p.len() ==> p[i] == q[i]
}
pub open spec fn installed(s:History,v:int,a:int) -> bool { s.logs.dom().contains((v,a)) }
pub open spec fn support(s:History,c:Config,v:int,p:Seq<int>) -> Set<int> {
    c.nodes.filter(|a:int| installed(s,v,a) && prefix(p,s.logs[(v,a)]))
}
pub open spec fn installs(s:History,c:Config,v:int) -> Set<int> {
    c.nodes.filter(|a:int| installed(s,v,a))
}
pub open spec fn fast(s:History,c:Config,v:int,p:Seq<int>) -> bool {
    s.initial.dom().contains(v) && support(s,c,v,p).len() >= fast_size(c)
}
pub open spec fn slow(s:History,c:Config,v:int,p:Seq<int>) -> bool {
    s.initial.dom().contains(v) && prefix(p,s.initial[v]) && installs(s,c,v).len() >= c.f+1
}
pub open spec fn certified(s:History,c:Config,v:int,p:Seq<int>) -> bool { fast(s,c,v,p) || slow(s,c,v,p) }
pub open spec fn highest(r:Recovery) -> Set<int> {
    r.nodes.filter(|a:int| r.previous[a] == r.maximum)
}
pub open spec fn merge_support(s:History,r:Recovery,p:Seq<int>) -> Set<int> {
    highest(r).filter(|a:int| prefix(p,s.logs[(r.maximum,a)]))
}
pub open spec fn majority(s:History,r:Recovery,p:Seq<int>) -> bool {
    2*merge_support(s,r,p).len() > highest(r).len()
}
pub open spec fn recovery_ok(s:History,c:Config,v:int,r:Recovery) -> bool {
    &&& quorum(c,r.nodes) && r.previous.dom() == r.nodes
    &&& forall|a:int| r.nodes.contains(a) ==> 0 <= r.previous[a] < v && installed(s,r.previous[a],a)
        && r.previous[a] <= r.maximum
    &&& exists|a:int| r.nodes.contains(a) && r.previous[a] == r.maximum
    // The snapshot's last normal view covers every earlier installed view.
    // Future messages cannot install a view below the replica's promised target.
    &&& forall|u:int,a:int| installed(s,u,a) && u < v && r.nodes.contains(a) ==> u <= r.previous[a]
    &&& majority(s,r,r.winner)
    &&& forall|p:Seq<int>| #[trigger] majority(s,r,p) ==> p.len() <= r.winner.len()
    &&& prefix(r.winner,s.initial[v])
}
pub open spec fn well_formed(s:History,c:Config) -> bool {
    &&& s.initial.dom().contains(0) && s.initial[0] == Seq::<int>::empty()
    &&& forall|v:int| s.initial.dom().contains(v) ==> v >= 0 && s.initial[v].no_duplicates()
        && (v > 0 ==> s.recoveries.dom().contains(v) && recovery_ok(s,c,v,s.recoveries[v]))
    &&& forall|v:int,a:int| #[trigger] installed(s,v,a) ==> c.nodes.contains(a) && s.initial.dom().contains(v)
        && s.logs[(v,a)].no_duplicates() && prefix(s.initial[v],s.logs[(v,a)])
}
pub proof fn prefix_transitive(a:Seq<int>,b:Seq<int>,c:Seq<int>)
    requires prefix(a,b),prefix(b,c), ensures prefix(a,c),
{
    assert forall|i:int| 0 <= i < a.len() implies a[i] == c[i] by { assert(a[i] == b[i]); assert(b[i] == c[i]); }
}
pub proof fn prefixes_comparable(a:Seq<int>,b:Seq<int>,c:Seq<int>)
    requires prefix(a,c),prefix(b,c), ensures prefix(a,b) || prefix(b,a),
{}
pub proof fn intersection_bound(universe:Set<int>,p:Set<int>,q:Set<int>)
    requires p.subset_of(universe),q.subset_of(universe),
    ensures p.intersect(q).len()+universe.len() >= p.len()+q.len(),
{
    assert(p.union(q).subset_of(universe)); lemma_len_subset(p.union(q),universe);
    lemma_set_intersect_union_lens(p,q);
}
pub proof fn intersects(universe:Set<int>,p:Set<int>,q:Set<int>)
    requires p.subset_of(universe),q.subset_of(universe),p.len()+q.len() > universe.len(),
    ensures exists|a:int| p.contains(a) && q.contains(a),
{
    intersection_bound(universe,p,q);
    vstd::set::lemma_set_choose_len(p.intersect(q));
    let a = p.intersect(q).choose(); assert(p.contains(a) && q.contains(a));
}
pub proof fn majority_is_retained(s:History,c:Config,v:int,r:Recovery,p:Seq<int>)
    requires recovery_ok(s,c,v,r),majority(s,r,p),
    ensures prefix(p,r.winner),prefix(p,s.initial[v]),
{
    let a = merge_support(s,r,p); let b = merge_support(s,r,r.winner); let u = highest(r);
    assert(a.subset_of(u) && b.subset_of(u));
    intersects(u,a,b);
    let n = choose|n:int| a.contains(n) && b.contains(n);
    assert(prefix(p,s.logs[(r.maximum,n)]) && prefix(r.winner,s.logs[(r.maximum,n)]));
    prefixes_comparable(p,r.winner,s.logs[(r.maximum,n)]);
    assert(p.len() <= r.winner.len());
    assert(prefix(p,r.winner)); prefix_transitive(p,r.winner,s.initial[v]);
}
pub proof fn certificate_has_voter(s:History,c:Config,v:int,p:Seq<int>)
    requires config_ok(c),well_formed(s,c),certified(s,c,v,p),
    ensures exists|a:int| c.nodes.contains(a) && installed(s,v,a) && prefix(p,s.logs[(v,a)]),
{
    if fast(s,c,v,p) {
        let q = support(s,c,v,p);
        assert(q.len()>0); vstd::set::lemma_set_choose_len(q);
        let a=q.choose(); assert(q.contains(a));
    } else {
        let q=installs(s,c,v); assert(q.len()>0); vstd::set::lemma_set_choose_len(q);
        let a=q.choose(); assert(q.contains(a));
        prefix_transitive(p,s.initial[v],s.logs[(v,a)]);
    }
}
pub proof fn recovery_maximum_covers_certificate(s:History,c:Config,v:int,p:Seq<int>,b:int)
    requires config_ok(c),well_formed(s,c),certified(s,c,v,p),s.initial.dom().contains(b),v < b,
    ensures s.recoveries[b].maximum >= v,
{
    assert(v >= 0 && b > 0);
    let r=s.recoveries[b];
    let q=if fast(s,c,v,p) { support(s,c,v,p) } else { installs(s,c,v) };
    assert(q.subset_of(c.nodes) && r.nodes.subset_of(c.nodes));
    assert(threshold(c) >= 1);
    assert(q.len() >= c.f+1);
    intersects(c.nodes,q,r.nodes);
    let a=choose|a:int| q.contains(a) && r.nodes.contains(a);
    assert(installed(s,v,a)); assert(v <= r.previous[a] <= r.maximum);
}
pub proof fn later_view_preserves(s:History,c:Config,v:int,p:Seq<int>,b:int)
    requires config_ok(c),well_formed(s,c),certified(s,c,v,p),s.initial.dom().contains(b),v < b,
    ensures prefix(p,s.initial[b]),prefix(p,s.recoveries[b].winner),
    decreases b,
{
    assert(v >= 0 && b > 0);
    let r=s.recoveries[b]; let m=highest(r);
    recovery_maximum_covers_certificate(s,c,v,p,b);
    let a=choose|a:int| r.nodes.contains(a) && r.previous[a] == r.maximum;
    assert(m.contains(a)); assert(installed(s,r.maximum,a));
    assert(s.initial.dom().contains(r.maximum) && r.maximum < b);
    if r.maximum > v {
        later_view_preserves(s,c,v,p,r.maximum);
        assert forall|n:int| m.contains(n) implies merge_support(s,r,p).contains(n) by {
            assert(installed(s,r.maximum,n));
            prefix_transitive(p,s.initial[r.maximum],s.logs[(r.maximum,n)]);
        }
        assert(merge_support(s,r,p) =~= m);
        assert(m != Set::<int>::empty());
        assert(m.len()>0);
        assert(majority(s,r,p));
    } else if slow(s,c,v,p) {
        assert(r.maximum == v);
        assert forall|n:int| m.contains(n) implies merge_support(s,r,p).contains(n) by {
            assert(installed(s,v,n)); prefix_transitive(p,s.initial[v],s.logs[(v,n)]);
        }
        assert(merge_support(s,r,p) =~= m);
        assert(m != Set::<int>::empty());
        assert(m.len()>0);
        assert(majority(s,r,p));
    } else {
        assert(r.maximum == v);
        let q=support(s,c,v,p); let survivors=q.intersect(r.nodes);
        assert(q.subset_of(c.nodes));
        intersection_bound(c.nodes,q,r.nodes);
        assert(survivors.len() >= threshold(c));
        assert forall|n:int| survivors.contains(n) implies merge_support(s,r,p).contains(n) by {
            assert(installed(s,v,n)); assert(v <= r.previous[n] <= r.maximum);
        }
        assert(survivors.subset_of(merge_support(s,r,p)));
        lemma_len_subset(survivors,merge_support(s,r,p));
        assert(m.subset_of(r.nodes)); lemma_len_subset(m,r.nodes);
        assert(2*threshold(c) > c.f+1);
        assert(majority(s,r,p));
    }
    majority_is_retained(s,c,b,r,p);
}
pub proof fn certificates_compatible(s:History,c:Config,v:int,p:Seq<int>,b:int,q:Seq<int>)
    requires config_ok(c),well_formed(s,c),certified(s,c,v,p),certified(s,c,b,q),
    ensures prefix(p,q) || prefix(q,p),
{
    if v < b {
        later_view_preserves(s,c,v,p,b); certificate_has_voter(s,c,b,q);
        let a=choose|a:int| c.nodes.contains(a) && installed(s,b,a) && prefix(q,s.logs[(b,a)]);
        prefix_transitive(p,s.initial[b],s.logs[(b,a)]);
        prefixes_comparable(p,q,s.logs[(b,a)]);
    } else if b < v {
        later_view_preserves(s,c,b,q,v); certificate_has_voter(s,c,v,p);
        let a=choose|a:int| c.nodes.contains(a) && installed(s,v,a) && prefix(p,s.logs[(v,a)]);
        prefix_transitive(q,s.initial[v],s.logs[(v,a)]);
        prefixes_comparable(p,q,s.logs[(v,a)]);
    } else if slow(s,c,v,p) {
        certificate_has_voter(s,c,b,q);
        let a=choose|a:int| c.nodes.contains(a) && installed(s,b,a) && prefix(q,s.logs[(b,a)]);
        prefix_transitive(p,s.initial[v],s.logs[(v,a)]); prefixes_comparable(p,q,s.logs[(v,a)]);
    } else if slow(s,c,b,q) {
        certificate_has_voter(s,c,v,p);
        let a=choose|a:int| c.nodes.contains(a) && installed(s,v,a) && prefix(p,s.logs[(v,a)]);
        prefix_transitive(q,s.initial[b],s.logs[(b,a)]); prefixes_comparable(p,q,s.logs[(v,a)]);
    } else {
        let x=support(s,c,v,p); let y=support(s,c,v,q);
        assert(x.subset_of(c.nodes) && y.subset_of(c.nodes));
        assert(2*fast_size(c) > c.nodes.len()); intersects(c.nodes,x,y);
        let a=choose|a:int| x.contains(a) && y.contains(a);
        prefixes_comparable(p,q,s.logs[(v,a)]);
    }
}
pub proof fn agreement(s:History,c:Config,v:int,p:Seq<int>,b:int,q:Seq<int>,i:int)
    requires config_ok(c),well_formed(s,c),certified(s,c,v,p),certified(s,c,b,q),0 <= i < p.len(),i < q.len(),
    ensures p[i] == q[i],
{ certificates_compatible(s,c,v,p,b,q); }
} // verus!
