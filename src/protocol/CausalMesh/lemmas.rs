//! Foundational lemmas: bounds built from contributors, availability, and
//! dependency chains.
use vstd::prelude::*;
use super::vc::*;
use super::ring::*;
use super::types::*;
use super::model::*;
use super::invariants::*;

verus! {

/// Knowledge: a write below a least upper bound is below one contributor.
pub proof fn lemma_version_below_lub(c: Constants, s: State, base: VC, parts: spec_fn(VC) -> bool,
                                     r: VC, w: Version)
    requires
        writes_ok(c, s), s.writes.contains(w), lub_of(c.n, base, parts, r), le(w.vc, r),
        known(s, c.n, base), base.len() == c.n,
        forall|p: VC| #[trigger] parts(p) ==> known(s, c.n, p) && p.len() == c.n,
    ensures le(w.vc, base) || exists|p: VC| #[trigger] parts(p) && le(w.vc, p),
{
    reveal(writes_ok);
    let o = w.origin;
    assert(server(c.n, o) && w.vc[o] >= 1 && w.vc.len() == c.n);
    assert(w.vc[o] <= r[o]);
    if r[o] == base[o] {
        reveal(known);
        assert(base[o] >= 1);
        let v = choose|v: Version| #[trigger] s.writes.contains(v) && v.origin == o && v.vc[o] == base[o] && le(v.vc, base);
        assert(le(w.vc, v.vc));
        lemma_le_trans(w.vc, v.vc, base);
    } else {
        let p = choose|p: VC| #[trigger] parts(p) && p[o] == r[o];
        assert(known(s, c.n, p));
        reveal(known);
        assert(p[o] >= 1);
        let v = choose|v: Version| #[trigger] s.writes.contains(v) && v.origin == o && v.vc[o] == p[o] && le(v.vc, p);
        assert(le(w.vc, v.vc));
        lemma_le_trans(w.vc, v.vc, p);
    }
}

pub proof fn lemma_lub_sound(s: State, n: nat, base: VC, parts: spec_fn(VC) -> bool, r: VC)
    requires lub_of(n, base, parts, r), sound(s, n, base),
        forall|p: VC| #[trigger] parts(p) ==> sound(s, n, p),
    ensures sound(s, n, r),
{
    assert forall|o: int| 0 <= o < n implies #[trigger] r[o] <= ctr(s, o) by {
        if r[o] != base[o] {
            let p = choose|p: VC| #[trigger] parts(p) && p[o] == r[o];
            assert(sound(s, n, p));
        }
    }
    reveal(known);
    assert forall|o: int| 0 <= o < n && #[trigger] r[o] >= 1 implies
        exists|v: Version| #[trigger] s.writes.contains(v) && v.origin == o && v.vc[o] == r[o] && le(v.vc, r) by {
        if r[o] == base[o] {
            let v = choose|v: Version| #[trigger] s.writes.contains(v) && v.origin == o && v.vc[o] == base[o] && le(v.vc, base);
            lemma_le_trans(v.vc, base, r);
        } else {
            let p = choose|p: VC| #[trigger] parts(p) && p[o] == r[o];
            assert(sound(s, n, p));
            let v = choose|v: Version| #[trigger] s.writes.contains(v) && v.origin == o && v.vc[o] == p[o] && le(v.vc, p);
            lemma_le_trans(v.vc, p, r);
        }
    }
}

pub proof fn lemma_lub_avail(c: Constants, s: State, base: VC, parts: spec_fn(VC) -> bool, r: VC)
    requires lub_of(c.n, base, parts, r), avail(c, s, base),
        forall|p: VC| #[trigger] parts(p) ==> avail(c, s, p),
        writes_ok(c, s),
    ensures avail(c, s, r),
{
    reveal(avail);
    assert forall|v: Version, q: int| #![trigger s.writes.contains(v), s.seen[q].contains(v)]
        s.writes.contains(v) && v.vc[v.origin] <= r[v.origin] && server(c.n, q)
        implies s.seen[q].contains(v) by {
        reveal(writes_ok);
        let o = v.origin;
        assert(server(c.n, o));
        if r[o] != base[o] {
            let p = choose|p: VC| #[trigger] parts(p) && p[o] == r[o];
            assert(avail(c, s, p));
        }
    }
}

pub proof fn lemma_avail_down(c: Constants, s: State, x: VC, y: VC)
    requires avail(c, s, x), le(y, x), writes_ok(c, s), x.len() == c.n,
    ensures avail(c, s, y),
{
    reveal(avail);
    assert forall|v: Version, q: int| #![trigger s.writes.contains(v), s.seen[q].contains(v)]
        s.writes.contains(v) && v.vc[v.origin] <= y[v.origin] && server(c.n, q)
        implies s.seen[q].contains(v) by {
        reveal(writes_ok);
        assert(y[v.origin] <= x[v.origin]);
    }
}

/// The exact join is a least upper bound built from its arguments.
pub proof fn lemma_join_lub_of(n: nat, a: VC, b: VC)
    requires a.len() == n, b.len() == n
    ensures lub_of(n, a, |x: VC| x == b, join(a, b)),
{
    lemma_join_lub(a, b);
    let parts = |x: VC| x == b;
    assert forall|i: int| 0 <= i < n implies (#[trigger] join(a, b)[i] == a[i]
        || exists|p: VC| #[trigger] parts(p) && p[i] == join(a, b)[i]) by {
        if join(a, b)[i] != a[i] { assert(parts(b) && b[i] == join(a, b)[i]); }
    }
}

// ---- Dependency chains ----

pub open spec fn map_le(d1: Map<int, VC>, d2: Map<int, VC>) -> bool {
    forall|k: int| #[trigger] d1.dom().contains(k) ==> d2.dom().contains(k) && le(d1[k], d2[k])
}

pub proof fn lemma_chain_mono(ic1: Set<Version>, d1: Map<int, VC>, ic2: Set<Version>, d2: Map<int, VC>,
                              path: Seq<Version>)
    requires chain(ic1, d1, path), ic1.subset_of(ic2), map_le(d1, d2)
    ensures chain(ic2, d2, path)
{
    reveal(chain);
    assert(d2.dom().contains(path[0].key));
    lemma_le_trans(path[0].vc, d1[path[0].key], d2[path[0].key]);
}

pub proof fn lemma_reached_mono(ic1: Set<Version>, d1: Map<int, VC>, ic2: Set<Version>, d2: Map<int, VC>)
    requires ic1.subset_of(ic2), map_le(d1, d2)
    ensures forall|v: Version| #[trigger] reached(ic1, d1).contains(v) ==> reached(ic2, d2).contains(v)
{
    assert forall|v: Version| #[trigger] reached(ic1, d1).contains(v) implies reached(ic2, d2).contains(v) by {
        let path = choose|path: Seq<Version>| #[trigger] chain(ic1, d1, path) && path.last() == v;
        lemma_chain_mono(ic1, d1, ic2, d2, path);
        lemma_chain_ends(ic2, d2, path);
        assert(exists|p: Seq<Version>| #[trigger] chain(ic2, d2, p) && p.last() == v);
    }
}

/// Extend a chain by one dependency step.
pub proof fn lemma_reached_step(ic: Set<Version>, d: Map<int, VC>, u: Version, x: Version)
    requires reached(ic, d).contains(u), ic.contains(x), matches(u.deps, x)
    ensures reached(ic, d).contains(x)
{
    let path = choose|path: Seq<Version>| #[trigger] chain(ic, d, path) && path.last() == u;
    let p2 = path.push(x);
    reveal(chain);
    assert(chain(ic, d, p2)) by {
        assert forall|t: int| 0 <= t < p2.len() implies ic.contains(#[trigger] p2[t]) by {
            if t < path.len() { assert(p2[t] == path[t]); }
        }
        assert forall|t: int, u2: int| #![trigger p2[t], p2[u2]]
            0 <= t && u2 == t + 1 && u2 < p2.len() implies matches(p2[t].deps, p2[u2]) by {
            if u2 < path.len() { assert(p2[t] == path[t] && p2[u2] == path[u2]); }
            else { assert(p2[t] == path.last()); }
        }
    }
    assert(p2.last() == x);
    assert(exists|p: Seq<Version>| #[trigger] chain(ic, d, p) && p.last() == x);
}

/// Prepend a version that meets d to a chain from its own deps.
pub proof fn lemma_reached_prepend(ic: Set<Version>, d: Map<int, VC>, v: Version, u: Version)
    requires ic.contains(v), matches(d, v), reached(ic, v.deps).contains(u)
    ensures reached(ic, d).contains(u)
{
    let path = choose|path: Seq<Version>| #[trigger] chain(ic, v.deps, path) && path.last() == u;
    let p2 = seq![v] + path;
    reveal(chain);
    assert(chain(ic, d, p2)) by {
        assert forall|t: int| 0 <= t < p2.len() implies ic.contains(#[trigger] p2[t]) by {
            if t > 0 { assert(p2[t] == path[t - 1]); }
        }
        assert forall|t: int, u2: int| #![trigger p2[t], p2[u2]]
            0 <= t && u2 == t + 1 && u2 < p2.len() implies matches(p2[t].deps, p2[u2]) by {
            if t == 0 { assert(p2[u2] == path[0]); }
            else { assert(p2[t] == path[t - 1] && p2[u2] == path[u2 - 1]); }
        }
    }
    assert(p2.last() == u);
    assert(exists|p: Seq<Version>| #[trigger] chain(ic, d, p) && p.last() == u);
}

/// Along a chain, clocks only decrease, so every element is below a dependency.
pub proof fn lemma_chain_below(c: Constants, s: State, ic: Set<Version>, d: Map<int, VC>,
                               path: Seq<Version>, t: int)
    requires chain(ic, d, path), 0 <= t < path.len(), ic.subset_of(s.writes), writes_ok(c, s)
    ensures exists|k: int| #[trigger] d.dom().contains(k) && le(path[t].vc, d[k])
    decreases t
{
    reveal(chain);
    if t == 0 {
        assert(d.dom().contains(path[0].key));
    } else {
        lemma_chain_below(c, s, ic, d, path, t - 1);
        let k = choose|k: int| #[trigger] d.dom().contains(k) && le(path[t - 1].vc, d[k]);
        assert(matches(path[t - 1].deps, path[t]));
        let kk = path[t].key;
        assert(s.writes.contains(path[t - 1]));
        reveal(writes_ok);
        assert(le(path[t - 1].deps[kk], path[t - 1].vc));
        lemma_le_trans(path[t].vc, path[t - 1].deps[kk], path[t - 1].vc);
        lemma_le_trans(path[t].vc, path[t - 1].vc, d[k]);
    }
}

pub proof fn lemma_reached_below(c: Constants, s: State, ic: Set<Version>, d: Map<int, VC>, u: Version)
    requires reached(ic, d).contains(u), ic.subset_of(s.writes), writes_ok(c, s)
    ensures exists|k: int| #[trigger] d.dom().contains(k) && le(u.vc, d[k]), s.writes.contains(u)
{
    let path = choose|path: Seq<Version>| #[trigger] chain(ic, d, path) && path.last() == u;
    lemma_chain_ends(ic, d, path);
    lemma_chain_below(c, s, ic, d, path, path.len() - 1);
}

} // verus!
