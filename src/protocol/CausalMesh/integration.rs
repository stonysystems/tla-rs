//! Figure 7 integration is safe and complete when the dependencies are
//! available: C-cache stays a causal cut of available versions, and every
//! write reachable from the dependencies becomes visible.
use vstd::prelude::*;
use super::vc::*;
use super::ring::*;
use super::types::*;
use super::model::*;
use super::invariants::*;
use super::lemmas::*;

verus! {

/// A C-cache entry of key k: sound, available, attained, and a written value.
pub open spec fn entry_ok(c: Constants, s: State, k: int, e: Entry) -> bool {
    &&& sound(s, c.n, e.vc)
    &&& avail(c, s, e.vc)
    &&& forall|o: int| 0 <= o < c.n && #[trigger] e.vc[o] >= 1 ==>
        exists|w: Version| #[trigger] s.writes.contains(w) && w.key == k && le(w.vc, e.vc) && w.vc[o] == e.vc[o]
    &&& exists|w: Version| #[trigger] s.writes.contains(w) && w.key == k && le(w.vc, e.vc) && w.value == e.value
}

pub open spec fn entries_ok(c: Constants, s: State, sv: Server) -> bool {
    forall|k: int| #[trigger] sv.ccache.dom().contains(k) ==> entry_ok(c, s, k, sv.ccache[k])
}

pub open spec fn seen_covered(c: Constants, s: State, q: int, sv: Server) -> bool {
    forall|v: Version| #[trigger] s.seen[q].contains(v) ==>
        sv.icache.contains(v) || le(v.vc, entry(sv, c.n, v.key).vc)
}

/// What integration at server q needs to know about q.
pub open spec fn server_ready(c: Constants, s: State, q: int) -> bool {
    let sv = s.servers[q];
    &&& writes_ok(c, s)
    &&& server(c.n, q) && s.servers.len() == c.n && s.seen.len() == c.n
    &&& sv.icache.subset_of(s.seen[q]) && s.seen[q].subset_of(s.writes)
    &&& seen_covered(c, s, q, sv)
    &&& cut_srv(c.n, s.writes, sv)
    &&& sound(s, c.n, sv.gvc)
    &&& entries_ok(c, s, sv)
}

pub open spec fn deps_ready(c: Constants, s: State, d: Map<int, VC>) -> bool {
    forall|k: int| #[trigger] d.dom().contains(k) ==> sound(s, c.n, d[k]) && avail(c, s, d[k])
}

pub proof fn lemma_zero_known(s: State, n: nat)
    ensures known(s, n, zero(n)), bounded(s, n, zero(n))
{
    reveal(known);
}

/// Entries either come from the lub rule or stay initial.
pub proof fn lemma_entry_grows(c: Constants, sv: Server, d: Map<int, VC>, t: Server, k: int)
    requires integrated(c.n, sv, d, t), entries_len(c.n, sv)
    ensures
        le(entry(sv, c.n, k).vc, entry(t, c.n, k).vc),
        t.ccache.dom().contains(k) ==> lub_of(c.n, entry(sv, c.n, k).vc, key_vcs(reached(sv.icache, d), k), entry(t, c.n, k).vc),
        !t.ccache.dom().contains(k) ==> entry(t, c.n, k) == entry(sv, c.n, k),
        entry(t, c.n, k).vc.len() == c.n,
{
    if !t.ccache.dom().contains(k) {
        assert(!sv.ccache.dom().contains(k));
        lemma_le_refl(zero(c.n));
    } else {
        assert(entry(t, c.n, k) == t.ccache[k]);
    }
}

pub open spec fn entries_len(n: nat, sv: Server) -> bool {
    forall|k: int| #[trigger] sv.ccache.dom().contains(k) ==> sv.ccache[k].vc.len() == n
}

pub proof fn lemma_ready_len(c: Constants, s: State, q: int)
    requires server_ready(c, s, q)
    ensures entries_len(c.n, s.servers[q])
{
    let sv = s.servers[q];
    assert forall|k: int| #[trigger] sv.ccache.dom().contains(k) implies sv.ccache[k].vc.len() == c.n by {
        assert(entry_ok(c, s, k, sv.ccache[k]));
    }
}

/// Integrated versions are stored writes below some dependency, hence available.
pub proof fn lemma_integrated_member(c: Constants, s: State, q: int, d: Map<int, VC>, m: Version)
    requires server_ready(c, s, q), deps_ready(c, s, d), reached(s.servers[q].icache, d).contains(m)
    ensures s.servers[q].icache.contains(m), s.writes.contains(m), sound(s, c.n, m.vc), avail(c, s, m.vc)
{
    let ic = s.servers[q].icache;
    assert(ic.subset_of(s.writes));
    lemma_reached_below(c, s, ic, d, m);
    let k = choose|k: int| #[trigger] d.dom().contains(k) && le(m.vc, d[k]);
    reveal(writes_ok);
    assert(sound(s, c.n, d[k]));
    lemma_avail_down(c, s, d[k], m.vc);
}

/// Each element of a write chain from d is reached through q's I-cache, or
/// is already visible and no longer pending there.
pub proof fn lemma_chain_stored_or_visible(c: Constants, s: State, q: int, d: Map<int, VC>,
                                           path: Seq<Version>, idx: int)
    requires server_ready(c, s, q), deps_ready(c, s, d), chain(s.writes, d, path), 0 <= idx < path.len()
    ensures
        reached(s.servers[q].icache, d).contains(path[idx])
            || (le(path[idx].vc, entry(s.servers[q], c.n, path[idx].key).vc)
                && !s.servers[q].icache.contains(path[idx]))
    decreases idx
{
    let sv = s.servers[q];
    let x = path[idx];
    lemma_chain_below(c, s, s.writes, d, path, idx);
    let k = choose|k: int| #[trigger] d.dom().contains(k) && le(x.vc, d[k]);
    assert(avail(c, s, d[k]));
    assert(s.writes.contains(x)) by { reveal(chain); }
    assert(s.seen[q].contains(x)) by {
        reveal(writes_ok);
        assert(x.vc[x.origin] <= d[k][x.origin]);
        reveal(avail);
    }
    if sv.icache.contains(x) {
        if idx == 0 {
            assert(matches(d, x)) by { reveal(chain); }
            lemma_singleton_chain(sv.icache, d, x);
        } else {
            lemma_chain_stored_or_visible(c, s, q, d, path, idx - 1);
            let y = path[idx - 1];
            assert(matches(y.deps, x)) by { reveal(chain); }
            if reached(sv.icache, d).contains(y) {
                lemma_reached_step(sv.icache, d, y, x);
            } else {
                assert(s.writes.contains(y)) by { reveal(chain); }
                reveal(cut_srv);
                assert(!sv.icache.contains(x));
            }
        }
    }
}

/// Replacing the last element by a same-key version below it keeps a chain.
pub proof fn lemma_reached_lower(ic: Set<Version>, d: Map<int, VC>, m: Version, v: Version)
    requires reached(ic, d).contains(m), ic.contains(v), v.key == m.key, le(v.vc, m.vc)
    ensures reached(ic, d).contains(v)
{
    let path = choose|path: Seq<Version>| #[trigger] chain(ic, d, path) && path.last() == m;
    lemma_chain_ends(ic, d, path);
    let p2 = path.update(path.len() - 1, v);
    reveal(chain);
    assert(chain(ic, d, p2)) by {
        let l = path.len() - 1;
        if l == 0 {
            lemma_le_trans(v.vc, m.vc, d[m.key]);
        }
        assert forall|t: int| 0 <= t < p2.len() implies ic.contains(#[trigger] p2[t]) by {
            if t != l { assert(p2[t] == path[t]); }
        }
        assert forall|t: int, u: int| #![trigger p2[t], p2[u]]
            0 <= t && u == t + 1 && u < p2.len() implies matches(p2[t].deps, p2[u]) by {
            assert(p2[t] == path[t]);
            if u == l {
                assert(matches(path[t].deps, path[u]));
                lemma_le_trans(v.vc, m.vc, path[t].deps[m.key]);
            } else {
                assert(p2[u] == path[u]);
            }
        }
    }
    assert(p2.last() == v);
    assert(exists|p: Seq<Version>| #[trigger] chain(ic, d, p) && p.last() == v);
}

pub proof fn lemma_integrate(c: Constants, s: State, q: int, d: Map<int, VC>, t: Server)
    requires server_ready(c, s, q), deps_ready(c, s, d), integrated(c.n, s.servers[q], d, t)
    ensures
        t.icache.subset_of(s.servers[q].icache),
        forall|k: int| #![trigger entry(t, c.n, k)] le(entry(s.servers[q], c.n, k).vc, entry(t, c.n, k).vc),
        seen_covered(c, s, q, t),
        cut_srv(c.n, s.writes, t),
        sound(s, c.n, t.gvc),
        t.gvc[q] == s.servers[q].gvc[q],
        entries_ok(c, s, t),
        forall|w: Version| #[trigger] reached(s.writes, d).contains(w) ==> le(w.vc, entry(t, c.n, w.key).vc),
{
    let sv = s.servers[q];
    let m = reached(sv.icache, d);
    lemma_ready_len(c, s, q);
    lemma_zero_known(s, c.n);
    assert forall|k: int| #![trigger entry(t, c.n, k)] le(entry(sv, c.n, k).vc, entry(t, c.n, k).vc) by {
        lemma_entry_grows(c, sv, d, t, k);
    }
    // Integrated versions are visible afterwards.
    assert forall|x: Version| #[trigger] m.contains(x) implies le(x.vc, entry(t, c.n, x.key).vc) by {
        lemma_entry_grows(c, sv, d, t, x.key);
        assert(t.ccache.dom().contains(x.key));
        assert(key_vcs(m, x.key)(x.vc));
    }
    // Seen versions stay stored or become visible.
    assert forall|v: Version| #[trigger] s.seen[q].contains(v) implies
        t.icache.contains(v) || le(v.vc, entry(t, c.n, v.key).vc) by {
        if !m.contains(v) && sv.icache.contains(v) {
            assert(t.icache.contains(v));
        } else if !m.contains(v) {
            lemma_le_trans(v.vc, entry(sv, c.n, v.key).vc, entry(t, c.n, v.key).vc);
        }
    }
    // Completeness: every write reachable from d is visible.
    assert forall|w: Version| #[trigger] reached(s.writes, d).contains(w) implies
        le(w.vc, entry(t, c.n, w.key).vc) by {
        let path = choose|path: Seq<Version>| #[trigger] chain(s.writes, d, path) && path.last() == w;
        lemma_chain_ends(s.writes, d, path);
        lemma_chain_stored_or_visible(c, s, q, d, path, path.len() - 1);
        if !m.contains(w) {
            lemma_le_trans(w.vc, entry(sv, c.n, w.key).vc, entry(t, c.n, w.key).vc);
        }
    }
    // The server clock is a sound bound that keeps q's own counter.
    assert forall|p: VC| #[trigger] dep_or_version_vcs(d, m)(p) implies sound(s, c.n, p) by {
        if !(exists|k: int| #[trigger] d.dom().contains(k) && d[k] == p) {
            let x = choose|x: Version| #[trigger] m.contains(x) && x.vc == p;
            lemma_integrated_member(c, s, q, d, x);
        }
    }
    lemma_lub_sound(s, c.n, sv.gvc, dep_or_version_vcs(d, m), t.gvc);
    assert(t.gvc[q] == sv.gvc[q]) by {
        if t.gvc[q] != sv.gvc[q] {
            let p = choose|p: VC| #[trigger] dep_or_version_vcs(d, m)(p) && p[q] == t.gvc[q];
            assert(sound(s, c.n, p));
            assert(p[q] <= ctr(s, q));
        }
    }
    // Entries: sound, available, attained, valid.
    assert forall|k: int| #[trigger] t.ccache.dom().contains(k) implies entry_ok(c, s, k, t.ccache[k]) by {
        lemma_entry_grows(c, sv, d, t, k);
        let base = entry(sv, c.n, k);
        let parts = key_vcs(m, k);
        let e = t.ccache[k];
        if sv.ccache.dom().contains(k) { assert(entry_ok(c, s, k, sv.ccache[k])); }
        else {
            reveal(avail);
            assert(avail(c, s, zero(c.n))) by {
                assert forall|v: Version, q2: int| #![trigger s.writes.contains(v), s.seen[q2].contains(v)]
                    s.writes.contains(v) && v.vc[v.origin] <= zero(c.n)[v.origin] && server(c.n, q2)
                    implies s.seen[q2].contains(v) by {
                    reveal(writes_ok);
                }
            }
        }
        assert forall|p: VC| #[trigger] parts(p) implies sound(s, c.n, p) && avail(c, s, p) by {
            let x = choose|x: Version| #[trigger] m.contains(x) && x.key == k && x.vc == p;
            lemma_integrated_member(c, s, q, d, x);
        }
        lemma_lub_sound(s, c.n, base.vc, parts, e.vc);
        lemma_lub_avail(c, s, base.vc, parts, e.vc);
        assert forall|o: int| 0 <= o < c.n && #[trigger] e.vc[o] >= 1 implies
            exists|w: Version| #[trigger] s.writes.contains(w) && w.key == k && le(w.vc, e.vc) && w.vc[o] == e.vc[o] by {
            if e.vc[o] == base.vc[o] {
                assert(sv.ccache.dom().contains(k));
                let w = choose|w: Version| #[trigger] s.writes.contains(w) && w.key == k && le(w.vc, base.vc) && w.vc[o] == base.vc[o];
                lemma_le_trans(w.vc, base.vc, e.vc);
            } else {
                let p = choose|p: VC| #[trigger] parts(p) && p[o] == e.vc[o];
                let x = choose|x: Version| #[trigger] m.contains(x) && x.key == k && x.vc == p;
                lemma_integrated_member(c, s, q, d, x);
            }
        }
        if sv.ccache.dom().contains(k) && e.value == base.value {
            let w = choose|w: Version| #[trigger] s.writes.contains(w) && w.key == k && le(w.vc, base.vc) && w.value == base.value;
            lemma_le_trans(w.vc, base.vc, e.vc);
        } else {
            let x = choose|x: Version| #[trigger] m.contains(x) && x.key == k && x.value == e.value;
            lemma_integrated_member(c, s, q, d, x);
            assert(parts(x.vc));
        }
    }
    // Causal cut. An integrated write's dependencies are reachable from d, so
    // they become visible, and any still pending are integrated with it. A
    // write that was not pending and is newly visible would lie below an
    // integrated write of its key, so it was seen, hence pending.
    reveal(cut_srv);
    assert forall|v: Version, k: int, u: Version|
        #![trigger s.writes.contains(v), v.deps.dom().contains(k), s.writes.contains(u)]
        s.writes.contains(v) && le(v.vc, entry(t, c.n, v.key).vc) && !t.icache.contains(v)
        && v.deps.dom().contains(k) && s.writes.contains(u) && u.key == k && le(u.vc, v.deps[k])
        implies le(u.vc, entry(t, c.n, k).vc) && !t.icache.contains(u) by {
        if m.contains(v) {
            lemma_reached_mono(sv.icache, d, s.writes, d);
            assert(reached(s.writes, d).contains(v));
            lemma_reached_step(s.writes, d, v, u);
            if sv.icache.contains(u) {
                lemma_reached_step(sv.icache, d, v, u);
            }
        } else {
            assert(!sv.icache.contains(v));
            if !le(v.vc, entry(sv, c.n, v.key).vc) {
                lemma_entry_grows(c, sv, d, t, v.key);
                assert(t.ccache.dom().contains(v.key));
                let base = entry(sv, c.n, v.key);
                let parts = key_vcs(m, v.key);
                if sv.ccache.dom().contains(v.key) { assert(entry_ok(c, s, v.key, sv.ccache[v.key])); }
                assert forall|p: VC| #[trigger] parts(p) implies known(s, c.n, p) && p.len() == c.n by {
                    let x = choose|x: Version| #[trigger] m.contains(x) && x.key == v.key && x.vc == p;
                    lemma_integrated_member(c, s, q, d, x);
                }
                lemma_version_below_lub(c, s, base.vc, parts, entry(t, c.n, v.key).vc, v);
                let p = choose|p: VC| #[trigger] parts(p) && le(v.vc, p);
                let x = choose|x: Version| #[trigger] m.contains(x) && x.key == v.key && x.vc == p;
                lemma_integrated_member(c, s, q, d, x);
                assert(s.seen[q].contains(v)) by {
                    reveal(writes_ok);
                    reveal(avail);
                    assert(v.vc[v.origin] <= x.vc[v.origin]);
                }
                assert(false);
            }
            assert(le(u.vc, entry(sv, c.n, k).vc) && !sv.icache.contains(u));
            lemma_le_trans(u.vc, entry(sv, c.n, k).vc, entry(t, c.n, k).vc);
        }
    }
}

} // verus!
