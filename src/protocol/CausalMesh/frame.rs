//! Frame lemmas: what survives when writes, counters and seen sets grow.
use vstd::prelude::*;
use super::vc::*;
use super::ring::*;
use super::types::*;
use super::model::*;
use super::invariants::*;
use super::integration::*;

verus! {

pub open spec fn counters_grow(c: Constants, s: State, s2: State) -> bool {
    &&& s2.servers.len() == s.servers.len()
    &&& s.writes.subset_of(s2.writes)
    &&& forall|o: int| #![trigger ctr(s2, o)] server(c.n, o) ==> ctr(s, o) <= ctr(s2, o)
}

pub proof fn lemma_sound_grows(c: Constants, s: State, s2: State, x: VC)
    requires counters_grow(c, s, s2), sound(s, c.n, x)
    ensures sound(s2, c.n, x)
{
    assert forall|o: int| 0 <= o < c.n implies #[trigger] x[o] <= ctr(s2, o) by {
        assert(x[o] <= ctr(s, o));
    }
    reveal(known);
    assert forall|o: int| 0 <= o < c.n && #[trigger] x[o] >= 1 implies
        exists|v: Version| #[trigger] s2.writes.contains(v) && v.origin == o && v.vc[o] == x[o] && le(v.vc, x) by {
        let v = choose|v: Version| #[trigger] s.writes.contains(v) && v.origin == o && v.vc[o] == x[o] && le(v.vc, x);
        assert(s2.writes.contains(v));
    }
}

pub proof fn lemma_map_sound_grows(c: Constants, s: State, s2: State, d: Map<int, VC>)
    requires counters_grow(c, s, s2), map_sound(s, c.n, d)
    ensures map_sound(s2, c.n, d)
{
    assert forall|k: int| #[trigger] d.dom().contains(k) implies sound(s2, c.n, d[k]) by {
        lemma_sound_grows(c, s, s2, d[k]);
    }
}

pub proof fn lemma_entries_sound_grows(c: Constants, s: State, s2: State, m: Map<int, Entry>)
    requires counters_grow(c, s, s2), entries_sound(s, c.n, m)
    ensures entries_sound(s2, c.n, m)
{
    assert forall|k: int| #[trigger] m.dom().contains(k) implies sound(s2, c.n, m[k].vc) by {
        lemma_sound_grows(c, s, s2, m[k].vc);
    }
}

/// Availability of a clock survives while the only new writes are ones it does
/// not count and servers only gain seen versions.
pub proof fn lemma_avail_grows(c: Constants, s: State, s2: State, x: VC)
    requires
        avail(c, s, x),
        s.seen.len() == s2.seen.len(),
        forall|q: int| #![trigger s2.seen[q]] server(c.n, q) ==> s.seen[q].subset_of(s2.seen[q]),
        forall|v: Version| #[trigger] s2.writes.contains(v) ==> s.writes.contains(v) || x[v.origin] < v.vc[v.origin],
    ensures avail(c, s2, x)
{
    reveal(avail);
    assert forall|v: Version, q: int| #![trigger s2.writes.contains(v), s2.seen[q].contains(v)]
        s2.writes.contains(v) && v.vc[v.origin] <= x[v.origin] && server(c.n, q)
        implies s2.seen[q].contains(v) by {
        assert(s.writes.contains(v));
        assert(s.seen[q].contains(v));
        assert(s.seen[q].subset_of(s2.seen[q]));
    }
}

pub proof fn lemma_server_ready(c: Constants, s: State, q: int)
    requires inv(c, s), server(c.n, q)
    ensures server_ready(c, s, q)
{
    reveal(seen_ok);
    reveal(clocks_ok);
    reveal(avail_ok);
    reveal(cut_ok);
    reveal(cache_ok);
    assert(cut(c, s, q));
    let sv = s.servers[q];
    assert(s.servers[q] == sv);
    assert forall|k: int| #[trigger] sv.ccache.dom().contains(k) implies entry_ok(c, s, k, sv.ccache[k]) by {
        assert(entries_sound(s, c.n, sv.ccache));
        assert(s.servers[q].ccache.dom().contains(k));
    }
}

pub proof fn lemma_deps_ready(c: Constants, s: State, cid: int)
    requires inv(c, s), s.clients.dom().contains(cid)
    ensures deps_ready(c, s, s.clients[cid].deps)
{
    reveal(clocks_ok);
    reveal(avail_ok);
    let d = s.clients[cid].deps;
    assert forall|k: int| #[trigger] d.dom().contains(k) implies sound(s, c.n, d[k]) && avail(c, s, d[k]) by {
        assert(map_sound(s, c.n, d));
        assert(s.clients[cid].deps.dom().contains(k));
    }
}

} // verus!
