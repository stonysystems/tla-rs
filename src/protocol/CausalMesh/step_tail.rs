//! Preservation for a propagation message that reaches its round-two tail.
use vstd::prelude::*;
use super::vc::*;
use super::ring::*;
use super::types::*;
use super::model::*;
use super::invariants::*;
use super::lemmas::*;
use super::integration::*;
use super::channels::*;
use super::frame::*;

verus! {

/// At its round-two tail a version is seen and available, and so are its
/// dependencies.
pub proof fn lemma_tail_ready(c: Constants, s: State, src: int)
    requires inv(c, s), server(c.n, src), s.chans[src].len() > 0, is_tail(c, s, src)
    ensures ({
        let v = s.chans[src][0].version;
        &&& s.seen[succ(c.n, src)].contains(v)
        &&& deps_ready(c, s, v.deps)
        &&& s.writes.contains(v)
        &&& sound(s, c.n, v.vc) && avail(c, s, v.vc)
    }),
{
    let v = s.chans[src][0].version;
    lemma_tail_avail(c, s, src);
    assert(server(c.n, succ(c.n, src))) by { vstd::arithmetic::div_mod::lemma_mod_bound(src + 1, c.n as int); }
    assert(s.writes.contains(v)) by { reveal(seen_ok); }
    reveal(writes_ok);
    assert forall|k: int| #[trigger] v.deps.dom().contains(k) implies sound(s, c.n, v.deps[k]) && avail(c, s, v.deps[k]) by {
        assert(map_sound(s, c.n, v.deps));
        lemma_avail_down(c, s, v.vc, v.deps[k]);
    }
}

/// Merging an available version into a C-cache (Figure 6, lines 27 and 29)
/// keeps the facts that integration established.
pub proof fn lemma_merge(c: Constants, s: State, q: int, v: Version, mid: Server, t: Server)
    requires
        writes_ok(c, s), server(c.n, q), s.servers.len() == c.n, s.seen.len() == c.n,
        seen_covered(c, s, q, mid), cut_srv(c.n, s.writes, mid), sound(s, c.n, mid.gvc),
        mid.gvc[q] == s.servers[q].gvc[q], entries_ok(c, s, mid),
        s.writes.contains(v), sound(s, c.n, v.vc), avail(c, s, v.vc),
        merged(c.n, mid, v, t),
    ensures
        t.icache == mid.icache,
        forall|k: int| #![trigger entry(t, c.n, k)] le(entry(mid, c.n, k).vc, entry(t, c.n, k).vc),
        le(v.vc, entry(t, c.n, v.key).vc),
        seen_covered(c, s, q, t),
        cut_srv(c.n, s.writes, t),
        sound(s, c.n, t.gvc),
        t.gvc[q] == s.servers[q].gvc[q],
        entries_ok(c, s, t),
{
    let old = entry(mid, c.n, v.key);
    let e = t.ccache[v.key];
    let parts = one_vc(v.vc);
    lemma_zero_known(s, c.n);
    assert(parts(v.vc));
    if mid.ccache.dom().contains(v.key) { assert(entry_ok(c, s, v.key, mid.ccache[v.key])); }
    else { lemma_avail_zero_merge(c, s); }
    assert(t.ccache.dom().contains(v.key) && entry(t, c.n, v.key) == e);
    assert forall|k: int| #![trigger entry(t, c.n, k)] le(entry(mid, c.n, k).vc, entry(t, c.n, k).vc) by {
        if k == v.key {
        } else if mid.ccache.dom().contains(k) {
            assert(entry_ok(c, s, k, mid.ccache[k]));
            assert(t.ccache[k] == mid.ccache[k]);
            lemma_le_refl(mid.ccache[k].vc);
        } else {
            assert(!t.ccache.dom().contains(k));
            lemma_le_refl(zero(c.n));
        }
    }
    assert forall|w: Version| #[trigger] s.seen[q].contains(w) implies
        t.icache.contains(w) || le(w.vc, entry(t, c.n, w.key).vc) by {
        if !mid.icache.contains(w) {
            lemma_le_trans(w.vc, entry(mid, c.n, w.key).vc, entry(t, c.n, w.key).vc);
        }
    }
    // The server clock.
    lemma_lub_sound(s, c.n, mid.gvc, parts, t.gvc);
    assert(t.gvc[q] == s.servers[q].gvc[q]) by {
        assert(v.vc[q] <= ctr(s, q));
    }
    // The merged entry.
    lemma_lub_sound(s, c.n, old.vc, parts, e.vc);
    lemma_lub_avail(c, s, old.vc, parts, e.vc);
    assert(entry_ok(c, s, v.key, e)) by {
        assert forall|o: int| 0 <= o < c.n && #[trigger] e.vc[o] >= 1 implies
            exists|w: Version| #[trigger] s.writes.contains(w) && w.key == v.key && le(w.vc, e.vc) && w.vc[o] == e.vc[o] by {
            if e.vc[o] == old.vc[o] {
                assert(mid.ccache.dom().contains(v.key));
                let w = choose|w: Version| #[trigger] s.writes.contains(w) && w.key == v.key && le(w.vc, old.vc) && w.vc[o] == old.vc[o];
                lemma_le_trans(w.vc, old.vc, e.vc);
            }
        }
        if mid.ccache.dom().contains(v.key) && e.value == old.value {
            let w = choose|w: Version| #[trigger] s.writes.contains(w) && w.key == v.key && le(w.vc, old.vc) && w.value == old.value;
            lemma_le_trans(w.vc, old.vc, e.vc);
        }
    }
    assert forall|k: int| #[trigger] t.ccache.dom().contains(k) implies entry_ok(c, s, k, t.ccache[k]) by {
        if k != v.key { assert(t.ccache[k] == mid.ccache[k]); }
    }
    // Causal cut: a newly visible write lies below v, so it was seen and,
    // not being visible before, is still pending.
    reveal(cut_srv);
    assert forall|x: Version, k: int, u: Version|
        #![trigger s.writes.contains(x), x.deps.dom().contains(k), s.writes.contains(u)]
        s.writes.contains(x) && le(x.vc, entry(t, c.n, x.key).vc) && !t.icache.contains(x)
        && x.deps.dom().contains(k) && s.writes.contains(u) && u.key == k && le(u.vc, x.deps[k])
        implies le(u.vc, entry(t, c.n, k).vc) && !t.icache.contains(u) by {
        if !le(x.vc, entry(mid, c.n, x.key).vc) {
            assert(x.key == v.key);
            assert forall|p: VC| #[trigger] parts(p) implies known(s, c.n, p) && p.len() == c.n by {}
            lemma_version_below_lub(c, s, old.vc, parts, e.vc, x);
            assert(s.seen[q].contains(x)) by {
                reveal(writes_ok);
                reveal(avail);
                assert(x.vc[x.origin] <= v.vc[x.origin]);
            }
            assert(false);
        }
        lemma_le_trans(u.vc, entry(mid, c.n, k).vc, entry(t, c.n, k).vc);
    }
}

proof fn lemma_avail_zero_merge(c: Constants, s: State)
    requires writes_ok(c, s)
    ensures avail(c, s, zero(c.n))
{
    reveal(avail);
    assert forall|w: Version, q2: int| #![trigger s.writes.contains(w), s.seen[q2].contains(w)]
        s.writes.contains(w) && w.vc[w.origin] <= zero(c.n)[w.origin] && server(c.n, q2)
        implies s.seen[q2].contains(w) by {
        reveal(writes_ok);
    }
}

pub proof fn lemma_step_tail(c: Constants, s: State, s2: State, src: int, mid: Server, t: Server)
    requires inv(c, s), propagate(c, s, s2, src, mid, t), is_tail(c, s, src)
    ensures inv(c, s2)
{
    let v = s.chans[src][0].version;
    let r = succ(c.n, src);
    assert(shape_ok(c, s));
    lemma_tail_ready(c, s, src);
    assert(server(c.n, r)) by { vstd::arithmetic::div_mod::lemma_mod_bound(src + 1, c.n as int); }
    lemma_server_ready(c, s, r);
    lemma_integrate(c, s, r, v.deps, mid);
    lemma_merge(c, s, r, v, mid, t);
    assert(forall|x: Version| #[trigger] s.seen[r].contains(x) ==>
        t.icache.contains(x) || le(x.vc, entry(t, c.n, x.key).vc));
    assert(entries_ok(c, s, t));
    let sv = s.servers[r];
    assert(s2.seen =~= s.seen) by {
        assert(s.seen[r].insert(v) =~= s.seen[r]);
    }
    assert(s2.writes == s.writes && s2.sent == s.sent && s2.clients == s.clients
        && s2.ctx == s.ctx && s2.history == s.history);
    assert(s2.servers == s.servers.update(r, t));
    assert(counters_grow(c, s, s2)) by {
        assert forall|o: int| #![trigger ctr(s2, o)] server(c.n, o) implies ctr(s, o) <= ctr(s2, o) by {}
    }
    assert(forall|o: int| #![trigger ctr(s2, o)] server(c.n, o) ==> ctr(s, o) == ctr(s2, o));
    assert forall|x: VC| avail(c, s, x) implies #[trigger] avail(c, s2, x) by {
        lemma_avail_grows(c, s, s2, x);
    }
    assert(shape_ok(c, s2));
    assert(writes_ok(c, s2)) by {
        reveal(writes_ok);
        assert forall|w: Version| #[trigger] s2.writes.contains(w) implies {
            &&& server(c.n, w.origin)
            &&& sound(s2, c.n, w.vc)
            &&& w.vc[w.origin] >= 1
            &&& map_sound(s2, c.n, w.deps)
            &&& forall|k: int| #[trigger] w.deps.dom().contains(k) ==> le(w.deps[k], w.vc)
        } by {
            lemma_sound_grows(c, s, s2, w.vc);
            lemma_map_sound_grows(c, s, s2, w.deps);
        }
    }
    assert(clocks_ok(c, s2)) by {
        reveal(clocks_ok);
        assert forall|o: int| #![trigger s2.servers[o]] server(c.n, o) implies {
            &&& sound(s2, c.n, s2.servers[o].gvc)
            &&& entries_sound(s2, c.n, s2.servers[o].ccache)
        } by {
            if o == r {
                lemma_sound_grows(c, s, s2, t.gvc);
                assert forall|k: int| #[trigger] t.ccache.dom().contains(k) implies sound(s2, c.n, t.ccache[k].vc) by {
                    assert(entry_ok(c, s, k, t.ccache[k]));
                    lemma_sound_grows(c, s, s2, t.ccache[k].vc);
                }
            } else {
                assert(s2.servers[o] == s.servers[o]);
                lemma_sound_grows(c, s, s2, s.servers[o].gvc);
                lemma_entries_sound_grows(c, s, s2, s.servers[o].ccache);
            }
        }
        assert forall|cid: int| #[trigger] s2.clients.dom().contains(cid) implies {
            &&& map_sound(s2, c.n, s2.clients[cid].deps)
            &&& entries_sound(s2, c.n, s2.clients[cid].local)
        } by {
            lemma_map_sound_grows(c, s, s2, s.clients[cid].deps);
            lemma_entries_sound_grows(c, s, s2, s.clients[cid].local);
        }
        assert forall|i: int| #![trigger s2.history[i]] 0 <= i < s2.history.len() && s2.history[i] is Read implies {
            &&& sound(s2, c.n, s2.history[i]->Read_server_vc)
            &&& sound(s2, c.n, s2.history[i]->Read_vc)
        } by {
            assert(s.history[i] == s2.history[i]);
            lemma_sound_grows(c, s, s2, s.history[i]->Read_server_vc);
            lemma_sound_grows(c, s, s2, s.history[i]->Read_vc);
        }
    }
    assert(fifo_ok(c, s2)) by {
        reveal(fifo_ok);
        assert forall|q: int| #![trigger s2.chans[q]] server(c.n, q) implies {
            &&& s2.chans[q].len() <= s2.sent[q].len()
            &&& forall|i: int| #![trigger s2.chans[q][i]] 0 <= i < s2.chans[q].len()
                ==> s2.chans[q][i] == s2.sent[q][i + delivered(s2, q)]
            &&& forall|i: int| #![trigger s2.sent[q][i]] 0 <= i < delivered(s2, q)
                ==> s2.seen[succ(c.n, q)].contains(s2.sent[q][i].version)
        } by {
            if q == src {
                assert(delivered(s2, q) == delivered(s, q) + 1);
                assert forall|i: int| #![trigger s2.chans[q][i]] 0 <= i < s2.chans[q].len()
                    implies s2.chans[q][i] == s2.sent[q][i + delivered(s2, q)] by {
                    assert(s2.chans[q][i] == s.chans[q][i + 1]);
                }
                assert forall|i: int| #![trigger s2.sent[q][i]] 0 <= i < delivered(s2, q)
                    implies s2.seen[succ(c.n, q)].contains(s2.sent[q][i].version) by {
                    if i == delivered(s, q) { assert(s.chans[q][0] == s.sent[q][i]); }
                }
            } else {
                assert(s2.chans[q] == s.chans[q]);
            }
        }
    }
    assert(msg_ok(c, s2)) by { reveal(msg_ok); }
    assert(forward_ok(c, s2)) by { reveal(forward_ok); }
    assert(progress_ok(c, s2)) by {
        reveal(progress_ok);
        reveal(fifo_ok);
        assert forall|q: int, i: int| #![trigger s2.sent[q][i]]
            server(c.n, q) && 0 <= i < s2.sent[q].len() && s2.sent[q][i].hop >= 2 implies
            exists|p: int, j: int| #![trigger s2.sent[p][j]]
                server(c.n, p) && succ(c.n, p) == q && 0 <= j < delivered(s2, p)
                && s2.sent[p][j] == (Msg { version: s2.sent[q][i].version, hop: (s2.sent[q][i].hop - 1) as nat }) by {
            let (p, j) = choose|p: int, j: int| #![trigger s.sent[p][j]]
                server(c.n, p) && succ(c.n, p) == q && 0 <= j < delivered(s, p)
                && s.sent[p][j] == (Msg { version: s.sent[q][i].version, hop: (s.sent[q][i].hop - 1) as nat });
            assert(delivered(s, p) <= delivered(s2, p));
        }
    }
    assert(drag_ok(c, s2)) by { reveal(drag_ok); }
    assert(seen_ok(c, s2)) by {
        reveal(seen_ok);
        assert forall|q: int| #![trigger s2.seen[q]] server(c.n, q) implies {
            &&& s2.seen[q].subset_of(s2.writes)
            &&& s2.servers[q].icache.subset_of(s2.seen[q])
            &&& forall|w: Version| #[trigger] s2.seen[q].contains(w) ==>
                s2.servers[q].icache.contains(w) || le(w.vc, entry(s2.servers[q], c.n, w.key).vc)
            &&& forall|w: Version| #[trigger] s2.writes.contains(w) && w.origin == q ==> s2.seen[q].contains(w)
        } by {
            if q == r {
                assert(seen_covered(c, s, r, t));
            } else {
                assert(s2.servers[q] == s.servers[q]);
            }
        }
    }
    assert(avail_ok(c, s2)) by {
        reveal(avail_ok);
        assert forall|q: int, k: int| #![trigger s2.servers[q].ccache.dom().contains(k)]
            server(c.n, q) && s2.servers[q].ccache.dom().contains(k)
            implies avail(c, s2, s2.servers[q].ccache[k].vc) by {
            if q == r {
                assert(s2.servers[q] == t);
                assert(entry_ok(c, s, k, t.ccache[k]));
            } else {
                assert(s2.servers[q] == s.servers[q]);
                assert(s.servers[q].ccache.dom().contains(k));
            }
        }
    }
    assert(cut_ok(c, s2)) by {
        reveal(cut_ok);
        assert forall|q: int| #[trigger] server(c.n, q) implies cut(c, s2, q) by {
            if q != r { assert(s2.servers[q] == s.servers[q]); assert(cut(c, s, q)); }
        }
    }
    assert(client_ok(c, s2)) by { reveal(client_ok); }
    assert(cache_ok(c, s2)) by {
        reveal(cache_ok);
        assert forall|q: int, k: int| #![trigger s2.servers[q].ccache.dom().contains(k)]
            server(c.n, q) && s2.servers[q].ccache.dom().contains(k) implies {
            let e = s2.servers[q].ccache[k];
            &&& forall|o: int| 0 <= o < c.n && #[trigger] e.vc[o] >= 1 ==>
                exists|w: Version| #[trigger] s2.writes.contains(w) && w.key == k && le(w.vc, e.vc) && w.vc[o] == e.vc[o]
            &&& exists|w: Version| #[trigger] s2.writes.contains(w) && w.key == k && le(w.vc, e.vc) && w.value == e.value
        } by {
            if q == r {
                assert(s2.servers[q] == t);
                assert(entry_ok(c, s, k, t.ccache[k]));
            } else {
                assert(s2.servers[q] == s.servers[q]);
                assert(s.servers[q].ccache.dom().contains(k));
            }
        }
    }
    assert(events_ok(c, s2)) by { reveal(events_ok); }
}

} // verus!
