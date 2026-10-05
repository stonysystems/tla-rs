//! Preservation for a client write (Figure 6, ClientWrite).
use vstd::prelude::*;
use super::vc::*;
use super::ring::*;
use super::types::*;
use super::model::*;
use super::invariants::*;
use super::lemmas::*;
use super::integration::*;
use super::frame::*;

verus! {

pub proof fn lemma_version_positive(c: Constants, s: State, w: Version, x: VC)
    requires writes_ok(c, s), s.writes.contains(w), le(w.vc, x)
    ensures x[w.origin] >= 1, x != zero(c.n)
{
    reveal(writes_ok);
    assert(w.vc[w.origin] >= 1);
    assert(server(c.n, w.origin));
    if x == zero(c.n) { assert(x[w.origin] == 0); }
}

/// Clocks sound in s never count the new write.
pub proof fn lemma_new_not_below(c: Constants, s: State, srv: int, v: Version, x: VC)
    requires sound(s, c.n, x), server(c.n, srv), v.vc[srv] == ctr(s, srv) + 1
    ensures !le(v.vc, x), x[srv] < v.vc[srv]
{
    assert(x[srv] <= ctr(s, srv));
}

pub proof fn lemma_write_deps_sound(c: Constants, s: State, cid: int)
    requires inv(c, s), s.clients.dom().contains(cid)
    ensures
        map_sound(s, c.n, write_deps(c.n, s.clients[cid])),
        map_le(s.clients[cid].deps, write_deps(c.n, s.clients[cid])),
        forall|k: int| #[trigger] s.clients[cid].local.dom().contains(k) ==>
            write_deps(c.n, s.clients[cid]).dom().contains(k)
            && le(s.clients[cid].local[k].vc, write_deps(c.n, s.clients[cid])[k]),
{
    let cl = s.clients[cid];
    let d = write_deps(c.n, cl);
    reveal(clocks_ok);
    assert(map_sound(s, c.n, cl.deps) && entries_sound(s, c.n, cl.local));
    lemma_zero_known(s, c.n);
    assert forall|k: int| #[trigger] d.dom().contains(k) implies sound(s, c.n, d[k]) by {
        let a = dep(cl.deps, c.n, k);
        let b = local_entry(cl, c.n, k).vc;
        if cl.deps.dom().contains(k) { assert(sound(s, c.n, cl.deps[k])); }
        if cl.local.dom().contains(k) { assert(sound(s, c.n, cl.local[k].vc)); }
        lemma_join_lub_of(c.n, a, b);
        lemma_lub_sound(s, c.n, a, |x: VC| x == b, join(a, b));
    }
    assert forall|k: int| #[trigger] cl.deps.dom().contains(k) implies d.dom().contains(k) && le(cl.deps[k], d[k]) by {
        assert(sound(s, c.n, cl.deps[k]));
        if cl.local.dom().contains(k) { assert(sound(s, c.n, cl.local[k].vc)); }
        lemma_join_lub(cl.deps[k], local_entry(cl, c.n, k).vc);
    }
    assert forall|k: int| #[trigger] cl.local.dom().contains(k) implies d.dom().contains(k) && le(cl.local[k].vc, d[k]) by {
        assert(sound(s, c.n, cl.local[k].vc));
        if cl.deps.dom().contains(k) { assert(sound(s, c.n, cl.deps[k])); }
        lemma_join_lub(dep(cl.deps, c.n, k), cl.local[k].vc);
    }
}

/// The new version: a fresh counter at its origin, a sound clock that
/// dominates its deps and every earlier write from the same origin.
pub proof fn lemma_new_version(c: Constants, s: State, cid: int, srv: int, key: int, value: int, gvc: VC)
    requires inv(c, s), s.clients.dom().contains(cid), server(c.n, srv),
        lub_of(c.n, s.servers[srv].gvc, dep_vcs(write_deps(c.n, s.clients[cid])), gvc),
    ensures ({
        let v = new_version(c, s, cid, srv, key, value, gvc);
        &&& v.vc.len() == c.n
        &&& v.vc[srv] == ctr(s, srv) + 1
        &&& forall|o: int| 0 <= o < c.n && o != srv ==> #[trigger] v.vc[o] <= ctr(s, o)
        &&& !s.writes.contains(v)
        &&& forall|k: int| #[trigger] v.deps.dom().contains(k) ==> le(v.deps[k], v.vc)
        &&& map_sound(s, c.n, v.deps)
        &&& le(s.servers[srv].gvc, v.vc)
        &&& forall|w: Version| #[trigger] s.writes.contains(w) && w.origin == srv ==> le(w.vc, v.vc)
        &&& forall|o: int| 0 <= o < c.n && o != srv && #[trigger] v.vc[o] >= 1 ==>
            exists|w: Version| #[trigger] s.writes.contains(w) && w.origin == o && w.vc[o] == v.vc[o] && le(w.vc, v.vc)
    }),
{
    let v = new_version(c, s, cid, srv, key, value, gvc);
    let d = write_deps(c.n, s.clients[cid]);
    lemma_write_deps_sound(c, s, cid);
    reveal(clocks_ok);
    assert(sound(s, c.n, s.servers[srv].gvc));
    assert forall|p: VC| #[trigger] dep_vcs(d)(p) implies sound(s, c.n, p) by {
        let k = choose|k: int| #[trigger] d.dom().contains(k) && d[k] == p;
    }
    lemma_lub_sound(s, c.n, s.servers[srv].gvc, dep_vcs(d), gvc);
    assert(gvc[srv] == ctr(s, srv)) by {
        if gvc[srv] != s.servers[srv].gvc[srv] {
            let p = choose|p: VC| #[trigger] dep_vcs(d)(p) && p[srv] == gvc[srv];
            assert(sound(s, c.n, p));
        }
    }
    lemma_tick(gvc, srv);
    assert forall|k: int| #[trigger] v.deps.dom().contains(k) implies le(v.deps[k], v.vc) by {
        assert(dep_vcs(d)(d[k]));
        lemma_le_trans(d[k], gvc, v.vc);
    }
    lemma_le_trans(s.servers[srv].gvc, gvc, v.vc);
    assert(!s.writes.contains(v)) by {
        if s.writes.contains(v) {
            reveal(writes_ok);
            assert(v.vc[srv] <= ctr(s, srv));
        }
    }
    reveal(known);
    assert forall|w: Version| #[trigger] s.writes.contains(w) && w.origin == srv implies le(w.vc, v.vc) by {
        reveal(writes_ok);
        assert(w.vc[srv] <= ctr(s, srv));
        assert(w.vc[srv] >= 1);
        let z = choose|z: Version| #[trigger] s.writes.contains(z) && z.origin == srv
            && z.vc[srv] == s.servers[srv].gvc[srv] && le(z.vc, s.servers[srv].gvc);
        assert(le(w.vc, z.vc));
        lemma_le_trans(w.vc, z.vc, s.servers[srv].gvc);
        lemma_le_trans(w.vc, s.servers[srv].gvc, v.vc);
    }
    assert forall|o: int| 0 <= o < c.n && o != srv && #[trigger] v.vc[o] >= 1 implies
        exists|w: Version| #[trigger] s.writes.contains(w) && w.origin == o && w.vc[o] == v.vc[o] && le(w.vc, v.vc) by {
        assert(v.vc[o] == gvc[o]);
        let w = choose|w: Version| #[trigger] s.writes.contains(w) && w.origin == o && w.vc[o] == gvc[o] && le(w.vc, gvc);
        lemma_le_trans(w.vc, gvc, v.vc);
    }
}

/// Adding a write that no existing clock counts preserves a causal cut, and
/// the new write is not visible.
pub proof fn lemma_cut_add(c: Constants, s: State, sv: Server, v: Version, srv: int)
    requires cut_srv(c.n, s.writes, sv), writes_ok(c, s), server(c.n, srv), v.vc[srv] == ctr(s, srv) + 1,
        forall|k: int| #[trigger] sv.ccache.dom().contains(k) ==> sound(s, c.n, sv.ccache[k].vc),
    ensures cut_srv(c.n, s.writes.insert(v), sv), !le(v.vc, entry(sv, c.n, v.key).vc)
{
    let w2 = s.writes.insert(v);
    lemma_zero_known(s, c.n);
    if sv.ccache.dom().contains(v.key) { assert(sound(s, c.n, sv.ccache[v.key].vc)); }
    lemma_new_not_below(c, s, srv, v, entry(sv, c.n, v.key).vc);
    reveal(cut_srv);
    assert forall|x: Version, k: int, u: Version|
        #![trigger w2.contains(x), x.deps.dom().contains(k), w2.contains(u)]
        w2.contains(x) && le(x.vc, entry(sv, c.n, x.key).vc) && !sv.icache.contains(x)
        && x.deps.dom().contains(k) && w2.contains(u) && u.key == k && le(u.vc, x.deps[k])
        implies le(u.vc, entry(sv, c.n, k).vc) && !sv.icache.contains(u) by {
        if sv.ccache.dom().contains(x.key) { assert(sound(s, c.n, sv.ccache[x.key].vc)); }
        if x == v {
            lemma_new_not_below(c, s, srv, v, entry(sv, c.n, x.key).vc);
        } else {
            reveal(writes_ok);
            assert(map_sound(s, c.n, x.deps));
            assert(sound(s, c.n, x.deps[k]));
            if u == v { lemma_new_not_below(c, s, srv, v, x.deps[k]); }
        }
    }
}

pub proof fn lemma_step_write(c: Constants, s: State, s2: State, cid: int, srv: int, key: int, value: int, gvc: VC)
    requires inv(c, s), client_write(c, s, s2, cid, srv, key, value, gvc)
    ensures inv(c, s2)
{
    assert(shape_ok(c, s));
    let cl = s.clients[cid];
    let sv = s.servers[srv];
    let v = new_version(c, s, cid, srv, key, value, gvc);
    let d = write_deps(c.n, cl);
    let out = Msg { version: v, hop: 1 };
    let ctx2 = s.ctx[cid].insert(v);
    let L = s.sent[srv].len() as int;
    lemma_new_version(c, s, cid, srv, key, value, gvc);
    lemma_write_deps_sound(c, s, cid);
    lemma_tick(gvc, srv);
    assert(s2.writes == s.writes.insert(v));
    assert(s2.servers == s.servers.update(srv, Server { gvc: v.vc, icache: sv.icache.insert(v), ..sv }));
    assert(s2.sent == s.sent.update(srv, s.sent[srv].push(out)));
    assert(s2.chans == s.chans.update(srv, s.chans[srv].push(out)));
    assert(s2.seen == s.seen.update(srv, s.seen[srv].insert(v)));
    assert(s2.clients == s.clients.insert(cid, Client { local: cl.local.insert(key, Entry { value, vc: v.vc }), ..cl }));
    assert(s2.ctx == s.ctx.insert(cid, ctx2));
    assert(s2.history == s.history.push(Event::Write { client: cid, version: v, ctx: ctx2 }));
    assert(ctr(s2, srv) == ctr(s, srv) + 1);
    assert(forall|o: int| #![trigger ctr(s2, o)] server(c.n, o) && o != srv ==> ctr(s2, o) == ctr(s, o));
    assert(counters_grow(c, s, s2)) by {
        assert forall|o: int| #![trigger ctr(s2, o)] server(c.n, o) implies ctr(s, o) <= ctr(s2, o) by {}
    }
    assert forall|x: VC| sound(s, c.n, x) && avail(c, s, x) implies #[trigger] avail(c, s2, x) by {
        assert forall|w: Version| #[trigger] s2.writes.contains(w) implies s.writes.contains(w) || x[w.origin] < w.vc[w.origin] by {
            if w == v { lemma_new_not_below(c, s, srv, v, x); }
        }
        lemma_avail_grows(c, s, s2, x);
    }
    // The new clock is sound after the write.
    assert(sound(s2, c.n, v.vc)) by {
        assert forall|o: int| 0 <= o < c.n implies #[trigger] v.vc[o] <= ctr(s2, o) by {}
        reveal(known);
        assert forall|o: int| 0 <= o < c.n && #[trigger] v.vc[o] >= 1 implies
            exists|w: Version| #[trigger] s2.writes.contains(w) && w.origin == o && w.vc[o] == v.vc[o] && le(w.vc, v.vc) by {
            if o == srv {
                lemma_le_refl(v.vc);
                assert(s2.writes.contains(v));
            } else {
                let w = choose|w: Version| #[trigger] s.writes.contains(w) && w.origin == o && w.vc[o] == v.vc[o] && le(w.vc, v.vc);
                assert(s2.writes.contains(w));
            }
        }
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
            if w == v {
                lemma_map_sound_grows(c, s, s2, v.deps);
            } else {
                lemma_sound_grows(c, s, s2, w.vc);
                lemma_map_sound_grows(c, s, s2, w.deps);
            }
        }
        assert forall|x: Version, w: Version| #![trigger s2.writes.contains(x), s2.writes.contains(w)]
            s2.writes.contains(x) && s2.writes.contains(w) && x.origin == w.origin
            && x.vc[x.origin] <= w.vc[w.origin] implies le(x.vc, w.vc) by {
            if x == v && w != v {
                assert(w.vc[srv] <= ctr(s, srv));
            } else if x != v && w == v {
                assert(s.writes.contains(x) && x.origin == srv);
            } else if x == v && w == v {
                lemma_le_refl(v.vc);
            }
        }
        assert forall|x: Version, w: Version| #![trigger s2.writes.contains(x), s2.writes.contains(w)]
            s2.writes.contains(x) && s2.writes.contains(w) && x.origin == w.origin
            && x.vc[x.origin] == w.vc[w.origin] implies x == w by {
            if x == v && w != v { assert(w.vc[srv] <= ctr(s, srv)); }
            if x != v && w == v { assert(x.vc[srv] <= ctr(s, srv)); }
        }
    }
    assert(clocks_ok(c, s2)) by {
        reveal(clocks_ok);
        assert forall|o: int| #![trigger s2.servers[o]] server(c.n, o) implies {
            &&& sound(s2, c.n, s2.servers[o].gvc)
            &&& entries_sound(s2, c.n, s2.servers[o].ccache)
        } by {
            lemma_entries_sound_grows(c, s, s2, s.servers[o].ccache);
            if o != srv { lemma_sound_grows(c, s, s2, s.servers[o].gvc); }
        }
        assert forall|id: int| #[trigger] s2.clients.dom().contains(id) implies {
            &&& map_sound(s2, c.n, s2.clients[id].deps)
            &&& entries_sound(s2, c.n, s2.clients[id].local)
        } by {
            lemma_map_sound_grows(c, s, s2, s.clients[id].deps);
            lemma_entries_sound_grows(c, s, s2, s.clients[id].local);
            if id == cid {
                let l2 = cl.local.insert(key, Entry { value, vc: v.vc });
                assert forall|k: int| #[trigger] l2.dom().contains(k) implies sound(s2, c.n, l2[k].vc) by {
                    if k != key { assert(cl.local.dom().contains(k)); }
                }
            }
        }
        assert forall|i: int| #![trigger s2.history[i]] 0 <= i < s2.history.len() && s2.history[i] is Read implies {
            &&& sound(s2, c.n, s2.history[i]->Read_server_vc)
            &&& sound(s2, c.n, s2.history[i]->Read_vc)
        } by {
            assert(i < s.history.len());
            assert(s2.history[i] == s.history[i]);
            lemma_sound_grows(c, s, s2, s.history[i]->Read_server_vc);
            lemma_sound_grows(c, s, s2, s.history[i]->Read_vc);
        }
    }
    assert(forall|q: int, i: int| #![trigger s2.sent[q][i]] server(c.n, q) && 0 <= i < s.sent[q].len()
        ==> s2.sent[q][i] == s.sent[q][i]);
    assert(s2.sent[srv][L] == out);
    assert(fifo_ok(c, s2)) by {
        reveal(fifo_ok);
        assert forall|q: int| #![trigger s2.chans[q]] server(c.n, q) implies {
            &&& s2.chans[q].len() <= s2.sent[q].len()
            &&& forall|i: int| #![trigger s2.chans[q][i]] 0 <= i < s2.chans[q].len()
                ==> s2.chans[q][i] == s2.sent[q][i + delivered(s2, q)]
            &&& forall|i: int| #![trigger s2.sent[q][i]] 0 <= i < delivered(s2, q)
                ==> s2.seen[succ(c.n, q)].contains(s2.sent[q][i].version)
        } by {
            assert(s.chans[q].len() <= s.sent[q].len());
            assert(delivered(s2, q) == delivered(s, q));
            assert forall|i: int| #![trigger s2.chans[q][i]] 0 <= i < s2.chans[q].len()
                implies s2.chans[q][i] == s2.sent[q][i + delivered(s2, q)] by {
                if q != srv || i < s.chans[q].len() { assert(s2.chans[q][i] == s.chans[q][i]); }
            }
            assert forall|i: int| #![trigger s2.sent[q][i]] 0 <= i < delivered(s2, q)
                implies s2.seen[succ(c.n, q)].contains(s2.sent[q][i].version) by {
                assert(s.seen[succ(c.n, q)].contains(s.sent[q][i].version));
            }
        }
    }
    assert(msg_ok(c, s2)) by {
        reveal(msg_ok);
        lemma_at_zero(c.n, srv);
        assert(tail_hop(c) >= 1) by {
            assert(c.rounds * c.n >= 2) by (nonlinear_arith) requires c.rounds >= 2, c.n >= 1;
        }
    }
    assert(forward_ok(c, s2)) by {
        reveal(forward_ok);
        assert forall|w: Version| #[trigger] s2.writes.contains(w) implies
            exists|i: int| 0 <= i < s2.sent[w.origin].len() && #[trigger] s2.sent[w.origin][i] == (Msg { version: w, hop: 1 }) by {
            if w == v {
                assert(s2.sent[w.origin][L] == out);
            } else {
                let i = choose|i: int| 0 <= i < s.sent[w.origin].len() && #[trigger] s.sent[w.origin][i] == (Msg { version: w, hop: 1 });
                reveal(writes_ok);
                assert(s2.sent[w.origin][i] == s.sent[w.origin][i]);
            }
        }
        assert forall|q: int, w: Version| #![trigger s2.seen[q].contains(w)] server(c.n, q) && s2.seen[q].contains(w) implies
            exists|i: int| 0 <= i < s2.sent[q].len() && #[trigger] s2.sent[q][i].version == w by {
            if q == srv && w == v {
                assert(s2.sent[q][L].version == w);
            } else {
                assert(s.seen[q].contains(w));
                let i = choose|i: int| 0 <= i < s.sent[q].len() && #[trigger] s.sent[q][i].version == w;
                assert(s2.sent[q][i] == s.sent[q][i]);
            }
        }
    }
    assert(progress_ok(c, s2)) by {
        reveal(progress_ok);
        reveal(fifo_ok);
        assert forall|q: int, i: int| #![trigger s2.sent[q][i]]
            server(c.n, q) && 0 <= i < s2.sent[q].len() && s2.sent[q][i].hop >= 2 implies
            exists|p: int, j: int| #![trigger s2.sent[p][j]]
                server(c.n, p) && succ(c.n, p) == q && 0 <= j < delivered(s2, p)
                && s2.sent[p][j] == (Msg { version: s2.sent[q][i].version, hop: (s2.sent[q][i].hop - 1) as nat }) by {
            assert(i < s.sent[q].len());
            assert(s2.sent[q][i] == s.sent[q][i]);
            let (p, j) = choose|p: int, j: int| #![trigger s.sent[p][j]]
                server(c.n, p) && succ(c.n, p) == q && 0 <= j < delivered(s, p)
                && s.sent[p][j] == (Msg { version: s.sent[q][i].version, hop: (s.sent[q][i].hop - 1) as nat });
            assert(s.chans[p].len() <= s.sent[p].len());
            assert(s2.sent[p][j] == s.sent[p][j]);
            assert(delivered(s2, p) == delivered(s, p));
        }
    }
    assert(drag_ok(c, s2)) by {
        reveal(drag_ok);
        assert forall|q: int, i: int, w: Version, j: nat|
            #![trigger s2.sent[q][i], s2.writes.contains(w), at(c.n, s2.sent[q][i].version.origin, j)]
            server(c.n, q) && 0 <= i < s2.sent[q].len() && s2.writes.contains(w)
            && j < s2.sent[q][i].hop && s2.sent[q][i].hop < j + c.n
            && at(c.n, s2.sent[q][i].version.origin, j) == w.origin
            && w != s2.sent[q][i].version && w.vc[w.origin] <= s2.sent[q][i].version.vc[w.origin]
            implies exists|i2: int| 0 <= i2 < i && #[trigger] s2.sent[q][i2].version == w by {
            if q == srv && i == L {
                assert(s2.sent[q][i] == out);
                assert(j == 0);
                lemma_at_zero(c.n, srv);
                assert(w.origin == srv && s.writes.contains(w));
                reveal(forward_ok);
                assert(exists|i1: int| 0 <= i1 < s.sent[w.origin].len() && #[trigger] s.sent[w.origin][i1] == (Msg { version: w, hop: 1 }));
                let i1 = choose|i1: int| 0 <= i1 < s.sent[w.origin].len() && #[trigger] s.sent[w.origin][i1] == (Msg { version: w, hop: 1 });
                assert(s2.sent[q][i1] == s.sent[q][i1]);
                assert(s2.sent[q][i1].version == w);
            } else {
                assert(i < s.sent[q].len());
                assert(s2.sent[q][i] == s.sent[q][i]);
                let mv = s.sent[q][i].version;
                assert(s.writes.contains(mv)) by { reveal(msg_ok); }
                if w == v {
                    reveal(writes_ok);
                    assert(sound(s, c.n, mv.vc));
                    assert(mv.vc[srv] <= ctr(s, srv));
                } else {
                    assert(s.writes.contains(w));
                    assert(at(c.n, s.sent[q][i].version.origin, j) == w.origin);
                    assert(exists|i2: int| 0 <= i2 < i && #[trigger] s.sent[q][i2].version == w);
                    let i2 = choose|i2: int| 0 <= i2 < i && #[trigger] s.sent[q][i2].version == w;
                    assert(s2.sent[q][i2] == s.sent[q][i2]);
                    assert(s2.sent[q][i2].version == w);
                }
            }
        }
    }
    assert(seen_ok(c, s2)) by {
        reveal(seen_ok);
        assert forall|q: int| #![trigger s2.seen[q]] server(c.n, q) implies {
            &&& s2.seen[q].subset_of(s2.writes)
            &&& s2.servers[q].icache.subset_of(s2.seen[q])
            &&& forall|w: Version| #[trigger] s2.seen[q].contains(w) ==>
                s2.servers[q].icache.contains(w) || le(w.vc, entry(s2.servers[q], c.n, w.key).vc)
            &&& forall|w: Version| #[trigger] s2.writes.contains(w) && w.origin == q ==> s2.seen[q].contains(w)
        } by {
            assert(entry(s2.servers[q], c.n, key) == entry(s.servers[q], c.n, key));
            assert forall|w: Version| #[trigger] s2.seen[q].contains(w) implies
                s2.servers[q].icache.contains(w) || le(w.vc, entry(s2.servers[q], c.n, w.key).vc) by {
                if !(q == srv && w == v) {
                    assert(s.seen[q].contains(w));
                    assert(entry(s2.servers[q], c.n, w.key) == entry(s.servers[q], c.n, w.key));
                }
            }
        }
    }
    assert(avail_ok(c, s2)) by {
        reveal(avail_ok);
        reveal(clocks_ok);
        assert forall|q: int, k: int| #![trigger s2.servers[q].ccache.dom().contains(k)]
            server(c.n, q) && s2.servers[q].ccache.dom().contains(k)
            implies avail(c, s2, s2.servers[q].ccache[k].vc) by {
            assert(s.servers[q].ccache.dom().contains(k));
            assert(entries_sound(s, c.n, s.servers[q].ccache));
        }
        assert forall|id: int, k: int| #![trigger s2.clients[id].deps.dom().contains(k)]
            s2.clients.dom().contains(id) && s2.clients[id].deps.dom().contains(k)
            implies avail(c, s2, s2.clients[id].deps[k]) by {
            assert(s.clients[id].deps.dom().contains(k));
            assert(map_sound(s, c.n, s.clients[id].deps));
        }
    }
    assert(cut_ok(c, s2)) by {
        reveal(cut_ok);
        reveal(clocks_ok);
        assert forall|q: int| #[trigger] server(c.n, q) implies cut(c, s2, q) by {
            assert(cut(c, s, q));
            assert(entries_sound(s, c.n, s.servers[q].ccache));
            lemma_cut_add(c, s, s.servers[q], v, srv);
            reveal(cut_srv);
            assert forall|k: int| #![trigger entry(s2.servers[q], c.n, k)]
                entry(s2.servers[q], c.n, k) == entry(s.servers[q], c.n, k) by {}
        }
    }
    assert(client_ok(c, s2)) by {
        reveal(client_ok);
        lemma_reached_mono(s.writes, cl.deps, s2.writes, cl.deps);
        assert forall|id: int| #[trigger] s2.clients.dom().contains(id) implies {
            let c2 = s2.clients[id];
            &&& s2.ctx[id].subset_of(s2.writes)
            &&& forall|w: Version| #[trigger] s2.ctx[id].contains(w) ==>
                le(w.vc, local_entry(c2, c.n, w.key).vc) || reached(s2.writes, c2.deps).contains(w)
            &&& forall|k: int| #[trigger] c2.local.dom().contains(k) ==>
                exists|w: Version| #[trigger] s2.ctx[id].contains(w) && w.key == k
                    && w.vc == c2.local[k].vc && w.value == c2.local[k].value
        } by {
            if id == cid {
                let c2 = s2.clients[id];
                assert forall|w: Version| #[trigger] s2.ctx[id].contains(w) implies
                    le(w.vc, local_entry(c2, c.n, w.key).vc) || reached(s2.writes, c2.deps).contains(w) by {
                    if w == v {
                        lemma_le_refl(v.vc);
                    } else if le(w.vc, local_entry(cl, c.n, w.key).vc) {
                        if w.key == key {
                            reveal(writes_ok);
                            if !cl.local.dom().contains(key) { lemma_version_positive(c, s, w, zero(c.n)); }
                            lemma_le_trans(cl.local[key].vc, d[key], v.vc);
                            lemma_le_trans(w.vc, cl.local[key].vc, v.vc);
                        }
                    }
                }
                assert forall|k: int| #[trigger] c2.local.dom().contains(k) implies
                    exists|w: Version| #[trigger] s2.ctx[id].contains(w) && w.key == k
                        && w.vc == c2.local[k].vc && w.value == c2.local[k].value by {
                    if k == key {
                        assert(s2.ctx[id].contains(v));
                    } else {
                        let w = choose|w: Version| #[trigger] s.ctx[id].contains(w) && w.key == k
                            && w.vc == cl.local[k].vc && w.value == cl.local[k].value;
                        assert(s2.ctx[id].contains(w));
                    }
                }
            } else {
                lemma_reached_mono(s.writes, s.clients[id].deps, s2.writes, s.clients[id].deps);
            }
        }
    }
    assert(cache_ok(c, s2)) by {
        reveal(cache_ok);
        assert forall|q: int, k: int| #![trigger s2.servers[q].ccache.dom().contains(k)]
            server(c.n, q) && s2.servers[q].ccache.dom().contains(k) implies {
            let e = s2.servers[q].ccache[k];
            &&& forall|o: int| 0 <= o < c.n && #[trigger] e.vc[o] >= 1 ==>
                exists|w: Version| #[trigger] s2.writes.contains(w) && w.key == k && le(w.vc, e.vc) && w.vc[o] == e.vc[o]
            &&& exists|w: Version| #[trigger] s2.writes.contains(w) && w.key == k && le(w.vc, e.vc) && w.value == e.value
        } by {
            assert(s.servers[q].ccache.dom().contains(k));
            let e = s.servers[q].ccache[k];
            assert forall|o: int| 0 <= o < c.n && #[trigger] e.vc[o] >= 1 implies
                exists|w: Version| #[trigger] s2.writes.contains(w) && w.key == k && le(w.vc, e.vc) && w.vc[o] == e.vc[o] by {
                let w = choose|w: Version| #[trigger] s.writes.contains(w) && w.key == k && le(w.vc, e.vc) && w.vc[o] == e.vc[o];
                assert(s2.writes.contains(w));
            }
            let w = choose|w: Version| #[trigger] s.writes.contains(w) && w.key == k && le(w.vc, e.vc) && w.value == e.value;
            assert(s2.writes.contains(w));
        }
    }
    assert(events_ok(c, s2)) by {
        lemma_step_write_events(c, s, s2, cid, srv, key, value, gvc);
    }
}

pub proof fn lemma_step_write_events(c: Constants, s: State, s2: State, cid: int, srv: int, key: int, value: int, gvc: VC)
    requires inv(c, s), client_write(c, s, s2, cid, srv, key, value, gvc)
    ensures events_ok(c, s2)
{
    let cl = s.clients[cid];
    let v = new_version(c, s, cid, srv, key, value, gvc);
    let d = write_deps(c.n, cl);
    let ctx2 = s.ctx[cid].insert(v);
    let h = s.history;
    let h2 = s2.history;
    let j = h.len() as int;
    lemma_new_version(c, s, cid, srv, key, value, gvc);
    lemma_write_deps_sound(c, s, cid);
    assert(h2 == h.push(Event::Write { client: cid, version: v, ctx: ctx2 }));
    assert(s2.writes == s.writes.insert(v));
    assert(s2.ctx == s.ctx.insert(cid, ctx2));
    assert(s2.clients.dom() == s.clients.dom());
    reveal(events_ok);
    reveal(client_ok);
    assert(s.ctx[cid].subset_of(s.writes));
    assert forall|i: int| #![trigger h2[i]] 0 <= i < h2.len() implies event_ok(c, s2, i) by {
        if i == j {
            assert forall|w: Version| #[trigger] ev_ctx(h2[i]).contains(w) implies
                w == v || reached(s2.writes, v.deps).contains(w) by {
                if w != v {
                    assert(s.ctx[cid].contains(w));
                    if le(w.vc, local_entry(cl, c.n, w.key).vc) {
                        if !cl.local.dom().contains(w.key) { lemma_version_positive(c, s, w, zero(c.n)); }
                        lemma_le_trans(w.vc, cl.local[w.key].vc, d[w.key]);
                        assert(s2.writes.contains(w));
                        lemma_singleton_chain(s2.writes, d, w);
                    } else {
                        lemma_reached_mono(s.writes, cl.deps, s2.writes, d);
                    }
                }
            }
        } else {
            assert(h2[i] == h[i]);
            if h[i] is Write {
                let w0 = h[i]->Write_version;
                lemma_reached_mono(s.writes, w0.deps, s2.writes, w0.deps);
            }
        }
    }
    assert forall|w: Version| #[trigger] s2.writes.contains(w) implies exists|i: int|
        0 <= i < h2.len() && #[trigger] h2[i] is Write && h2[i]->Write_version == w by {
        if w == v {
            assert(h2[j] is Write && h2[j]->Write_version == w);
        } else {
            let i = choose|i: int| 0 <= i < h.len() && #[trigger] h[i] is Write && h[i]->Write_version == w;
            assert(h2[i] == h[i]);
        }
    }
    assert forall|i: int, k: int| #![trigger super::properties::edge(h2, i, k)]
        super::properties::edge(h2, i, k) implies ev_ctx(h2[i]).subset_of(ev_ctx(h2[k])) by {
        if k == j {
            assert(h2[i] == h[i]);
            assert(!super::properties::observes(h2, i, k));
        } else {
            assert(h2[i] == h[i] && h2[k] == h[k]);
            assert(super::properties::edge(h, i, k));
            lemma_edge_ctx(c, s, i, k);
        }
    }
}

} // verus!
