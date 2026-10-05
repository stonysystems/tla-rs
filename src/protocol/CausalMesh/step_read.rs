//! Preservation for a client read (Figure 6, ClientRead, and Figure 4).
use vstd::prelude::*;
use super::vc::*;
use super::ring::*;
use super::types::*;
use super::model::*;
use super::invariants::*;
use super::lemmas::*;
use super::integration::*;
use super::frame::*;
use super::step_write::*;

verus! {

pub proof fn lemma_avail_zero(c: Constants, s: State)
    requires writes_ok(c, s)
    ensures avail(c, s, zero(c.n))
{
    reveal(avail);
    assert forall|v: Version, q: int| #![trigger s.writes.contains(v), s.seen[q].contains(v)]
        s.writes.contains(v) && v.vc[v.origin] <= zero(c.n)[v.origin] && server(c.n, q)
        implies s.seen[q].contains(v) by {
        reveal(writes_ok);
    }
}

/// Facts about the read's server reply `e`.
pub proof fn lemma_reply(c: Constants, s: State, srv: int, cid: int, t: Server, key: int)
    requires inv(c, s), server(c.n, srv), s.clients.dom().contains(cid),
        integrated(c.n, s.servers[srv], s.clients[cid].deps, t),
    ensures ({
        let e = entry(t, c.n, key);
        &&& sound(s, c.n, e.vc) && avail(c, s, e.vc)
        &&& (t.ccache.dom().contains(key) && entry_ok(c, s, key, e))
            || (!t.ccache.dom().contains(key) && e == initial_entry(c.n))
    }),
{
    lemma_server_ready(c, s, srv);
    lemma_deps_ready(c, s, cid);
    lemma_integrate(c, s, srv, s.clients[cid].deps, t);
    lemma_zero_known(s, c.n);
    reveal(writes_ok);
    lemma_avail_zero(c, s);
    if t.ccache.dom().contains(key) {
        assert(entry_ok(c, s, key, t.ccache[key]));
    }
}

pub proof fn lemma_step_read(c: Constants, s: State, s2: State, cid: int, srv: int, key: int, t: Server, r: Entry)
    requires inv(c, s), client_read(c, s, s2, cid, srv, key, t, r)
    ensures inv(c, s2)
{
    assert(shape_ok(c, s));
    let cl = s.clients[cid];
    let e = entry(t, c.n, key);
    let obs = observed(s, key, e.vc);
    let ctx2 = s.ctx[cid].union(obs);
    let deps2 = cl.deps.insert(key, join(dep(cl.deps, c.n, key), e.vc));
    lemma_server_ready(c, s, srv);
    lemma_deps_ready(c, s, cid);
    lemma_integrate(c, s, srv, cl.deps, t);
    lemma_reply(c, s, srv, cid, t, key);
    assert(s2.servers == s.servers.update(srv, t));
    assert(s2.clients == s.clients.insert(cid, Client { deps: deps2, ..cl }));
    assert(s2.ctx == s.ctx.insert(cid, ctx2));
    assert(s2.writes == s.writes && s2.seen == s.seen && s2.sent == s.sent && s2.chans == s.chans);
    assert(counters_grow(c, s, s2)) by {
        assert forall|o: int| #![trigger ctr(s2, o)] server(c.n, o) implies ctr(s, o) <= ctr(s2, o) by {}
    }
    assert forall|x: VC| avail(c, s, x) implies #[trigger] avail(c, s2, x) by {
        lemma_avail_grows(c, s, s2, x);
    }
    // The clock the client merges into deps is sound and available.
    let dk = join(dep(cl.deps, c.n, key), e.vc);
    assert(sound(s, c.n, dk) && avail(c, s, dk)) by {
        let a = dep(cl.deps, c.n, key);
        lemma_zero_known(s, c.n);
        lemma_avail_zero(c, s);
        if cl.deps.dom().contains(key) { assert(deps_ready(c, s, cl.deps)); assert(cl.deps.dom().contains(key)); }
        lemma_join_lub_of(c.n, a, e.vc);
        lemma_lub_sound(s, c.n, a, |x: VC| x == e.vc, dk);
        reveal(writes_ok);
        lemma_lub_avail(c, s, a, |x: VC| x == e.vc, dk);
    }
    lemma_returned_clock(c, s, cid, srv, key, t, r);
    // The returned clock is sound.
    assert(sound(s, c.n, r.vc)) by {
        if cl.local.dom().contains(key) {
            reveal(clocks_ok);
            assert(entries_sound(s, c.n, cl.local));
            lemma_join_lub_of(c.n, cl.local[key].vc, e.vc);
            lemma_lub_sound(s, c.n, cl.local[key].vc, |x: VC| x == e.vc, r.vc);
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
            if o == srv {
                lemma_sound_grows(c, s, s2, t.gvc);
                assert forall|k: int| #[trigger] t.ccache.dom().contains(k) implies sound(s2, c.n, t.ccache[k].vc) by {
                    assert(entry_ok(c, s, k, t.ccache[k]));
                    lemma_sound_grows(c, s, s2, t.ccache[k].vc);
                }
            } else {
                lemma_sound_grows(c, s, s2, s.servers[o].gvc);
                lemma_entries_sound_grows(c, s, s2, s.servers[o].ccache);
            }
        }
        assert forall|id: int| #[trigger] s2.clients.dom().contains(id) implies {
            &&& map_sound(s2, c.n, s2.clients[id].deps)
            &&& entries_sound(s2, c.n, s2.clients[id].local)
        } by {
            lemma_map_sound_grows(c, s, s2, s.clients[id].deps);
            lemma_entries_sound_grows(c, s, s2, s.clients[id].local);
            if id == cid {
                lemma_sound_grows(c, s, s2, dk);
                assert forall|k: int| #[trigger] deps2.dom().contains(k) implies sound(s2, c.n, deps2[k]) by {
                    if k != key { assert(cl.deps.dom().contains(k)); }
                }
            }
        }
        assert forall|i: int| #![trigger s2.history[i]] 0 <= i < s2.history.len() && s2.history[i] is Read implies {
            &&& sound(s2, c.n, s2.history[i]->Read_server_vc)
            &&& sound(s2, c.n, s2.history[i]->Read_vc)
        } by {
            if i == s.history.len() {
                lemma_sound_grows(c, s, s2, e.vc);
                lemma_sound_grows(c, s, s2, r.vc);
            } else {
                assert(s2.history[i] == s.history[i]);
                lemma_sound_grows(c, s, s2, s.history[i]->Read_server_vc);
                lemma_sound_grows(c, s, s2, s.history[i]->Read_vc);
            }
        }
    }
    assert(fifo_ok(c, s2)) by { reveal(fifo_ok); }
    assert(msg_ok(c, s2)) by { reveal(msg_ok); }
    assert(forward_ok(c, s2)) by { reveal(forward_ok); }
    assert(progress_ok(c, s2)) by { reveal(progress_ok); }
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
            if q == srv { assert(seen_covered(c, s, srv, t)); }
            else { assert(s2.servers[q] == s.servers[q]); }
        }
    }
    assert(avail_ok(c, s2)) by {
        reveal(avail_ok);
        assert forall|q: int, k: int| #![trigger s2.servers[q].ccache.dom().contains(k)]
            server(c.n, q) && s2.servers[q].ccache.dom().contains(k)
            implies avail(c, s2, s2.servers[q].ccache[k].vc) by {
            if q == srv {
                assert(s2.servers[q] == t);
                assert(entry_ok(c, s, k, t.ccache[k]));
            } else {
                assert(s2.servers[q] == s.servers[q]);
                assert(s.servers[q].ccache.dom().contains(k));
            }
        }
        assert forall|id: int, k: int| #![trigger s2.clients[id].deps.dom().contains(k)]
            s2.clients.dom().contains(id) && s2.clients[id].deps.dom().contains(k)
            implies avail(c, s2, s2.clients[id].deps[k]) by {
            if !(id == cid && k == key) { assert(s.clients[id].deps.dom().contains(k)); }
        }
    }
    assert(cut_ok(c, s2)) by {
        reveal(cut_ok);
        assert forall|q: int| #[trigger] server(c.n, q) implies cut(c, s2, q) by {
            if q != srv { assert(s2.servers[q] == s.servers[q]); assert(cut(c, s, q)); }
        }
    }
    assert(cache_ok(c, s2)) by {
        reveal(cache_ok);
        assert forall|q: int, k: int| #![trigger s2.servers[q].ccache.dom().contains(k)]
            server(c.n, q) && s2.servers[q].ccache.dom().contains(k) implies {
            let e2 = s2.servers[q].ccache[k];
            &&& forall|o: int| 0 <= o < c.n && #[trigger] e2.vc[o] >= 1 ==>
                exists|w: Version| #[trigger] s2.writes.contains(w) && w.key == k && le(w.vc, e2.vc) && w.vc[o] == e2.vc[o]
            &&& exists|w: Version| #[trigger] s2.writes.contains(w) && w.key == k && le(w.vc, e2.vc) && w.value == e2.value
        } by {
            if q == srv {
                assert(s2.servers[q] == t);
                assert(entry_ok(c, s, k, t.ccache[k]));
            } else {
                assert(s2.servers[q] == s.servers[q]);
                assert(s.servers[q].ccache.dom().contains(k));
            }
        }
    }
    lemma_read_observed(c, s, s2, cid, srv, key, t, r);
    assert(client_ok(c, s2)) by {
        reveal(client_ok);
        lemma_reached_mono(s.writes, cl.deps, s2.writes, deps2);
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
                assert forall|k: int| #[trigger] cl.local.dom().contains(k) implies
                    exists|w: Version| #[trigger] s2.ctx[id].contains(w) && w.key == k
                        && w.vc == cl.local[k].vc && w.value == cl.local[k].value by {
                    let w = choose|w: Version| #[trigger] s.ctx[id].contains(w) && w.key == k
                        && w.vc == cl.local[k].vc && w.value == cl.local[k].value;
                    assert(s2.ctx[id].contains(w));
                }
            }
        }
    }
    lemma_step_read_events(c, s, s2, cid, srv, key, t, r);
}

/// Observed writes and their contexts are reachable from the new deps, and
/// those of the read key lie below the reply.
pub proof fn lemma_read_observed(c: Constants, s: State, s2: State, cid: int, srv: int, key: int, t: Server, r: Entry)
    requires inv(c, s), client_read(c, s, s2, cid, srv, key, t, r)
    ensures
        observed(s, key, entry(t, c.n, key).vc).subset_of(s.writes),
        forall|w: Version| #[trigger] observed(s, key, entry(t, c.n, key).vc).contains(w) ==>
            reached(s.writes, s2.clients[cid].deps).contains(w)
            && (w.key == key ==> le(w.vc, entry(t, c.n, key).vc)),
{
    let cl = s.clients[cid];
    let e = entry(t, c.n, key);
    let deps2 = cl.deps.insert(key, join(dep(cl.deps, c.n, key), e.vc));
    lemma_server_ready(c, s, srv);
    lemma_deps_ready(c, s, cid);
    lemma_integrate(c, s, srv, cl.deps, t);
    lemma_reply(c, s, srv, cid, t, key);
    assert(s2.clients[cid].deps == deps2);
    assert forall|w: Version| #[trigger] observed(s, key, e.vc).contains(w) implies
        reached(s.writes, deps2).contains(w) && (w.key == key ==> le(w.vc, e.vc)) by {
        let i = choose|i: int| #![trigger s.history[i]] 0 <= i < s.history.len() && {
            let ev = s.history[i];
            &&& ev is Write
            &&& ev->Write_version.key == key && le(ev->Write_version.vc, e.vc)
            &&& ev->Write_ctx.contains(w)
        };
        let w0 = s.history[i]->Write_version;
        reveal(events_ok);
        assert(ev_ctx(s.history[i]).contains(w));
        assert(ev_ctx(s.history[i]).subset_of(s.writes));
        assert(s.writes.contains(w0));
        lemma_join_lub(dep(cl.deps, c.n, key), e.vc);
        lemma_le_trans(w0.vc, e.vc, deps2[key]);
        lemma_singleton_chain(s.writes, deps2, w0);
        if w != w0 {
            assert(reached(s.writes, w0.deps).contains(w));
            lemma_reached_prepend(s.writes, deps2, w0, w);
            lemma_reached_below(c, s, s.writes, w0.deps, w);
            let k = choose|k: int| #[trigger] w0.deps.dom().contains(k) && le(w.vc, w0.deps[k]);
            reveal(writes_ok);
            lemma_le_trans(w.vc, w0.deps[k], w0.vc);
            lemma_le_trans(w.vc, w0.vc, e.vc);
        }
    }
}

/// The local write's clock is sound, and the returned clock dominates the reply.
pub proof fn lemma_returned_clock(c: Constants, s: State, cid: int, srv: int, key: int, t: Server, r: Entry)
    requires inv(c, s), s.clients.dom().contains(cid), server(c.n, srv),
        integrated(c.n, s.servers[srv], s.clients[cid].deps, t),
        returned(c.n, s.clients[cid], key, entry(t, c.n, key), r),
    ensures
        le(entry(t, c.n, key).vc, r.vc),
        s.clients[cid].local.dom().contains(key) ==> sound(s, c.n, s.clients[cid].local[key].vc)
            && le(s.clients[cid].local[key].vc, r.vc),
{
    let cl = s.clients[cid];
    let e = entry(t, c.n, key);
    lemma_reply(c, s, srv, cid, t, key);
    if cl.local.dom().contains(key) {
        reveal(clocks_ok);
        assert(entries_sound(s, c.n, cl.local));
        assert(sound(s, c.n, cl.local[key].vc));
        lemma_join_lub(cl.local[key].vc, e.vc);
    } else {
        lemma_le_refl(e.vc);
    }
}

/// The new read event satisfies `read_ok`.
pub proof fn lemma_new_read_ok(c: Constants, s: State, s2: State, cid: int, srv: int, key: int, t: Server, r: Entry)
    requires inv(c, s), client_read(c, s, s2, cid, srv, key, t, r)
    ensures read_ok(c, s2.history[s.history.len() as int])
{
    let cl = s.clients[cid];
    let e = entry(t, c.n, key);
    let obs = observed(s, key, e.vc);
    let ctx2 = s.ctx[cid].union(obs);
    let ev = Event::Read { client: cid, key, server_vc: e.vc, vc: r.vc, value: r.value, ctx: ctx2 };
    assert(s2.history[s.history.len() as int] == ev);
    lemma_server_ready(c, s, srv);
    lemma_deps_ready(c, s, cid);
    lemma_integrate(c, s, srv, cl.deps, t);
    lemma_reply(c, s, srv, cid, t, key);
    lemma_read_observed(c, s, s2, cid, srv, key, t, r);
    lemma_returned_clock(c, s, cid, srv, key, t, r);
    reveal(client_ok);
    assert forall|w: Version| s.writes.contains(w) && w.key == key && le(w.vc, e.vc) implies #[trigger] obs.contains(w) by {
        let i = lemma_write_event(c, s, w);
    }
    assert forall|w: Version| #[trigger] ev_ctx(ev).contains(w) && w.key == key implies le(w.vc, r.vc) by {
        if obs.contains(w) {
            lemma_le_trans(w.vc, e.vc, r.vc);
        } else {
            assert(s.ctx[cid].contains(w));
            if le(w.vc, local_entry(cl, c.n, key).vc) {
                if !cl.local.dom().contains(key) { lemma_version_positive(c, s, w, zero(c.n)); }
                lemma_le_trans(w.vc, cl.local[key].vc, r.vc);
            } else {
                lemma_le_trans(w.vc, e.vc, r.vc);
            }
        }
    }
    assert forall|o: int| 0 <= o < c.n && #[trigger] e.vc[o] >= 1 implies
        exists|w: Version| #[trigger] ev_ctx(ev).contains(w) && w.key == key && w.vc[o] == e.vc[o] by {
        if !t.ccache.dom().contains(key) {
            assert(e == initial_entry(c.n));
            assert(e.vc[o] == 0);
        }
        assert(entry_ok(c, s, key, e));
        let w = choose|w: Version| #[trigger] s.writes.contains(w) && w.key == key && le(w.vc, e.vc) && w.vc[o] == e.vc[o];
        assert(obs.contains(w));
        assert(ev_ctx(ev).contains(w));
    }
    assert forall|o: int| 0 <= o < c.n && #[trigger] r.vc[o] >= 1 implies
        exists|w: Version| #[trigger] ev_ctx(ev).contains(w) && w.key == key && w.vc[o] == r.vc[o] by {
        if cl.local.dom().contains(key) && r.vc[o] != e.vc[o] {
            let w = choose|w: Version| #[trigger] s.ctx[cid].contains(w) && w.key == key
                && w.vc == cl.local[key].vc && w.value == cl.local[key].value;
            assert(ev_ctx(ev).contains(w));
        } else {
            assert(e.vc[o] >= 1);
        }
    }
    if !(r.vc == zero(c.n) && r.value == 0) {
        lemma_step_read_value(c, s, s2, cid, srv, key, t, r);
    }
}

pub proof fn lemma_step_read_events(c: Constants, s: State, s2: State, cid: int, srv: int, key: int, t: Server, r: Entry)
    requires inv(c, s), client_read(c, s, s2, cid, srv, key, t, r)
    ensures events_ok(c, s2)
{
    let cl = s.clients[cid];
    let e = entry(t, c.n, key);
    let obs = observed(s, key, e.vc);
    let ctx2 = s.ctx[cid].union(obs);
    let h = s.history;
    let h2 = s2.history;
    let j = h.len() as int;
    lemma_read_observed(c, s, s2, cid, srv, key, t, r);
    lemma_new_read_ok(c, s, s2, cid, srv, key, t, r);
    assert(h2 == h.push(Event::Read { client: cid, key, server_vc: e.vc, vc: r.vc, value: r.value, ctx: ctx2 }));
    assert(s2.ctx == s.ctx.insert(cid, ctx2));
    assert(s2.writes == s.writes && s2.clients.dom() == s.clients.dom());
    reveal(events_ok);
    reveal(client_ok);
    assert(s.ctx[cid].subset_of(s.writes));
    assert forall|i: int| #![trigger h2[i]] 0 <= i < h2.len() implies event_ok(c, s2, i) by {
        if i < j {
            assert(h2[i] == h[i]);
            assert(event_ok(c, s, i));
        }
    }
    assert forall|w: Version| #[trigger] s2.writes.contains(w) implies exists|i: int|
        0 <= i < h2.len() && #[trigger] h2[i] is Write && h2[i]->Write_version == w by {
        let i = choose|i: int| 0 <= i < h.len() && #[trigger] h[i] is Write && h[i]->Write_version == w;
        assert(h2[i] == h[i]);
    }
    assert forall|i: int, k: int| #![trigger super::properties::edge(h2, i, k)]
        super::properties::edge(h2, i, k) implies ev_ctx(h2[i]).subset_of(ev_ctx(h2[k])) by {
        if k == j {
            assert(h2[i] == h[i]);
            assert(event_ok(c, s, i));
            if super::properties::observes(h2, i, k) {
                assert forall|w: Version| #[trigger] ev_ctx(h2[i]).contains(w) implies ev_ctx(h2[k]).contains(w) by {
                    assert(ev_ctx(h[i]).subset_of(s.writes));
                    assert(obs.contains(w));
                }
            }
        } else {
            assert(h2[i] == h[i] && h2[k] == h[k]);
            assert(super::properties::edge(h, i, k));
            lemma_edge_ctx(c, s, i, k);
        }
    }
}

/// The value a read returns belongs to an observed or own write of the key.
pub proof fn lemma_step_read_value(c: Constants, s: State, s2: State, cid: int, srv: int, key: int, t: Server, r: Entry)
    requires inv(c, s), client_read(c, s, s2, cid, srv, key, t, r), !(r.vc == zero(c.n) && r.value == 0)
    ensures ({
        let e = entry(t, c.n, key);
        let ctx2 = s.ctx[cid].union(observed(s, key, e.vc));
        exists|w: Version| #[trigger] ctx2.contains(w) && w.key == key && le(w.vc, r.vc) && w.value == r.value
    }),
{
    let cl = s.clients[cid];
    let e = entry(t, c.n, key);
    let obs = observed(s, key, e.vc);
    let ctx2 = s.ctx[cid].union(obs);
    lemma_reply(c, s, srv, cid, t, key);
    lemma_returned_clock(c, s, cid, srv, key, t, r);
    reveal(client_ok);
    let from_server = t.ccache.dom().contains(key) && r.value == e.value;
    if from_server {
        let w = choose|w: Version| #[trigger] s.writes.contains(w) && w.key == key && le(w.vc, e.vc) && w.value == e.value;
        let i = lemma_write_event(c, s, w);
        assert(obs.contains(w));
        lemma_le_trans(w.vc, e.vc, r.vc);
        assert(ctx2.contains(w) && w.key == key && le(w.vc, r.vc) && w.value == r.value);
    } else {
        assert(cl.local.dom().contains(key)) by {
            if !cl.local.dom().contains(key) { assert(r == e); }
        }
        let l = cl.local[key];
        let w = choose|w: Version| #[trigger] s.ctx[cid].contains(w) && w.key == key && w.vc == l.vc && w.value == l.value;
        assert(s.writes.contains(w));
        assert(r.value == l.value) by {
            if r.value != l.value {
                assert(r.value == e.value);
                if !t.ccache.dom().contains(key) {
                    lemma_zero_known(s, c.n);
                    assert(le(e.vc, l.vc)) by { lemma_zero_le(c.n, l.vc); reveal(writes_ok); }
                }
            }
        }
        assert(ctx2.contains(w) && w.key == key && le(w.vc, r.vc) && w.value == r.value);
    }
}

} // verus!
