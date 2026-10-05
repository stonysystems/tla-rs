//! Initialization and the client-only steps: start, fork, stutter.
use vstd::prelude::*;
use super::vc::*;
use super::ring::*;
use super::types::*;
use super::model::*;
use super::invariants::*;
use super::integration::*;
use super::frame::*;

verus! {

pub proof fn lemma_init(c: Constants, s: State)
    requires init(c, s), c.rounds >= 2
    ensures inv(c, s)
{
    assert forall|o: int| server(c.n, o) implies #[trigger] s.servers[o] == empty_server(c.n) by {}
    assert(s.clients.dom() =~= s.ctx.dom());
    assert(shape_ok(c, s));
    lemma_zero_known(s, c.n);
    assert(writes_ok(c, s)) by { reveal(writes_ok); }
    assert(clocks_ok(c, s)) by {
        reveal(clocks_ok);
        assert forall|o: int| #![trigger s.servers[o]] server(c.n, o) implies {
            &&& sound(s, c.n, s.servers[o].gvc)
            &&& entries_sound(s, c.n, s.servers[o].ccache)
        } by {
            assert(s.servers[o] == empty_server(c.n));
            assert forall|q: int| 0 <= q < c.n implies #[trigger] zero(c.n)[q] <= ctr(s, q) by {
                assert(s.servers[q] == empty_server(c.n));
            }
        }
    }
    assert(fifo_ok(c, s)) by { reveal(fifo_ok); }
    assert(msg_ok(c, s)) by { reveal(msg_ok); }
    assert(forward_ok(c, s)) by { reveal(forward_ok); }
    assert(progress_ok(c, s)) by { reveal(progress_ok); }
    assert(drag_ok(c, s)) by { reveal(drag_ok); }
    assert(seen_ok(c, s)) by {
        reveal(seen_ok);
        assert forall|q: int| #![trigger s.seen[q]] server(c.n, q) implies {
            &&& s.seen[q].subset_of(s.writes)
            &&& s.servers[q].icache.subset_of(s.seen[q])
            &&& forall|w: Version| #[trigger] s.seen[q].contains(w) ==>
                s.servers[q].icache.contains(w) || le(w.vc, entry(s.servers[q], c.n, w.key).vc)
            &&& forall|w: Version| #[trigger] s.writes.contains(w) && w.origin == q ==> s.seen[q].contains(w)
        } by {
            assert(s.servers[q] == empty_server(c.n));
        }
    }
    assert(avail_ok(c, s)) by {
        reveal(avail_ok);
        assert forall|q: int, k: int| #![trigger s.servers[q].ccache.dom().contains(k)]
            server(c.n, q) && s.servers[q].ccache.dom().contains(k)
            implies avail(c, s, s.servers[q].ccache[k].vc) by {
            assert(s.servers[q] == empty_server(c.n));
        }
    }
    assert(cut_ok(c, s)) by {
        reveal(cut_ok);
        assert forall|q: int| #[trigger] server(c.n, q) implies cut(c, s, q) by { reveal(cut_srv); }
    }
    assert(client_ok(c, s)) by { reveal(client_ok); }
    assert(cache_ok(c, s)) by {
        reveal(cache_ok);
        assert forall|q: int, k: int| #![trigger s.servers[q].ccache.dom().contains(k)]
            server(c.n, q) && s.servers[q].ccache.dom().contains(k) implies false by {
            assert(s.servers[q] == empty_server(c.n));
        }
    }
    assert(events_ok(c, s)) by { reveal(events_ok); }
}


/// Steps that leave servers, writes and seen sets alone preserve soundness
/// and availability of every clock.
pub proof fn lemma_core_frame(c: Constants, s: State, s2: State)
    requires inv(c, s), s2.servers == s.servers, s2.writes == s.writes, s2.seen == s.seen
    ensures
        writes_ok(c, s2),
        forall|x: VC| sound(s, c.n, x) ==> #[trigger] sound(s2, c.n, x),
        forall|x: VC| avail(c, s, x) ==> #[trigger] avail(c, s2, x),
        forall|d: Map<int, VC>| map_sound(s, c.n, d) ==> #[trigger] map_sound(s2, c.n, d),
        forall|m: Map<int, Entry>| entries_sound(s, c.n, m) ==> #[trigger] entries_sound(s2, c.n, m),
{
    assert(shape_ok(c, s));
    assert(counters_grow(c, s, s2)) by {
        assert forall|o: int| #![trigger ctr(s2, o)] server(c.n, o) implies ctr(s, o) <= ctr(s2, o) by {}
    }
    assert forall|x: VC| sound(s, c.n, x) implies #[trigger] sound(s2, c.n, x) by { lemma_sound_grows(c, s, s2, x); }
    assert forall|x: VC| avail(c, s, x) implies #[trigger] avail(c, s2, x) by { lemma_avail_grows(c, s, s2, x); }
    assert forall|d: Map<int, VC>| map_sound(s, c.n, d) implies #[trigger] map_sound(s2, c.n, d) by {
        lemma_map_sound_grows(c, s, s2, d);
    }
    assert forall|m: Map<int, Entry>| entries_sound(s, c.n, m) implies #[trigger] entries_sound(s2, c.n, m) by {
        lemma_entries_sound_grows(c, s, s2, m);
    }
    assert(writes_ok(c, s2)) by {
        reveal(writes_ok);
        assert forall|w: Version| #[trigger] s2.writes.contains(w) implies {
            &&& server(c.n, w.origin)
            &&& sound(s2, c.n, w.vc)
            &&& w.vc[w.origin] >= 1
            &&& map_sound(s2, c.n, w.deps)
            &&& forall|k: int| #[trigger] w.deps.dom().contains(k) ==> le(w.deps[k], w.vc)
        } by {}
    }
}

/// A new client changes nothing any existing event or invariant mentions.
pub proof fn lemma_step_start(c: Constants, s: State, s2: State, cid: int)
    requires inv(c, s), start_client(s, s2, cid)
    ensures inv(c, s2)
{
    assert(shape_ok(c, s));
    assert(s2.clients == s.clients.insert(cid, empty_client()));
    assert(s2.ctx == s.ctx.insert(cid, Set::empty()));
    assert(s2.clients.dom() =~= s2.ctx.dom());
    lemma_core_frame(c, s, s2);
    assert(clocks_ok(c, s2)) by {
        reveal(clocks_ok);
        assert forall|o: int| #![trigger s2.servers[o]] server(c.n, o) implies {
            &&& sound(s2, c.n, s2.servers[o].gvc)
            &&& entries_sound(s2, c.n, s2.servers[o].ccache)
        } by { assert(s.servers[o] == s2.servers[o]); }
        assert forall|id: int| #[trigger] s2.clients.dom().contains(id) implies {
            &&& map_sound(s2, c.n, s2.clients[id].deps)
            &&& entries_sound(s2, c.n, s2.clients[id].local)
        } by {
            if id != cid { assert(s.clients.dom().contains(id)); }
            else {
                assert(map_sound(s2, c.n, s2.clients[id].deps));
                assert(entries_sound(s2, c.n, s2.clients[id].local));
            }
        }
        assert forall|i: int| #![trigger s2.history[i]] 0 <= i < s2.history.len() && s2.history[i] is Read implies {
            &&& sound(s2, c.n, s2.history[i]->Read_server_vc)
            &&& sound(s2, c.n, s2.history[i]->Read_vc)
        } by {}
    }
    assert(fifo_ok(c, s2)) by { reveal(fifo_ok); }
    assert(msg_ok(c, s2)) by { reveal(msg_ok); }
    assert(forward_ok(c, s2)) by { reveal(forward_ok); }
    assert(progress_ok(c, s2)) by { reveal(progress_ok); }
    assert(drag_ok(c, s2)) by { reveal(drag_ok); }
    assert(seen_ok(c, s2)) by { reveal(seen_ok); }
    assert(avail_ok(c, s2)) by {
        reveal(avail_ok);
        assert forall|q: int, k: int| #![trigger s2.servers[q].ccache.dom().contains(k)]
            server(c.n, q) && s2.servers[q].ccache.dom().contains(k)
            implies avail(c, s2, s2.servers[q].ccache[k].vc) by {
            assert(s.servers[q].ccache.dom().contains(k));
        }
        assert forall|id: int, k: int| #![trigger s2.clients[id].deps.dom().contains(k)]
            s2.clients.dom().contains(id) && s2.clients[id].deps.dom().contains(k)
            implies avail(c, s2, s2.clients[id].deps[k]) by {
            assert(id != cid);
            assert(s.clients[id].deps.dom().contains(k));
        }
    }
    assert(cut_ok(c, s2)) by { reveal(cut_ok); }
    assert(client_ok(c, s2)) by {
        reveal(client_ok);
        assert forall|id: int| #[trigger] s2.clients.dom().contains(id) implies {
            let c2 = s2.clients[id];
            &&& s2.ctx[id].subset_of(s2.writes)
            &&& forall|w: Version| #[trigger] s2.ctx[id].contains(w) ==>
                le(w.vc, local_entry(c2, c.n, w.key).vc) || reached(s2.writes, c2.deps).contains(w)
            &&& forall|k: int| #[trigger] c2.local.dom().contains(k) ==>
                exists|w: Version| #[trigger] s2.ctx[id].contains(w) && w.key == k
                    && w.vc == c2.local[k].vc && w.value == c2.local[k].value
        } by {
            if id != cid { assert(s.clients.dom().contains(id)); }
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
        }
    }
    assert(events_ok(c, s2)) by {
        reveal(events_ok);
        assert forall|i: int| #![trigger s2.history[i]] 0 <= i < s2.history.len() implies event_ok(c, s2, i) by {
            assert(event_ok(c, s, i));
            assert(super::properties::actor(s.history[i]) != cid);
            if s.history[i] is Fork { assert(s.history[i]->Fork_child != cid); }
        }
    }
}

pub proof fn lemma_step_fork(c: Constants, s: State, s2: State, parent: int, child: int)
    requires inv(c, s), fork(s, s2, parent, child)
    ensures inv(c, s2)
{
    assert(shape_ok(c, s));
    let pc = s.ctx[parent];
    let h = s.history;
    let h2 = s2.history;
    let j = h.len() as int;
    assert(s2.clients == s.clients.insert(child, s.clients[parent]));
    assert(s2.ctx == s.ctx.insert(child, pc));
    assert(h2 == h.push(Event::Fork { parent, child, ctx: pc }));
    assert(s2.clients.dom() =~= s2.ctx.dom());
    lemma_core_frame(c, s, s2);
    assert(clocks_ok(c, s2)) by {
        reveal(clocks_ok);
        assert forall|o: int| #![trigger s2.servers[o]] server(c.n, o) implies {
            &&& sound(s2, c.n, s2.servers[o].gvc)
            &&& entries_sound(s2, c.n, s2.servers[o].ccache)
        } by { assert(s.servers[o] == s2.servers[o]); }
        assert forall|id: int| #[trigger] s2.clients.dom().contains(id) implies {
            &&& map_sound(s2, c.n, s2.clients[id].deps)
            &&& entries_sound(s2, c.n, s2.clients[id].local)
        } by {
            if id == child { assert(s.clients.dom().contains(parent)); }
            else { assert(s.clients.dom().contains(id)); }
        }
        assert forall|i: int| #![trigger s2.history[i]] 0 <= i < s2.history.len() && s2.history[i] is Read implies {
            &&& sound(s2, c.n, s2.history[i]->Read_server_vc)
            &&& sound(s2, c.n, s2.history[i]->Read_vc)
        } by {
            assert(i < j);
            assert(h2[i] == h[i]);
        }
    }
    assert(fifo_ok(c, s2)) by { reveal(fifo_ok); }
    assert(msg_ok(c, s2)) by { reveal(msg_ok); }
    assert(forward_ok(c, s2)) by { reveal(forward_ok); }
    assert(progress_ok(c, s2)) by { reveal(progress_ok); }
    assert(drag_ok(c, s2)) by { reveal(drag_ok); }
    assert(seen_ok(c, s2)) by { reveal(seen_ok); }
    assert(avail_ok(c, s2)) by {
        reveal(avail_ok);
        assert forall|q: int, k: int| #![trigger s2.servers[q].ccache.dom().contains(k)]
            server(c.n, q) && s2.servers[q].ccache.dom().contains(k)
            implies avail(c, s2, s2.servers[q].ccache[k].vc) by {
            assert(s.servers[q].ccache.dom().contains(k));
        }
        assert forall|id: int, k: int| #![trigger s2.clients[id].deps.dom().contains(k)]
            s2.clients.dom().contains(id) && s2.clients[id].deps.dom().contains(k)
            implies avail(c, s2, s2.clients[id].deps[k]) by {
            if id == child { assert(s.clients[parent].deps.dom().contains(k)); }
            else { assert(s.clients[id].deps.dom().contains(k)); }
        }
    }
    assert(cut_ok(c, s2)) by { reveal(cut_ok); }
    assert(client_ok(c, s2)) by {
        reveal(client_ok);
        assert forall|id: int| #[trigger] s2.clients.dom().contains(id) implies {
            let c2 = s2.clients[id];
            &&& s2.ctx[id].subset_of(s2.writes)
            &&& forall|w: Version| #[trigger] s2.ctx[id].contains(w) ==>
                le(w.vc, local_entry(c2, c.n, w.key).vc) || reached(s2.writes, c2.deps).contains(w)
            &&& forall|k: int| #[trigger] c2.local.dom().contains(k) ==>
                exists|w: Version| #[trigger] s2.ctx[id].contains(w) && w.key == k
                    && w.vc == c2.local[k].vc && w.value == c2.local[k].value
        } by {
            if id == child { assert(s.clients.dom().contains(parent)); }
            else { assert(s.clients.dom().contains(id)); }
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
        }
    }
    assert(events_ok(c, s2)) by {
        reveal(events_ok);
        reveal(client_ok);
        assert(pc.subset_of(s.writes));
        assert forall|i: int| #![trigger h2[i]] 0 <= i < h2.len() implies event_ok(c, s2, i) by {
            if i < j {
                assert(h2[i] == h[i]);
                assert(event_ok(c, s, i));
                assert(super::properties::actor(h[i]) != child);
                if h[i] is Fork { assert(h[i]->Fork_child != child); }
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
            } else {
                assert(h2[i] == h[i] && h2[k] == h[k]);
                assert(super::properties::edge(h, i, k));
            }
        }
    }
}

} // verus!
