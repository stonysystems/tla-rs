//! Preservation for a propagation message that is stored and forwarded.
use vstd::prelude::*;
use super::vc::*;
use super::ring::*;
use super::types::*;
use super::model::*;
use super::invariants::*;
use super::frame::*;

verus! {

pub proof fn lemma_step_forward(c: Constants, s: State, s2: State, src: int, mid: Server, t: Server)
    requires inv(c, s), propagate(c, s, s2, src, mid, t), !is_tail(c, s, src)
    ensures inv(c, s2)
{
    assert(shape_ok(c, s));
    let m = s.chans[src][0];
    let v = m.version;
    let h = m.hop;
    let r = succ(c.n, src);
    let out = Msg { version: v, hop: h + 1 };
    let del = delivered(s, src);
    assert(server(c.n, r)) by { vstd::arithmetic::div_mod::lemma_mod_bound(src + 1, c.n as int); }
    assert(m == s.sent[src][del] && 0 <= del < s.sent[src].len()) by {
        reveal(fifo_ok);
        assert(s.chans[src].len() <= s.sent[src].len());
    }
    assert(s.writes.contains(v) && 1 <= h < tail_hop(c) && at(c.n, v.origin, (h - 1) as nat) == src) by {
        reveal(msg_ok);
    }
    assert(server(c.n, v.origin)) by { reveal(writes_ok); }
    assert(at(c.n, v.origin, h) == r) by { lemma_at_succ(c.n, v.origin, (h - 1) as nat); }
    let sv = s.servers[r];
    assert(t == stored(c, s, src));
    assert(t.ccache == sv.ccache && t.gvc == sv.gvc && sv.icache.subset_of(t.icache));
    assert(s2.writes == s.writes && s2.clients == s.clients && s2.ctx == s.ctx && s2.history == s.history);
    assert(s2.servers == s.servers.update(r, t));
    assert(s2.seen == s.seen.update(r, s.seen[r].insert(v)));
    assert(s2.sent == s.sent.update(r, s.sent[r].push(out)));
    assert(counters_grow(c, s, s2)) by {
        assert forall|o: int| #![trigger ctr(s2, o)] server(c.n, o) implies ctr(s, o) <= ctr(s2, o) by {}
    }
    assert forall|x: VC| avail(c, s, x) implies #[trigger] avail(c, s2, x) by {
        lemma_avail_grows(c, s, s2, x);
    }
    assert(forall|q: int| #![trigger s2.servers[q]] server(c.n, q) ==>
        s2.servers[q].ccache == s.servers[q].ccache && s2.servers[q].gvc == s.servers[q].gvc);
    assert(forall|q: int, k: int| #![trigger entry(s2.servers[q], c.n, k)] server(c.n, q) ==>
        entry(s2.servers[q], c.n, k) == entry(s.servers[q], c.n, k));
    assert(forall|q: int, i: int| #![trigger s2.sent[q][i]] server(c.n, q) && 0 <= i < s.sent[q].len()
        ==> s2.sent[q][i] == s.sent[q][i]);
    assert(s2.sent[r][s.sent[r].len() as int] == out);

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
            assert(s.servers[o] == s.servers[o]);
            lemma_sound_grows(c, s, s2, s.servers[o].gvc);
            lemma_entries_sound_grows(c, s, s2, s.servers[o].ccache);
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
            lemma_sound_grows(c, s, s2, s.history[i]->Read_server_vc);
            lemma_sound_grows(c, s, s2, s.history[i]->Read_vc);
        }
    }
    assert(fifo_ok(c, s2)) by {
        reveal(fifo_ok);
        let chans1 = s.chans.update(src, s.chans[src].drop_first());
        assert(s2.chans == chans1.update(r, chans1[r].push(out)));
        assert forall|q: int| #![trigger s2.chans[q]] server(c.n, q) implies {
            &&& s2.chans[q].len() <= s2.sent[q].len()
            &&& forall|i: int| #![trigger s2.chans[q][i]] 0 <= i < s2.chans[q].len()
                ==> s2.chans[q][i] == s2.sent[q][i + delivered(s2, q)]
            &&& forall|i: int| #![trigger s2.sent[q][i]] 0 <= i < delivered(s2, q)
                ==> s2.seen[succ(c.n, q)].contains(s2.sent[q][i].version)
        } by {
            assert(s.chans[q].len() <= s.sent[q].len());
            let dq = delivered(s, q);
            if q == src {
                assert(delivered(s2, q) == dq + 1);
                assert forall|i: int| #![trigger s2.chans[q][i]] 0 <= i < s2.chans[q].len()
                    implies s2.chans[q][i] == s2.sent[q][i + delivered(s2, q)] by {
                    if q == r && i == s2.chans[q].len() - 1 {
                        assert(s2.chans[q][i] == out);
                    } else {
                        assert(s2.chans[q][i] == s.chans[q][i + 1]);
                        assert(s.chans[q][i + 1] == s.sent[q][i + 1 + dq]);
                    }
                }
                assert forall|i: int| #![trigger s2.sent[q][i]] 0 <= i < delivered(s2, q)
                    implies s2.seen[succ(c.n, q)].contains(s2.sent[q][i].version) by {
                    assert(s2.sent[q][i] == s.sent[q][i]);
                    if i < dq { assert(s.seen[succ(c.n, q)].contains(s.sent[q][i].version)); }
                }
            } else if q == r {
                assert(delivered(s2, q) == dq);
                assert forall|i: int| #![trigger s2.chans[q][i]] 0 <= i < s2.chans[q].len()
                    implies s2.chans[q][i] == s2.sent[q][i + delivered(s2, q)] by {
                    if i < s.chans[q].len() { assert(s2.chans[q][i] == s.chans[q][i]); }
                }
                assert forall|i: int| #![trigger s2.sent[q][i]] 0 <= i < delivered(s2, q)
                    implies s2.seen[succ(c.n, q)].contains(s2.sent[q][i].version) by {
                    assert(s.seen[succ(c.n, q)].contains(s.sent[q][i].version));
                }
            } else {
                assert(s2.chans[q] == s.chans[q]);
                assert(s2.sent[q] == s.sent[q]);
                assert forall|i: int| #![trigger s2.sent[q][i]] 0 <= i < delivered(s2, q)
                    implies s2.seen[succ(c.n, q)].contains(s2.sent[q][i].version) by {
                    assert(s.seen[succ(c.n, q)].contains(s.sent[q][i].version));
                }
            }
        }
    }
    assert(msg_ok(c, s2)) by {
        reveal(msg_ok);
        assert forall|q: int, i: int| #![trigger s2.sent[q][i]] server(c.n, q) && 0 <= i < s2.sent[q].len() implies {
            let mm = s2.sent[q][i];
            &&& s2.writes.contains(mm.version)
            &&& 1 <= mm.hop <= tail_hop(c)
            &&& at(c.n, mm.version.origin, (mm.hop - 1) as nat) == q
        } by {
            if !(q == r && i == s.sent[r].len()) { assert(s2.sent[q][i] == s.sent[q][i]); }
        }
    }
    assert(forward_ok(c, s2)) by {
        reveal(forward_ok);
        assert forall|w: Version| #[trigger] s2.writes.contains(w) implies
            exists|i: int| 0 <= i < s2.sent[w.origin].len() && #[trigger] s2.sent[w.origin][i] == (Msg { version: w, hop: 1 }) by {
            let i = choose|i: int| 0 <= i < s.sent[w.origin].len() && #[trigger] s.sent[w.origin][i] == (Msg { version: w, hop: 1 });
            reveal(writes_ok);
            assert(s2.sent[w.origin][i] == s.sent[w.origin][i]);
        }
        assert forall|q: int, w: Version| #![trigger s2.seen[q].contains(w)] server(c.n, q) && s2.seen[q].contains(w) implies
            exists|i: int| 0 <= i < s2.sent[q].len() && #[trigger] s2.sent[q][i].version == w by {
            if q == r && w == v {
                assert(s2.sent[q][s.sent[r].len() as int].version == w);
            } else {
                let i = choose|i: int| 0 <= i < s.sent[q].len() && #[trigger] s.sent[q][i].version == w;
                assert(s2.sent[q][i] == s.sent[q][i]);
            }
        }
    }
    assert(progress_ok(c, s2)) by {
        reveal(progress_ok);
        assert forall|q: int, i: int| #![trigger s2.sent[q][i]]
            server(c.n, q) && 0 <= i < s2.sent[q].len() && s2.sent[q][i].hop >= 2 implies
            exists|p: int, j: int| #![trigger s2.sent[p][j]]
                server(c.n, p) && succ(c.n, p) == q && 0 <= j < delivered(s2, p)
                && s2.sent[p][j] == (Msg { version: s2.sent[q][i].version, hop: (s2.sent[q][i].hop - 1) as nat }) by {
            reveal(fifo_ok);
            if q == r && i == s.sent[r].len() {
                assert(s2.sent[src][del] == s.sent[src][del]);
                assert(delivered(s2, src) == del + 1) by {
                    assert(s.chans[src].len() <= s.sent[src].len());
                }
            } else {
                assert(s2.sent[q][i] == s.sent[q][i]);
                let (p, j) = choose|p: int, j: int| #![trigger s.sent[p][j]]
                    server(c.n, p) && succ(c.n, p) == q && 0 <= j < delivered(s, p)
                    && s.sent[p][j] == (Msg { version: s.sent[q][i].version, hop: (s.sent[q][i].hop - 1) as nat });
                assert(s.chans[p].len() <= s.sent[p].len());
                assert(s2.sent[p][j] == s.sent[p][j]);
                assert(delivered(s, p) <= delivered(s2, p));
            }
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
            if q == r && i == s.sent[r].len() {
                assert(s2.sent[q][i] == out);
                assert(s.writes.contains(w));
                if j == h {
                    assert(w.origin == r);
                    reveal(forward_ok);
                    assert(exists|i1: int| 0 <= i1 < s.sent[w.origin].len() && #[trigger] s.sent[w.origin][i1] == (Msg { version: w, hop: 1 }));
                    let i1 = choose|i1: int| 0 <= i1 < s.sent[w.origin].len() && #[trigger] s.sent[w.origin][i1] == (Msg { version: w, hop: 1 });
                    assert(s2.sent[q][i1] == s.sent[q][i1]);
                    assert(0 <= i1 < i && s2.sent[q][i1].version == w);
                } else {
                    assert(j < h && h < j + c.n);
                    assert(s.sent[src][del] == m);
                    assert(at(c.n, s.sent[src][del].version.origin, j) == w.origin);
                    assert(w != s.sent[src][del].version && w.vc[w.origin] <= s.sent[src][del].version.vc[w.origin]);
                    assert(exists|i2: int| 0 <= i2 < del && #[trigger] s.sent[src][i2].version == w);
                    let i2 = choose|i2: int| 0 <= i2 < del && #[trigger] s.sent[src][i2].version == w;
                    reveal(fifo_ok);
                    assert(s.chans[src].len() <= s.sent[src].len());
                    assert(s.seen[succ(c.n, src)].contains(s.sent[src][i2].version));
                    assert(s.seen[r].contains(w));
                    reveal(forward_ok);
                    assert(exists|i3: int| 0 <= i3 < s.sent[r].len() && #[trigger] s.sent[r][i3].version == w);
                    let i3 = choose|i3: int| 0 <= i3 < s.sent[r].len() && #[trigger] s.sent[r][i3].version == w;
                    assert(s2.sent[q][i3] == s.sent[q][i3]);
                    assert(0 <= i3 < i && s2.sent[q][i3].version == w);
                }
            } else {
                assert(i < s.sent[q].len());
                assert(s2.sent[q][i] == s.sent[q][i]);
                assert(s.writes.contains(w));
                assert(at(c.n, s.sent[q][i].version.origin, j) == w.origin);
                assert(exists|i2: int| 0 <= i2 < i && #[trigger] s.sent[q][i2].version == w);
                let i2 = choose|i2: int| 0 <= i2 < i && #[trigger] s.sent[q][i2].version == w;
                assert(s2.sent[q][i2] == s.sent[q][i2]);
                assert(s2.sent[q][i2].version == w);
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
            if q == r {
                assert forall|w: Version| #[trigger] s2.seen[q].contains(w) implies
                    s2.servers[q].icache.contains(w) || le(w.vc, entry(s2.servers[q], c.n, w.key).vc) by {
                    if w != v { assert(s.seen[q].contains(w)); }
                }
            }
        }
    }
    assert(avail_ok(c, s2)) by {
        reveal(avail_ok);
        assert forall|q: int, k: int| #![trigger s2.servers[q].ccache.dom().contains(k)]
            server(c.n, q) && s2.servers[q].ccache.dom().contains(k)
            implies avail(c, s2, s2.servers[q].ccache[k].vc) by {
            assert(s.servers[q].ccache.dom().contains(k));
        }
    }
    assert(cut_ok(c, s2)) by {
        reveal(cut_ok);
        assert forall|q: int| #[trigger] server(c.n, q) implies cut(c, s2, q) by {
            assert(cut(c, s, q));
            reveal(cut_srv);
            if q == r && !has_seen(c.n, sv, v) {
                assert(t.icache == sv.icache.insert(v));
                assert(!le(v.vc, entry(sv, c.n, v.key).vc));
            }
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
            assert(s.servers[q].ccache.dom().contains(k));
        }
    }
    assert(events_ok(c, s2)) by { reveal(events_ok); }
}

} // verus!
