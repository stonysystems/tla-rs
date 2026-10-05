//! Propagation along FIFO chains (paper Lemmas 1-3). When a version reaches its
//! tail after two rounds, every write its clock counts has reached all servers.
use vstd::prelude::*;
use super::vc::*;
use super::ring::*;
use super::types::*;
use super::model::*;
use super::invariants::*;

verus! {

/// Every earlier hop of a sent message was already delivered.
pub proof fn lemma_earlier_hop(c: Constants, s: State, q: int, i: int, h: nat)
    requires
        progress_ok(c, s), msg_ok(c, s), fifo_ok(c, s), shape_ok(c, s),
        server(c.n, q), 0 <= i < s.sent[q].len(), 1 <= h < s.sent[q][i].hop,
    ensures exists|p: int, j: int| #![trigger s.sent[p][j]]
        server(c.n, p) && 0 <= j < delivered(s, p)
        && s.sent[p][j] == (Msg { version: s.sent[q][i].version, hop: h })
    decreases s.sent[q][i].hop - h
{
    reveal(progress_ok);
    let m = s.sent[q][i];
    let (p, j) = choose|p: int, j: int| #![trigger s.sent[p][j]]
        server(c.n, p) && succ(c.n, p) == q && 0 <= j < delivered(s, p)
        && s.sent[p][j] == (Msg { version: m.version, hop: (m.hop - 1) as nat });
    if h < m.hop - 1 {
        reveal(fifo_ok);
        assert(s.chans[p].len() <= s.sent[p].len());
        lemma_earlier_hop(c, s, p, j, h);
    }
}

/// A delivered message's receiver has seen its version.
pub proof fn lemma_delivered_seen(c: Constants, s: State, p: int, j: int)
    requires fifo_ok(c, s), msg_ok(c, s), shape_ok(c, s), writes_ok(c, s), server(c.n, p), 0 <= j < delivered(s, p),
    ensures
        s.seen[at(c.n, s.sent[p][j].version.origin, s.sent[p][j].hop)].contains(s.sent[p][j].version),
        s.sent[p][j].hop >= 1, s.writes.contains(s.sent[p][j].version),
{
    reveal(fifo_ok);
    reveal(msg_ok);
    let m = s.sent[p][j];
    assert(s.chans[p].len() <= s.sent[p].len());
    assert(at(c.n, m.version.origin, (m.hop - 1) as nat) == p);
    assert(s.writes.contains(m.version));
    reveal(writes_ok);
    assert(server(c.n, m.version.origin));
    lemma_at_succ(c.n, m.version.origin, (m.hop - 1) as nat);
}

/// The version of the head message on src's channel at hop h has been seen by
/// the server it visits at any earlier hop.
pub proof fn lemma_visited_seen(c: Constants, s: State, src: int, h: nat)
    requires
        progress_ok(c, s), msg_ok(c, s), fifo_ok(c, s), shape_ok(c, s), seen_ok(c, s), writes_ok(c, s),
        server(c.n, src), s.chans[src].len() > 0,
        h < s.chans[src][0].hop,
    ensures s.seen[at(c.n, s.chans[src][0].version.origin, h)].contains(s.chans[src][0].version)
{
    reveal(fifo_ok);
    let i = delivered(s, src);
    assert(s.chans[src][0] == s.sent[src][i]);
    let v = s.sent[src][i].version;
    reveal(msg_ok);
    assert(s.writes.contains(v));
    reveal(writes_ok);
    if h == 0 {
        lemma_at_zero(c.n, v.origin);
        reveal(seen_ok);
        assert(server(c.n, v.origin));
    } else {
        lemma_earlier_hop(c, s, src, i, h);
        let (p, j) = choose|p: int, j: int| #![trigger s.sent[p][j]]
            server(c.n, p) && 0 <= j < delivered(s, p) && s.sent[p][j] == (Msg { version: v, hop: h });
        lemma_delivered_seen(c, s, p, j);
    }
}

/// Lemma 3: at the round-two tail, every write counted by the version's clock
/// has reached every server.
pub proof fn lemma_tail_avail(c: Constants, s: State, src: int)
    requires
        progress_ok(c, s), msg_ok(c, s), fifo_ok(c, s), drag_ok(c, s), shape_ok(c, s),
        seen_ok(c, s), writes_ok(c, s),
        server(c.n, src), s.chans[src].len() > 0, is_tail(c, s, src),
    ensures
        avail(c, s, s.chans[src][0].version.vc),
        s.seen[succ(c.n, src)].contains(s.chans[src][0].version),
{
    reveal(fifo_ok);
    let i0 = delivered(s, src);
    assert(s.chans[src][0] == s.sent[src][i0]);
    let msg = s.sent[src][i0];
    let v = msg.version;
    let o = v.origin;
    let n = c.n;
    let tl = tail_hop(c);
    reveal(msg_ok);
    assert(s.writes.contains(v));
    assert(msg.hop == tl);
    reveal(writes_ok);
    assert(server(n, o));
    assert(c.rounds * n >= 2 * n) by (nonlinear_arith) requires c.rounds >= 2, n >= 1;
    assert(tl >= 2 * n - 1);
    reveal(avail);
    assert forall|w: Version, q: int| #![trigger s.writes.contains(w), s.seen[q].contains(w)]
        s.writes.contains(w) && w.vc[w.origin] <= v.vc[w.origin] && server(n, q)
        implies s.seen[q].contains(w) by {
        let start = (tl - n) as nat;
        lemma_at_covers(n, o, start, q);
        let hq = choose|h: nat| start <= h < start + n && #[trigger] at(n, o, h) == q;
        lemma_visited_seen(c, s, src, hq);
        if w != v {
            reveal(seen_ok);
            if w.origin != q {
                // hq >= 1, so the message visiting q was sent from its predecessor.
                assert(n >= 2) by {
                    if n == 1 { assert(q == 0 && w.origin == 0); }
                }
                assert(hq >= 1);
                lemma_earlier_hop(c, s, src, i0, hq);
                let (p, j) = choose|p: int, j: int| #![trigger s.sent[p][j]]
                    server(n, p) && 0 <= j < delivered(s, p) && s.sent[p][j] == (Msg { version: v, hop: hq });
                // w's origin lies among the n - 1 hops before hq.
                let st2 = (hq - n + 1) as nat;
                lemma_at_covers(n, o, st2, w.origin);
                let jw = choose|h: nat| st2 <= h < st2 + n && #[trigger] at(n, o, h) == w.origin;
                assert(jw < hq);
                assert(s.sent[p][j].version == v && s.sent[p][j].hop == hq);
                assert(0 <= jw < hq && hq < jw + n);
                assert(at(n, s.sent[p][j].version.origin, jw) == w.origin);
                assert(s.chans[p].len() <= s.sent[p].len());
                assert(0 <= j < s.sent[p].len());
                reveal(drag_ok);
                assert(exists|i2: int| 0 <= i2 < j && #[trigger] s.sent[p][i2].version == w);
                let i2 = choose|i2: int| 0 <= i2 < j && #[trigger] s.sent[p][i2].version == w;
                lemma_delivered_seen(c, s, p, i2);
                assert(s.sent[p][i2].hop <= tl);
                assert(at(n, w.origin, s.sent[p][i2].hop) == q) by {
                    assert(at(n, w.origin, (s.sent[p][i2].hop - 1) as nat) == p);
                    assert(at(n, o, (hq - 1) as nat) == p);
                    lemma_at_succ(n, w.origin, (s.sent[p][i2].hop - 1) as nat);
                    lemma_at_succ(n, o, (hq - 1) as nat);
                }
            }
        }
    }
    // The tail itself saw v one round earlier.
    let r = succ(n, src);
    lemma_at_succ(n, o, (tl - 1) as nat);
    assert(at(n, o, (tl - 1) as nat) == src);
    assert(at(n, o, tl) == r);
    lemma_at_period(n, o, (tl - n) as nat);
    lemma_visited_seen(c, s, src, (tl - n) as nat);
}

} // verus!
