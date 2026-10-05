//! Inductive invariant of the two-round protocol. No protocol guard reads any
//! of these predicates.
use vstd::prelude::*;
use super::vc::*;
use super::ring::*;
use super::types::*;
use super::model::*;

verus! {

/// Server o's own counter: the number of writes it has created.
pub open spec fn ctr(s: State, o: int) -> nat { s.servers[o].gvc[o] }

/// No clock mentions a write that its origin has not created yet.
pub open spec fn bounded(s: State, n: nat, x: VC) -> bool {
    &&& x.len() == n
    &&& forall|o: int| 0 <= o < n ==> #[trigger] x[o] <= ctr(s, o)
}

/// Vector-clock knowledge: a clock that has counted a write at o dominates it.
#[verifier::opaque]
pub open spec fn known(s: State, n: nat, x: VC) -> bool {
    forall|o: int| 0 <= o < n && #[trigger] x[o] >= 1 ==>
        exists|v: Version| #[trigger] s.writes.contains(v) && v.origin == o && v.vc[o] == x[o] && le(v.vc, x)
}

pub open spec fn sound(s: State, n: nat, x: VC) -> bool { bounded(s, n, x) && known(s, n, x) }

pub open spec fn map_sound(s: State, n: nat, d: Map<int, VC>) -> bool {
    forall|k: int| #[trigger] d.dom().contains(k) ==> sound(s, n, d[k])
}

pub open spec fn entries_sound(s: State, n: nat, m: Map<int, Entry>) -> bool {
    forall|k: int| #[trigger] m.dom().contains(k) ==> sound(s, n, m[k].vc)
}

/// Every write has a counter at its origin, unique there, and writes from one
/// origin are ordered by that counter.
#[verifier::opaque]
pub open spec fn writes_ok(c: Constants, s: State) -> bool {
    &&& forall|v: Version| #[trigger] s.writes.contains(v) ==> {
        &&& server(c.n, v.origin)
        &&& sound(s, c.n, v.vc)
        &&& v.vc[v.origin] >= 1
        &&& map_sound(s, c.n, v.deps)
        &&& forall|k: int| #[trigger] v.deps.dom().contains(k) ==> le(v.deps[k], v.vc)
    }
    &&& forall|v: Version, w: Version| #![trigger s.writes.contains(v), s.writes.contains(w)]
        s.writes.contains(v) && s.writes.contains(w) && v.origin == w.origin
        && v.vc[v.origin] <= w.vc[w.origin] ==> le(v.vc, w.vc)
    &&& forall|v: Version, w: Version| #![trigger s.writes.contains(v), s.writes.contains(w)]
        s.writes.contains(v) && s.writes.contains(w) && v.origin == w.origin
        && v.vc[v.origin] == w.vc[w.origin] ==> v == w
}

#[verifier::opaque]
pub open spec fn clocks_ok(c: Constants, s: State) -> bool {
    &&& forall|o: int| #![trigger s.servers[o]] server(c.n, o) ==> {
        &&& sound(s, c.n, s.servers[o].gvc)
        &&& entries_sound(s, c.n, s.servers[o].ccache)
    }
    &&& forall|cid: int| #[trigger] s.clients.dom().contains(cid) ==> {
        &&& map_sound(s, c.n, s.clients[cid].deps)
        &&& entries_sound(s, c.n, s.clients[cid].local)
    }
    &&& forall|i: int| #![trigger s.history[i]] 0 <= i < s.history.len() && s.history[i] is Read ==> {
        &&& sound(s, c.n, s.history[i]->Read_server_vc)
        &&& sound(s, c.n, s.history[i]->Read_vc)
    }
}

pub open spec fn shape_ok(c: Constants, s: State) -> bool {
    &&& valid_constants(c) && c.rounds >= 2
    &&& s.servers.len() == c.n && s.chans.len() == c.n
    &&& s.seen.len() == c.n && s.sent.len() == c.n
    &&& s.clients.dom() == s.ctx.dom()
}

/// Every write at every clock-counter up to `x[o]` has reached all servers.
#[verifier::opaque]
pub open spec fn avail(c: Constants, s: State, x: VC) -> bool {
    forall|v: Version, q: int| #![trigger s.writes.contains(v), s.seen[q].contains(v)]
        s.writes.contains(v) && v.vc[v.origin] <= x[v.origin] && server(c.n, q)
        ==> s.seen[q].contains(v)
}

/// Seen versions are stored, or already dominated in C-cache.
#[verifier::opaque]
pub open spec fn seen_ok(c: Constants, s: State) -> bool {
    forall|q: int| #![trigger s.seen[q]] server(c.n, q) ==> {
        &&& s.seen[q].subset_of(s.writes)
        &&& s.servers[q].icache.subset_of(s.seen[q])
        &&& forall|v: Version| #[trigger] s.seen[q].contains(v) ==>
            s.servers[q].icache.contains(v) || le(v.vc, entry(s.servers[q], c.n, v.key).vc)
        &&& forall|v: Version| #[trigger] s.writes.contains(v) && v.origin == q ==> s.seen[q].contains(v)
    }
}

/// C-cache entries and client dependencies only mention available writes.
#[verifier::opaque]
pub open spec fn avail_ok(c: Constants, s: State) -> bool {
    &&& forall|q: int, k: int| #![trigger s.servers[q].ccache.dom().contains(k)]
        server(c.n, q) && s.servers[q].ccache.dom().contains(k)
        ==> avail(c, s, s.servers[q].ccache[k].vc)
    &&& forall|cid: int, k: int| #![trigger s.clients[cid].deps.dom().contains(k)]
        s.clients.dom().contains(cid) && s.clients[cid].deps.dom().contains(k)
        ==> avail(c, s, s.clients[cid].deps[k])
}

/// Definition 1, strict causal cut, for the versions C-cache holds: a write
/// that C-cache covers and that is no longer pending in I-cache has every
/// version matching its dependencies covered and not pending. A dependency
/// (k, vc) is met by every version of k at or below vc.
#[verifier::opaque]
pub open spec fn cut_srv(n: nat, writes: Set<Version>, sv: Server) -> bool {
    forall|v: Version, k: int, u: Version|
        #![trigger writes.contains(v), v.deps.dom().contains(k), writes.contains(u)]
        writes.contains(v) && le(v.vc, entry(sv, n, v.key).vc) && !sv.icache.contains(v)
        && v.deps.dom().contains(k) && writes.contains(u) && u.key == k && le(u.vc, v.deps[k])
        ==> le(u.vc, entry(sv, n, k).vc) && !sv.icache.contains(u)
}

pub open spec fn cut(c: Constants, s: State, q: int) -> bool {
    cut_srv(c.n, s.writes, s.servers[q])
}

pub open spec fn cut_ok(c: Constants, s: State) -> bool {
    forall|q: int| #[trigger] server(c.n, q) ==> cut(c, s, q)
}

pub open spec fn delivered(s: State, q: int) -> int { s.sent[q].len() - s.chans[q].len() }

/// Channel q's queue is the undelivered suffix of what q has sent, and the
/// receiver has seen every delivered version.
#[verifier::opaque]
pub open spec fn fifo_ok(c: Constants, s: State) -> bool {
    forall|q: int| #![trigger s.chans[q]] server(c.n, q) ==> {
        &&& s.chans[q].len() <= s.sent[q].len()
        &&& forall|i: int| #![trigger s.chans[q][i]] 0 <= i < s.chans[q].len()
            ==> s.chans[q][i] == s.sent[q][i + delivered(s, q)]
        &&& forall|i: int| #![trigger s.sent[q][i]] 0 <= i < delivered(s, q)
            ==> s.seen[succ(c.n, q)].contains(s.sent[q][i].version)
    }
}

/// A message's hop locates its sender on the version's chain.
#[verifier::opaque]
pub open spec fn msg_ok(c: Constants, s: State) -> bool {
    forall|q: int, i: int| #![trigger s.sent[q][i]] server(c.n, q) && 0 <= i < s.sent[q].len() ==> {
        let m = s.sent[q][i];
        &&& s.writes.contains(m.version)
        &&& 1 <= m.hop <= tail_hop(c)
        &&& at(c.n, m.version.origin, (m.hop - 1) as nat) == q
    }
}

/// Every write's first message leaves its origin, and a server forwards every
/// version it has seen.
#[verifier::opaque]
pub open spec fn forward_ok(c: Constants, s: State) -> bool {
    &&& forall|v: Version| #[trigger] s.writes.contains(v) ==>
        exists|i: int| 0 <= i < s.sent[v.origin].len() && #[trigger] s.sent[v.origin][i] == (Msg { version: v, hop: 1 })
    &&& forall|q: int, v: Version| #![trigger s.seen[q].contains(v)] server(c.n, q) && s.seen[q].contains(v) ==>
        exists|i: int| 0 <= i < s.sent[q].len() && #[trigger] s.sent[q][i].version == v
}

/// A message at hop h > 1 follows the delivered message at hop h - 1.
#[verifier::opaque]
pub open spec fn progress_ok(c: Constants, s: State) -> bool {
    forall|q: int, i: int| #![trigger s.sent[q][i]]
        server(c.n, q) && 0 <= i < s.sent[q].len() && s.sent[q][i].hop >= 2 ==>
        exists|p: int, j: int| #![trigger s.sent[p][j]]
            server(c.n, p) && succ(c.n, p) == q && 0 <= j < delivered(s, p)
            && s.sent[p][j] == (Msg { version: s.sent[q][i].version, hop: (s.sent[q][i].hop - 1) as nat })
}

/// Lemma 3's dragging. Take a version w and a message for v. If v visited w's
/// origin within its last n - 1 hops and v's clock counts w, then a message for
/// w precedes v's message on the same channel.
#[verifier::opaque]
pub open spec fn drag_ok(c: Constants, s: State) -> bool {
    forall|q: int, i: int, w: Version, j: nat|
        #![trigger s.sent[q][i], s.writes.contains(w), at(c.n, s.sent[q][i].version.origin, j)]
        server(c.n, q) && 0 <= i < s.sent[q].len() && s.writes.contains(w)
        && j < s.sent[q][i].hop && s.sent[q][i].hop < j + c.n
        && at(c.n, s.sent[q][i].version.origin, j) == w.origin
        && w != s.sent[q][i].version && w.vc[w.origin] <= s.sent[q][i].version.vc[w.origin]
        ==> exists|i2: int| 0 <= i2 < i && #[trigger] s.sent[q][i2].version == w
}

/// A client's causal past is its own writes or reachable from its deps.
#[verifier::opaque]
pub open spec fn client_ok(c: Constants, s: State) -> bool {
    forall|cid: int| #[trigger] s.clients.dom().contains(cid) ==> {
        let cl = s.clients[cid];
        &&& s.ctx[cid].subset_of(s.writes)
        &&& forall|w: Version| #[trigger] s.ctx[cid].contains(w) ==>
            le(w.vc, local_entry(cl, c.n, w.key).vc) || reached(s.writes, cl.deps).contains(w)
        &&& forall|k: int| #[trigger] cl.local.dom().contains(k) ==>
            exists|w: Version| #[trigger] s.ctx[cid].contains(w) && w.key == k
                && w.vc == cl.local[k].vc && w.value == cl.local[k].value
    }
}

/// Each positive C-cache clock entry is attained by a dominated write of that
/// key, and the value is a written one.
#[verifier::opaque]
pub open spec fn cache_ok(c: Constants, s: State) -> bool {
    forall|q: int, k: int| #![trigger s.servers[q].ccache.dom().contains(k)]
        server(c.n, q) && s.servers[q].ccache.dom().contains(k) ==> {
        let e = s.servers[q].ccache[k];
        &&& forall|o: int| 0 <= o < c.n && #[trigger] e.vc[o] >= 1 ==>
            exists|w: Version| #[trigger] s.writes.contains(w) && w.key == k && le(w.vc, e.vc) && w.vc[o] == e.vc[o]
        &&& exists|w: Version| #[trigger] s.writes.contains(w) && w.key == k && le(w.vc, e.vc) && w.value == e.value
    }
}

pub open spec fn ev_ctx(e: Event) -> Set<Version> {
    match e {
        Event::Write { ctx, .. } => ctx,
        Event::Read { ctx, .. } => ctx,
        Event::Fork { ctx, .. } => ctx,
    }
}

/// One history event's facts.
pub open spec fn event_ok(c: Constants, s: State, i: int) -> bool {
    let h = s.history;
    &&& ev_ctx(h[i]).subset_of(s.writes)
    &&& s.clients.dom().contains(super::properties::actor(h[i]))
    &&& ev_ctx(h[i]).subset_of(s.ctx[super::properties::actor(h[i])])
    &&& h[i] is Fork ==> s.clients.dom().contains(h[i]->Fork_child)
        && ev_ctx(h[i]).subset_of(s.ctx[h[i]->Fork_child])
    &&& h[i] is Write ==> {
        let v = h[i]->Write_version;
        &&& ev_ctx(h[i]).contains(v)
        &&& forall|w: Version| #[trigger] ev_ctx(h[i]).contains(w) ==>
            w == v || reached(s.writes, v.deps).contains(w)
    }
    &&& h[i] is Read ==> read_ok(c, h[i])
}

/// A read reflects its context, and its clocks and value come from it.
pub open spec fn read_ok(c: Constants, e: Event) -> bool {
    let k = e->Read_key;
    let vc = e->Read_vc;
    let svc = e->Read_server_vc;
    &&& le(svc, vc)
    &&& forall|w: Version| #[trigger] ev_ctx(e).contains(w) && w.key == k ==> le(w.vc, vc)
    &&& forall|o: int| 0 <= o < c.n && #[trigger] vc[o] >= 1 ==>
        exists|w: Version| #[trigger] ev_ctx(e).contains(w) && w.key == k && w.vc[o] == vc[o]
    &&& forall|o: int| 0 <= o < c.n && #[trigger] svc[o] >= 1 ==>
        exists|w: Version| #[trigger] ev_ctx(e).contains(w) && w.key == k && w.vc[o] == svc[o]
    &&& (vc == zero(c.n) && e->Read_value == 0) || exists|w: Version|
        #[trigger] ev_ctx(e).contains(w) && w.key == k && le(w.vc, vc) && w.value == e->Read_value
}

/// History invariants that carry the client-level theorems.
#[verifier::opaque]
pub open spec fn events_ok(c: Constants, s: State) -> bool {
    let h = s.history;
    &&& forall|i: int| #![trigger h[i]] 0 <= i < h.len() ==> event_ok(c, s, i)
    &&& forall|v: Version| #[trigger] s.writes.contains(v) ==> exists|i: int|
        0 <= i < h.len() && #[trigger] h[i] is Write && h[i]->Write_version == v
    &&& forall|i: int, j: int| #![trigger super::properties::edge(h, i, j)]
        super::properties::edge(h, i, j) ==> ev_ctx(h[i]).subset_of(ev_ctx(h[j]))
}

pub proof fn lemma_event(c: Constants, s: State, i: int)
    requires events_ok(c, s), 0 <= i < s.history.len()
    ensures event_ok(c, s, i)
{
    reveal(events_ok);
}

/// Every write has its own event, whose context contains it.
pub proof fn lemma_write_event(c: Constants, s: State, w: Version) -> (i: int)
    requires events_ok(c, s), s.writes.contains(w)
    ensures 0 <= i < s.history.len(), s.history[i] is Write, s.history[i]->Write_version == w,
        ev_ctx(s.history[i]).contains(w), ev_ctx(s.history[i]).subset_of(s.writes),
{
    reveal(events_ok);
    let i = choose|i: int| 0 <= i < s.history.len() && #[trigger] s.history[i] is Write && s.history[i]->Write_version == w;
    assert(event_ok(c, s, i));
    i
}

pub proof fn lemma_edge_ctx(c: Constants, s: State, i: int, j: int)
    requires events_ok(c, s), super::properties::edge(s.history, i, j)
    ensures ev_ctx(s.history[i]).subset_of(ev_ctx(s.history[j]))
{
    reveal(events_ok);
}

pub open spec fn inv(c: Constants, s: State) -> bool {
    &&& shape_ok(c, s)
    &&& writes_ok(c, s)
    &&& clocks_ok(c, s)
    &&& fifo_ok(c, s)
    &&& msg_ok(c, s)
    &&& forward_ok(c, s)
    &&& progress_ok(c, s)
    &&& drag_ok(c, s)
    &&& seen_ok(c, s)
    &&& avail_ok(c, s)
    &&& cut_ok(c, s)
    &&& client_ok(c, s)
    &&& cache_ok(c, s)
    &&& events_ok(c, s)
}

} // verus!
