//! CausalMesh transitions, following arXiv 2508.15647v2 Figures 4, 6 and 7.
//! Server actions are atomic (Fact 1). Chains are FIFO queues (Fact 2).
//! Client requests are processed atomically with their replies.
use vstd::prelude::*;
use super::vc::*;
use super::ring::*;
use super::types::*;

verus! {

/// `r` is an upper bound of `base` and `parts` whose every entry is taken from
/// one of them. The exact join is one such bound.
pub open spec fn lub_of(n: nat, base: VC, parts: spec_fn(VC) -> bool, r: VC) -> bool {
    &&& r.len() == n
    &&& le(base, r)
    &&& forall|p: VC| #[trigger] parts(p) ==> le(p, r)
    &&& forall|i: int| 0 <= i < n ==> (#[trigger] r[i] == base[i]
        || exists|p: VC| #[trigger] parts(p) && p[i] == r[i])
}

/// A version satisfies a dependency map entry for its key.
pub open spec fn matches(d: Map<int, VC>, v: Version) -> bool {
    d.dom().contains(v.key) && le(v.vc, d[v.key])
}

/// A dependency chain through I-cache entries, starting from `d` (Figure 7,
/// "all transitive predecessors of deps"). A dependency (k, vc) is met by
/// every version of k with a clock at most vc (§4.7).
#[verifier::opaque]
pub open spec fn chain(ic: Set<Version>, d: Map<int, VC>, path: Seq<Version>) -> bool {
    &&& path.len() > 0
    &&& matches(d, path[0])
    &&& forall|t: int| 0 <= t < path.len() ==> ic.contains(#[trigger] path[t])
    &&& forall|t: int, u: int| #![trigger path[t], path[u]]
        0 <= t && u == t + 1 && u < path.len() ==> matches(path[t].deps, path[u])
}

pub proof fn lemma_singleton_chain(ic: Set<Version>, d: Map<int, VC>, v: Version)
    requires ic.contains(v), matches(d, v)
    ensures chain(ic, d, seq![v]), reached(ic, d).contains(v)
{
    reveal(chain);
    let path = seq![v];
    assert(chain(ic, d, path) && path.last() == v);
    assert(exists|path: Seq<Version>| #[trigger] chain(ic, d, path) && path.last() == v);
    assert(reached(ic, d).contains(v));
}

pub proof fn lemma_chain_ends(ic: Set<Version>, d: Map<int, VC>, path: Seq<Version>)
    requires chain(ic, d, path)
    ensures path.len() > 0, ic.contains(path[0]), matches(d, path[0]), ic.contains(path.last())
{
    reveal(chain);
}

pub open spec fn reached(ic: Set<Version>, d: Map<int, VC>) -> Set<Version> {
    ic.filter(|v: Version| exists|path: Seq<Version>| #[trigger] chain(ic, d, path) && path.last() == v)
}

pub open spec fn key_vcs(m: Set<Version>, k: int) -> spec_fn(VC) -> bool {
    |x: VC| exists|v: Version| #[trigger] m.contains(v) && v.key == k && v.vc == x
}

pub open spec fn dep_or_version_vcs(d: Map<int, VC>, m: Set<Version>) -> spec_fn(VC) -> bool {
    |x: VC| (exists|k: int| #[trigger] d.dom().contains(k) && d[k] == x)
        || exists|v: Version| #[trigger] m.contains(v) && v.vc == x
}

pub open spec fn dep_vcs(d: Map<int, VC>) -> spec_fn(VC) -> bool {
    |x: VC| exists|k: int| #[trigger] d.dom().contains(k) && d[k] == x
}

pub open spec fn has_value(m: Set<Version>, k: int, value: int) -> bool {
    exists|v: Version| #[trigger] m.contains(v) && v.key == k && v.value == value
}

/// Figure 7: remove the reached versions from I-cache, merge them into
/// C-cache, and merge every clock involved into the server clock.
pub open spec fn integrated(n: nat, s: Server, d: Map<int, VC>, t: Server) -> bool {
    let m = reached(s.icache, d);
    &&& t.icache == s.icache.difference(m)
    &&& forall|k: int| #[trigger] t.ccache.dom().contains(k) <==>
        (s.ccache.dom().contains(k) || exists|v: Version| #[trigger] m.contains(v) && v.key == k)
    &&& forall|k: int| #![trigger t.ccache.dom().contains(k)] t.ccache.dom().contains(k) ==> {
        let old = entry(s, n, k);
        let e = t.ccache[k];
        &&& lub_of(n, old.vc, key_vcs(m, k), e.vc)
        &&& (s.ccache.dom().contains(k) && e.value == old.value) || has_value(m, k, e.value)
    }
    &&& lub_of(n, s.gvc, dep_or_version_vcs(d, m), t.gvc)
}

pub open spec fn has_seen(n: nat, s: Server, v: Version) -> bool {
    s.icache.contains(v) || le(v.vc, entry(s, n, v.key).vc)
}

pub open spec fn tail_hop(c: Constants) -> nat { (c.rounds * c.n - 1) as nat }

/// The client's deps with its own writes merged in (Figure 6, lines 8-10).
pub open spec fn write_deps(n: nat, cl: Client) -> Map<int, VC> {
    Map::new(cl.deps.dom().union(cl.local.dom()),
        |k: int| join(dep(cl.deps, n, k), local_entry(cl, n, k).vc))
}

pub open spec fn new_version(c: Constants, s: State, cid: int, srv: int,
                             key: int, value: int, gvc: VC) -> Version {
    Version { key, value, vc: tick(gvc, srv), deps: write_deps(c.n, s.clients[cid]), origin: srv }
}

pub open spec fn write_post(c: Constants, s: State, cid: int, srv: int,
                            key: int, value: int, gvc: VC) -> State {
    let cl = s.clients[cid];
    let sv = s.servers[srv];
    let v = new_version(c, s, cid, srv, key, value, gvc);
    let out = Msg { version: v, hop: 1 };
    let ctx = s.ctx[cid].insert(v);
    State {
        servers: s.servers.update(srv, Server { gvc: v.vc, icache: sv.icache.insert(v), ..sv }),
        chans: s.chans.update(srv, s.chans[srv].push(out)),
        clients: s.clients.insert(cid, Client { local: cl.local.insert(key, Entry { value, vc: v.vc }), ..cl }),
        writes: s.writes.insert(v),
        seen: s.seen.update(srv, s.seen[srv].insert(v)),
        sent: s.sent.update(srv, s.sent[srv].push(out)),
        ctx: s.ctx.insert(cid, ctx),
        history: s.history.push(Event::Write { client: cid, version: v, ctx }),
    }
}

/// Figure 6, ClientWrite: merge deps and local into the clock, then tick.
pub open spec fn client_write(c: Constants, s: State, s2: State, cid: int, srv: int,
                              key: int, value: int, gvc: VC) -> bool {
    &&& server(c.n, srv) && s.clients.dom().contains(cid)
    &&& lub_of(c.n, s.servers[srv].gvc, dep_vcs(write_deps(c.n, s.clients[cid])), gvc)
    &&& s2 == write_post(c, s, cid, srv, key, value, gvc)
}

/// The receiver's state after storing a propagated version it has not seen.
pub open spec fn stored(c: Constants, s: State, src: int) -> Server {
    let v = s.chans[src][0].version;
    let sv = s.servers[succ(c.n, src)];
    if has_seen(c.n, sv, v) { sv } else { Server { icache: sv.icache.insert(v), ..sv } }
}

pub open spec fn is_tail(c: Constants, s: State, src: int) -> bool {
    s.chans[src][0].hop == tail_hop(c)
}

pub open spec fn propagate_post(c: Constants, s: State, src: int, t: Server) -> State {
    let m = s.chans[src][0];
    let v = m.version;
    let r = succ(c.n, src);
    let chans = s.chans.update(src, s.chans[src].drop_first());
    let out = Msg { version: v, hop: m.hop + 1 };
    if is_tail(c, s, src) {
        State { servers: s.servers.update(r, t), chans, seen: s.seen.update(r, s.seen[r].insert(v)), ..s }
    } else {
        State {
            servers: s.servers.update(r, t),
            chans: chans.update(r, chans[r].push(out)),
            seen: s.seen.update(r, s.seen[r].insert(v)),
            sent: s.sent.update(r, s.sent[r].push(out)),
            ..s
        }
    }
}

pub open spec fn one_vc(x: VC) -> spec_fn(VC) -> bool { |y: VC| y == x }

/// Figure 6, lines 27 and 29: merge the arriving version into the server
/// clock and into C-cache. I-cache is unchanged, so a copy stored in round one
/// stays there.
pub open spec fn merged(n: nat, s: Server, v: Version, t: Server) -> bool {
    let old = entry(s, n, v.key);
    let e = t.ccache[v.key];
    &&& t.icache == s.icache
    &&& t.ccache == s.ccache.insert(v.key, e)
    &&& lub_of(n, old.vc, one_vc(v.vc), e.vc)
    &&& (s.ccache.dom().contains(v.key) && e.value == old.value) || e.value == v.value
    &&& lub_of(n, s.gvc, one_vc(v.vc), t.gvc)
}

/// Figure 6, ServerWrite: store and forward, or at the tail integrate the
/// version's dependencies (line 28), giving `mid`, and merge the version
/// itself (lines 27, 29).
pub open spec fn propagate(c: Constants, s: State, s2: State, src: int, mid: Server, t: Server) -> bool {
    let v = s.chans[src][0].version;
    &&& server(c.n, src) && s.chans[src].len() > 0
    &&& if is_tail(c, s, src) {
        &&& integrated(c.n, s.servers[succ(c.n, src)], v.deps, mid)
        &&& merged(c.n, mid, v, t)
    } else {
        t == stored(c, s, src)
    }
    &&& s2 == propagate_post(c, s, src, t)
}

/// Writes whose effects a read observes: those it returns and their contexts.
pub open spec fn observed(s: State, key: int, svc: VC) -> Set<Version> {
    s.writes.filter(|w: Version| exists|i: int| #![trigger s.history[i]] 0 <= i < s.history.len() && {
        let e = s.history[i];
        &&& e is Write
        &&& e->Write_version.key == key && le(e->Write_version.vc, svc)
        &&& e->Write_ctx.contains(w)
    })
}

/// Figure 4 read: the client merges the server reply with its own write. The
/// newer version's value wins; for concurrent versions either may be chosen.
pub open spec fn returned(n: nat, cl: Client, key: int, e: Entry, r: Entry) -> bool {
    if cl.local.dom().contains(key) {
        let l = cl.local[key];
        &&& r.vc == join(l.vc, e.vc)
        &&& if le(e.vc, l.vc) { r.value == l.value }
            else if le(l.vc, e.vc) { r.value == e.value }
            else { r.value == l.value || r.value == e.value }
    } else {
        r == e
    }
}

pub open spec fn read_post(c: Constants, s: State, cid: int, srv: int, key: int,
                           t: Server, r: Entry) -> State {
    let cl = s.clients[cid];
    let e = entry(t, c.n, key);
    let ctx = s.ctx[cid].union(observed(s, key, e.vc));
    State {
        servers: s.servers.update(srv, t),
        clients: s.clients.insert(cid,
            Client { deps: cl.deps.insert(key, join(dep(cl.deps, c.n, key), e.vc)), ..cl }),
        ctx: s.ctx.insert(cid, ctx),
        history: s.history.push(Event::Read { client: cid, key, server_vc: e.vc, vc: r.vc,
            value: r.value, ctx }),
        ..s
    }
}

/// Figure 6, ClientRead: integrate the client's deps, then read C-cache.
pub open spec fn client_read(c: Constants, s: State, s2: State, cid: int, srv: int,
                             key: int, t: Server, r: Entry) -> bool {
    &&& server(c.n, srv) && s.clients.dom().contains(cid)
    &&& integrated(c.n, s.servers[srv], s.clients[cid].deps, t)
    &&& returned(c.n, s.clients[cid], key, entry(t, c.n, key), r)
    &&& s2 == read_post(c, s, cid, srv, key, t, r)
}

/// A new workflow starts with empty deps and local.
pub open spec fn start_client(s: State, s2: State, cid: int) -> bool {
    &&& !s.clients.dom().contains(cid)
    &&& s2 == State {
        clients: s.clients.insert(cid, empty_client()),
        ctx: s.ctx.insert(cid, Set::empty()),
        ..s
    }
}

/// Fan-out: a function inherits its predecessor's deps and local (§4.2).
pub open spec fn fork(s: State, s2: State, parent: int, child: int) -> bool {
    &&& s.clients.dom().contains(parent) && !s.clients.dom().contains(child)
    &&& s2 == State {
        clients: s.clients.insert(child, s.clients[parent]),
        ctx: s.ctx.insert(child, s.ctx[parent]),
        history: s.history.push(Event::Fork { parent, child, ctx: s.ctx[parent] }),
        ..s
    }
}

pub open spec fn init(c: Constants, s: State) -> bool {
    &&& valid_constants(c)
    &&& s.servers == Seq::new(c.n, |i: int| empty_server(c.n))
    &&& s.chans == Seq::new(c.n, |i: int| Seq::<Msg>::empty())
    &&& s.clients == Map::<int, Client>::empty()
    &&& s.writes == Set::<Version>::empty()
    &&& s.seen == Seq::new(c.n, |i: int| Set::<Version>::empty())
    &&& s.sent == Seq::new(c.n, |i: int| Seq::<Msg>::empty())
    &&& s.ctx == Map::<int, Set<Version>>::empty()
    &&& s.history == Seq::<Event>::empty()
}

} // verus!
