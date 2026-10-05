//! Concrete reachable executions on two servers. With two rounds, a migrating
//! reader finds a completed write again after moving; with one round, a
//! version is exposed at its tail before it reaches the other server.
use vstd::prelude::*;
use super::vc::*;
use super::ring::*;
use super::types::*;
use super::model::*;
use super::behavior::*;
use super::properties::*;

verus! {

pub open spec fn vc2(a: nat, b: nat) -> VC { seq![a, b] }
pub open spec fn key_x() -> int { 1 }
pub open spec fn key_z() -> int { 2 }

pub open spec fn start_state(s: State, cid: int) -> State {
    State { clients: s.clients.insert(cid, empty_client()), ctx: s.ctx.insert(cid, Set::empty()), ..s }
}

pub open spec fn init_state(n: nat) -> State {
    State {
        servers: Seq::new(n, |i: int| empty_server(n)),
        chans: Seq::new(n, |i: int| Seq::<Msg>::empty()),
        clients: Map::<int, Client>::empty(),
        writes: Set::<Version>::empty(),
        seen: Seq::new(n, |i: int| Set::<Version>::empty()),
        sent: Seq::new(n, |i: int| Seq::<Msg>::empty()),
        ctx: Map::<int, Set<Version>>::empty(),
        history: Seq::<Event>::empty(),
    }
}

/// Two fresh clients, 0 and 1, on an idle system.
pub proof fn lemma_two_clients(c: Constants) -> (t: Seq<State>)
    requires valid_constants(c), c.n == 2
    ensures behavior(c, t), t.last() == start_state(start_state(init_state(2), 0), 1)
{
    reveal(behavior);
    let s0 = init_state(2);
    assert(init(c, s0));
    let t = seq![s0];
    assert(behavior(c, t)) by {
        assert forall|i: int| 0 <= i < t.len() - 1 implies #[trigger] next(c, t[i], t[i + 1]) by {}
    }
    reveal(step);
    let t = lemma_extend(c, t, start_state(s0, 0), Action::Start { client: 0 });
    let t = lemma_extend(c, t, start_state(start_state(s0, 0), 1), Action::Start { client: 1 });
    t
}

pub proof fn lemma_vcs()
    ensures
        zero(2) == vc2(0, 0),
        tick(vc2(0, 0), 0) == vc2(1, 0),
        tick(vc2(1, 0), 1) == vc2(1, 1),
        join(vc2(0, 0), vc2(1, 0)) == vc2(1, 0),
        le(vc2(1, 0), vc2(1, 0)), le(vc2(1, 0), vc2(1, 1)), le(vc2(1, 1), vc2(1, 1)),
        !le(vc2(1, 0), vc2(0, 0)), !le(vc2(1, 1), vc2(0, 0)),
{
    assert(zero(2) =~= vc2(0, 0));
    assert(tick(vc2(0, 0), 0) =~= vc2(1, 0));
    assert(tick(vc2(1, 0), 1) =~= vc2(1, 1));
    assert(join(vc2(0, 0), vc2(1, 0)) =~= vc2(1, 0));
    assert(!le(vc2(1, 0), vc2(0, 0))) by { assert(vc2(1, 0)[0] > vc2(0, 0)[0]); }
    assert(!le(vc2(1, 1), vc2(0, 0))) by { assert(vc2(1, 1)[0] > vc2(0, 0)[0]); }
}

pub open spec fn x1() -> Version {
    Version { key: key_x(), value: 10, vc: vc2(1, 0), deps: Map::empty(), origin: 0 }
}

/// Client 0 writes x = 10 at server 0.
pub proof fn lemma_write_x(c: Constants, t: Seq<State>) -> (after: Seq<State>)
    requires valid_constants(c), c.n == 2, behavior(c, t),
        t.last() == start_state(start_state(init_state(2), 0), 1),
    ensures behavior(c, after), after.last() == write_post(c, t.last(), 0, 0, key_x(), 10, vc2(0, 0)),
        new_version(c, t.last(), 0, 0, key_x(), 10, vc2(0, 0)) == x1(),
{
    let s = t.last();
    lemma_vcs();
    assert(s.clients[0] == empty_client());
    assert(write_deps(2, empty_client()) =~= Map::<int, VC>::empty());
    assert(s.servers[0] == empty_server(2));
    assert(lub_of(2, s.servers[0].gvc, dep_vcs(write_deps(2, s.clients[0])), vc2(0, 0)));
    assert(new_version(c, s, 0, 0, key_x(), 10, vc2(0, 0)) == x1());
    reveal(step);
    lemma_extend(c, t, write_post(c, s, 0, 0, key_x(), 10, vc2(0, 0)),
        Action::Write { client: 0, server: 0, key: key_x(), value: 10, gvc: vc2(0, 0) })
}

pub open spec fn z1() -> Version {
    Version { key: key_z(), value: 20, vc: vc2(1, 1), deps: map![key_x() => vc2(1, 0)], origin: 1 }
}

/// Client 0 migrates to server 1 and writes z = 20, carrying x in `local`.
pub proof fn lemma_write_z(c: Constants, t: Seq<State>) -> (after: Seq<State>)
    requires valid_constants(c), c.n == 2, behavior(c, t),
        t.last() == write_post(c, start_state(start_state(init_state(2), 0), 1), 0, 0, key_x(), 10, vc2(0, 0)),
    ensures behavior(c, after), after.last() == write_post(c, t.last(), 0, 1, key_z(), 20, vc2(1, 0)),
        new_version(c, t.last(), 0, 1, key_z(), 20, vc2(1, 0)) == z1(),
{
    let s = t.last();
    lemma_vcs();
    let cl = s.clients[0];
    assert(cl.local =~= map![key_x() => Entry { value: 10, vc: vc2(1, 0) }]);
    assert(cl.deps =~= Map::<int, VC>::empty());
    let d = write_deps(2, cl);
    assert(d.dom() =~= set![key_x()]);
    assert(d[key_x()] == join(zero(2), vc2(1, 0)));
    assert(d =~= map![key_x() => vc2(1, 0)]);
    assert(s.servers[1] == empty_server(2));
    let parts = dep_vcs(d);
    assert(parts(vc2(1, 0))) by { assert(d.dom().contains(key_x()) && d[key_x()] == vc2(1, 0)); }
    assert(forall|p: VC| #[trigger] parts(p) ==> p == vc2(1, 0));
    assert(lub_of(2, s.servers[1].gvc, parts, vc2(1, 0)));
    assert(new_version(c, s, 0, 1, key_z(), 20, vc2(1, 0)) == z1());
    reveal(step);
    lemma_extend(c, t, write_post(c, s, 0, 1, key_z(), 20, vc2(1, 0)),
        Action::Write { client: 0, server: 1, key: key_z(), value: 20, gvc: vc2(1, 0) })
}

pub open spec fn after_z(c: Constants) -> State {
    write_post(c, write_post(c, start_state(start_state(init_state(2), 0), 1), 0, 0, key_x(), 10, vc2(0, 0)),
        0, 1, key_z(), 20, vc2(1, 0))
}

pub open spec fn exposed() -> Server {
    Server {
        gvc: vc2(1, 1),
        icache: Set::empty(),
        ccache: map![key_x() => Entry { value: 10, vc: vc2(1, 0) }, key_z() => Entry { value: 20, vc: vc2(1, 1) }],
    }
}

/// Facts about the state after both writes, shared by both executions.
pub proof fn lemma_after_z(c: Constants)
    requires c.n == 2
    ensures
        after_z(c).servers[0] == (Server { gvc: vc2(1, 0), icache: set![x1()], ccache: Map::empty() }),
        after_z(c).servers[1] == (Server { gvc: vc2(1, 1), icache: set![z1()], ccache: Map::empty() }),
        after_z(c).chans[0] == seq![Msg { version: x1(), hop: 1 }],
        after_z(c).chans[1] == seq![Msg { version: z1(), hop: 1 }],
        after_z(c).clients[1] == empty_client(),
        after_z(c).servers.len() == 2, after_z(c).chans.len() == 2,
{
    let s2 = start_state(start_state(init_state(2), 0), 1);
    lemma_vcs();
    assert(s2.clients[0] == empty_client());
    assert(write_deps(2, empty_client()) =~= Map::<int, VC>::empty());
    assert(new_version(c, s2, 0, 0, key_x(), 10, vc2(0, 0)) == x1());
    let s3 = write_post(c, s2, 0, 0, key_x(), 10, vc2(0, 0));
    let cl = s3.clients[0];
    assert(cl.local =~= map![key_x() => Entry { value: 10, vc: vc2(1, 0) }]);
    assert(cl.deps =~= Map::<int, VC>::empty());
    let d = write_deps(2, cl);
    assert(d.dom() =~= set![key_x()]);
    assert(d[key_x()] == join(zero(2), vc2(1, 0)));
    assert(d =~= map![key_x() => vc2(1, 0)]);
    assert(new_version(c, s3, 0, 1, key_z(), 20, vc2(1, 0)) == z1());
    assert(Set::<Version>::empty().insert(x1()) =~= set![x1()]);
    assert(Set::<Version>::empty().insert(z1()) =~= set![z1()]);
    assert(Seq::<Msg>::empty().push(Msg { version: x1(), hop: 1 }) =~= seq![Msg { version: x1(), hop: 1 }]);
    assert(Seq::<Msg>::empty().push(Msg { version: z1(), hop: 1 }) =~= seq![Msg { version: z1(), hop: 1 }]);
    assert(after_z(c).servers[0] =~= (Server { gvc: vc2(1, 0), icache: set![x1()], ccache: Map::empty() }));
}

/// With no dependencies, integration reaches nothing.
pub proof fn lemma_reach_nothing(ic: Set<Version>)
    ensures reached(ic, Map::<int, VC>::empty()) =~= Set::<Version>::empty()
{
    let d = Map::<int, VC>::empty();
    assert forall|v: Version| #[trigger] reached(ic, d).contains(v) implies false by {
        let path = choose|path: Seq<Version>| #[trigger] chain(ic, d, path) && path.last() == v;
        lemma_chain_ends(ic, d, path);
    }
}

/// Server 0 as z's single-round tail: integrating z's deps moves x into
/// C-cache (giving `visible()`), and z is then merged (Figure 6, lines 27-29).
pub proof fn lemma_tail_integration(c: Constants)
    requires c == (Constants { n: 2, rounds: 1 })
    ensures
        is_tail(c, after_z(c), 1),
        integrated(2, after_z(c).servers[0], z1().deps, visible()),
        merged(2, visible(), z1(), exposed()),
{
    let s = after_z(c);
    lemma_after_z(c);
    lemma_vcs();
    assert(succ(2, 1) == 0);
    assert(tail_hop(c) == 1);
    let sv = s.servers[0];
    let d = z1().deps;
    let m = reached(sv.icache, d);
    lemma_singleton_chain(sv.icache, d, x1());
    assert(m =~= set![x1()]);
    let e = visible();
    assert(e.icache =~= sv.icache.difference(m));
    assert forall|k: int| #[trigger] e.ccache.dom().contains(k) <==>
        (sv.ccache.dom().contains(k) || exists|v: Version| #[trigger] m.contains(v) && v.key == k) by {
        if k == key_x() { assert(m.contains(x1())); }
    }
    assert(lub_of(2, entry(sv, 2, key_x()).vc, key_vcs(m, key_x()), vc2(1, 0))) by {
        assert(key_vcs(m, key_x())(vc2(1, 0))) by { assert(m.contains(x1())); }
        assert forall|p: VC| #[trigger] key_vcs(m, key_x())(p) implies p == vc2(1, 0) by {}
    }
    assert(has_value(m, key_x(), 10)) by { assert(m.contains(x1())); }
    assert(lub_of(2, sv.gvc, dep_or_version_vcs(d, m), vc2(1, 0))) by {
        let parts = dep_or_version_vcs(d, m);
        assert forall|p: VC| #[trigger] parts(p) implies p == vc2(1, 0) by {}
    }
    assert(integrated(2, sv, d, visible()));
    assert(exposed().ccache =~= visible().ccache.insert(key_z(), Entry { value: 20, vc: vc2(1, 1) }));
    assert(entry(visible(), 2, key_z()) == initial_entry(2));
    assert(one_vc(vc2(1, 1))(vc2(1, 1)));
    assert(merged(2, visible(), z1(), exposed()));
}

/// With one round, server 0 is z's tail: it integrates z's dependency x and
/// merges z while x's message to server 1 is still in flight.
pub proof fn lemma_single_round_tail(c: Constants, t: Seq<State>) -> (after: Seq<State>)
    requires c == (Constants { n: 2, rounds: 1 }), behavior(c, t), t.last() == after_z(c),
    ensures behavior(c, after), after.last() == propagate_post(c, after_z(c), 1, exposed()),
{
    lemma_after_z(c);
    lemma_tail_integration(c);
    assert(after_z(c).chans[1][0].version == z1());
    assert(propagate(c, after_z(c), propagate_post(c, after_z(c), 1, exposed()), 1, visible(), exposed()));
    reveal(step);
    lemma_extend(c, t, propagate_post(c, after_z(c), 1, exposed()),
        Action::Propagate { src: 1, mid: visible(), after: exposed() })
}

/// A read that integrates nothing: the server is unchanged.
pub proof fn lemma_integrate_nothing(n: nat, sv: Server, d: Map<int, VC>)
    requires reached(sv.icache, d) =~= Set::<Version>::empty(), sv.gvc.len() == n,
        forall|k: int| #[trigger] d.dom().contains(k) ==> le(d[k], sv.gvc),
        forall|k: int| #[trigger] sv.ccache.dom().contains(k) ==> sv.ccache[k].vc.len() == n,
    ensures integrated(n, sv, d, sv)
{
    let m = reached(sv.icache, d);
    assert(sv.icache =~= sv.icache.difference(m));
    assert forall|k: int| #[trigger] sv.ccache.dom().contains(k) implies
        lub_of(n, entry(sv, n, k).vc, key_vcs(m, k), sv.ccache[k].vc) by {
        assert forall|p: VC| #[trigger] key_vcs(m, k)(p) implies le(p, sv.ccache[k].vc) by {}
    }
    assert(lub_of(n, sv.gvc, dep_or_version_vcs(d, m), sv.gvc)) by {
        assert forall|p: VC| #[trigger] dep_or_version_vcs(d, m)(p) implies le(p, sv.gvc) by {}
    }
}

pub open spec fn one_round() -> Constants { Constants { n: 2, rounds: 1 } }

pub open spec fn tail_state() -> State { propagate_post(one_round(), after_z(one_round()), 1, exposed()) }

pub open spec fn first_read() -> State {
    read_post(one_round(), tail_state(), 1, 0, key_x(), exposed(), Entry { value: 10, vc: vc2(1, 0) })
}

pub open spec fn unexposed() -> Server { Server { gvc: vc2(1, 1), icache: set![z1()], ccache: Map::empty() } }

pub open spec fn second_read() -> State {
    read_post(one_round(), first_read(), 1, 1, key_x(), unexposed(), initial_entry(2))
}

/// Client 1 reads x = 10 at server 0, moves to server 1, and reads x again.
pub proof fn lemma_single_round_reads(t: Seq<State>) -> (after: Seq<State>)
    requires behavior(one_round(), t), t.last() == tail_state(),
    ensures behavior(one_round(), after), after.last() == second_read(),
{
    let c = one_round();
    lemma_after_z(c);
    lemma_vcs();
    let s5 = tail_state();
    assert(s5.servers[0] == exposed());
    assert(s5.servers[1] == unexposed());
    assert(s5.clients[1] == empty_client());
    // First read: no deps, so nothing is integrated.
    assert(reached(exposed().icache, Map::<int, VC>::empty()) =~= Set::<Version>::empty());
    lemma_integrate_nothing(2, exposed(), Map::<int, VC>::empty());
    assert(entry(exposed(), 2, key_x()) == (Entry { value: 10, vc: vc2(1, 0) }));
    assert(client_read(c, s5, first_read(), 1, 0, key_x(), exposed(), Entry { value: 10, vc: vc2(1, 0) }));
    reveal(step);
    let t = lemma_extend(c, t, first_read(),
        Action::Read { client: 1, server: 0, key: key_x(), after: exposed(), result: Entry { value: 10, vc: vc2(1, 0) } });
    // Second read at server 1: x's version has not arrived, so the dep matches nothing.
    let s6 = first_read();
    let d = s6.clients[1].deps;
    assert(d =~= map![key_x() => vc2(1, 0)]);
    assert(s6.servers[1] == unexposed());
    assert(reached(unexposed().icache, d) =~= Set::<Version>::empty()) by {
        assert forall|v: Version| #[trigger] reached(unexposed().icache, d).contains(v) implies false by {
            let path = choose|path: Seq<Version>| #[trigger] chain(unexposed().icache, d, path) && path.last() == v;
            lemma_chain_ends(unexposed().icache, d, path);
            assert(path[0] == z1());
        }
    }
    assert(le(vc2(1, 0), vc2(1, 1)));
    lemma_integrate_nothing(2, unexposed(), d);
    assert(entry(unexposed(), 2, key_x()) == initial_entry(2));
    assert(client_read(c, s6, second_read(), 1, 1, key_x(), unexposed(), initial_entry(2)));
    lemma_extend(c, t, second_read(),
        Action::Read { client: 1, server: 1, key: key_x(), after: unexposed(), result: initial_entry(2) })
}

/// With single-round propagation, as in the VLDB version, a client observes
/// x = 10 at one server and then misses it at another.
pub proof fn theorem_single_round_violates_causality() -> (t: Seq<State>)
    ensures
        behavior(one_round(), t),
        !causal_visibility(t.last().history),
        !monotonic_reads(t.last().history),
{
    let c = one_round();
    let t = lemma_two_clients(c);
    let t = lemma_write_x(c, t);
    let t = lemma_write_z(c, t);
    assert(t.last() == after_z(c));
    let t = lemma_single_round_tail(c, t);
    let t = lemma_single_round_reads(t);
    lemma_vcs();
    let h = second_read().history;
    assert(h.len() == 4);
    assert(h[0] is Write && h[0]->Write_version == x1());
    assert(h[2] is Read && h[2]->Read_key == key_x() && h[2]->Read_server_vc == vc2(1, 0)
        && h[2]->Read_vc == vc2(1, 0) && actor(h[2]) == 1);
    assert(h[3] is Read && h[3]->Read_key == key_x() && h[3]->Read_vc == zero(2) && actor(h[3]) == 1);
    let p = seq![0int, 2int, 3int];
    assert(hb_path(h, p)) by {
        assert(edge(h, 0, 2)) by { assert(observes(h, 0, 2)); }
        assert(edge(h, 2, 3)) by { assert(session_edge(h, 2, 3)); }
    }
    assert(hb(h, 0, 3)) by { assert(p[0] == 0 && p.last() == 3); }
    assert(!le(h[0]->Write_version.vc, h[3]->Read_vc));
    assert(!le(h[2]->Read_vc, h[3]->Read_vc));
    t
}

pub open spec fn two_rounds() -> Constants { Constants { n: 2, rounds: 2 } }

pub open spec fn after_x() -> State {
    write_post(two_rounds(), start_state(start_state(init_state(2), 0), 1), 0, 0, key_x(), 10, vc2(0, 0))
}
pub open spec fn holding() -> Server { Server { gvc: vc2(1, 0), icache: set![x1()], ccache: Map::empty() } }
pub open spec fn visible() -> Server {
    Server { gvc: vc2(1, 0), icache: Set::empty(), ccache: map![key_x() => Entry { value: 10, vc: vc2(1, 0) }] }
}
pub open spec fn hop1() -> State {
    propagate_post(two_rounds(), after_x(), 0,
        Server { gvc: zero(2), icache: set![x1()], ccache: Map::empty() })
}
pub open spec fn hop2() -> State { propagate_post(two_rounds(), hop1(), 1, holding()) }
/// Server 1 after merging x as its tail: x is visible and, as Figure 6 never
/// removes it there, still in I-cache.
pub open spec fn tail_x() -> Server {
    Server { gvc: vc2(1, 0), icache: set![x1()], ccache: map![key_x() => Entry { value: 10, vc: vc2(1, 0) }] }
}
pub open spec fn hop3() -> State { propagate_post(two_rounds(), hop2(), 0, tail_x()) }
pub open spec fn read_at_1() -> State {
    read_post(two_rounds(), hop3(), 1, 1, key_x(), tail_x(), Entry { value: 10, vc: vc2(1, 0) })
}
pub open spec fn read_at_0() -> State {
    read_post(two_rounds(), read_at_1(), 1, 0, key_x(), visible(), Entry { value: 10, vc: vc2(1, 0) })
}

/// x travels 0 -> 1 -> 0 -> 1; server 1 is its tail after two rounds and
/// merges it into C-cache.
pub proof fn lemma_two_round_propagation(t: Seq<State>) -> (after: Seq<State>)
    requires behavior(two_rounds(), t), t.last() == after_x(),
    ensures behavior(two_rounds(), after), after.last() == hop3(),
{
    let c = two_rounds();
    lemma_vcs();
    let s2 = start_state(start_state(init_state(2), 0), 1);
    assert(s2.clients[0] == empty_client());
    assert(write_deps(2, empty_client()) =~= Map::<int, VC>::empty());
    assert(new_version(c, s2, 0, 0, key_x(), 10, vc2(0, 0)) == x1());
    let s3 = after_x();
    assert(Set::<Version>::empty().insert(x1()) =~= set![x1()]);
    assert(s3.servers[0] == holding()) by { assert(s3.servers[0] =~= holding()); }
    assert(s3.servers[1] == empty_server(2));
    assert(s3.chans[0] =~= seq![Msg { version: x1(), hop: 1 }]);
    assert(s3.chans[1] =~= Seq::<Msg>::empty());
    assert(tail_hop(c) == 3);
    assert(succ(2, 0) == 1 && succ(2, 1) == 0);
    reveal(step);
    // Hop 1: server 1 stores x and forwards it.
    assert(!has_seen(2, empty_server(2), x1()));
    assert(stored(c, s3, 0) == (Server { gvc: zero(2), icache: set![x1()], ccache: Map::empty() }));
    let t = lemma_extend(c, t, hop1(), Action::Propagate { src: 0,
        mid: Server { gvc: zero(2), icache: set![x1()], ccache: Map::empty() },
        after: Server { gvc: zero(2), icache: set![x1()], ccache: Map::empty() } });
    // Hop 2: server 0 has seen x and forwards it again.
    let s4 = hop1();
    assert(s4.chans[1] =~= seq![Msg { version: x1(), hop: 2 }]);
    assert(s4.chans[0] =~= Seq::<Msg>::empty());
    assert(s4.servers[0] == holding());
    assert(has_seen(2, holding(), x1()));
    assert(!is_tail(c, s4, 1));
    let t = lemma_extend(c, t, hop2(), Action::Propagate { src: 1, mid: holding(), after: holding() });
    // Hop 3: server 1 is the tail. x has no deps, so integration changes
    // nothing, and x is merged into C-cache.
    let s5 = hop2();
    assert(s5.chans[0] =~= seq![Msg { version: x1(), hop: 3 }]);
    let at1 = Server { gvc: zero(2), icache: set![x1()], ccache: Map::empty() };
    assert(s5.servers[1] == at1);
    assert(is_tail(c, s5, 0));
    lemma_reach_nothing(at1.icache);
    assert(x1().deps == Map::<int, VC>::empty());
    lemma_integrate_nothing(2, at1, x1().deps);
    assert(tail_x().ccache =~= at1.ccache.insert(key_x(), Entry { value: 10, vc: vc2(1, 0) }));
    assert(entry(at1, 2, key_x()) == initial_entry(2));
    assert(one_vc(vc2(1, 0))(vc2(1, 0)));
    assert(merged(2, at1, x1(), tail_x()));
    lemma_extend(c, t, hop3(), Action::Propagate { src: 0, mid: at1, after: tail_x() })
}

/// Client 1 reads x at server 1, moves to server 0, and reads it again. The
/// second read integrates x from server 0's I-cache using the client's deps.
pub proof fn lemma_two_round_reads(t: Seq<State>) -> (after: Seq<State>)
    requires behavior(two_rounds(), t), t.last() == hop3(),
    ensures behavior(two_rounds(), after), after.last() == read_at_0(),
{
    let c = two_rounds();
    lemma_vcs();
    let s = hop3();
    assert(s.servers[1] == tail_x());
    assert(s.servers[0] == holding());
    assert(s.clients[1] == empty_client());
    lemma_reach_nothing(tail_x().icache);
    lemma_integrate_nothing(2, tail_x(), Map::<int, VC>::empty());
    reveal(step);
    let t = lemma_extend(c, t, read_at_1(),
        Action::Read { client: 1, server: 1, key: key_x(), after: tail_x(), result: Entry { value: 10, vc: vc2(1, 0) } });
    let s6 = read_at_1();
    let d = s6.clients[1].deps;
    assert(d =~= map![key_x() => vc2(1, 0)]);
    assert(s6.servers[0] == holding());
    let m = reached(holding().icache, d);
    lemma_singleton_chain(holding().icache, d, x1());
    assert(m =~= set![x1()]);
    assert(visible().icache =~= holding().icache.difference(m));
    assert forall|k: int| #[trigger] visible().ccache.dom().contains(k) <==>
        (holding().ccache.dom().contains(k) || exists|v: Version| #[trigger] m.contains(v) && v.key == k) by {
        if k == key_x() { assert(m.contains(x1())); }
    }
    assert(lub_of(2, entry(holding(), 2, key_x()).vc, key_vcs(m, key_x()), vc2(1, 0))) by {
        assert(key_vcs(m, key_x())(vc2(1, 0))) by { assert(m.contains(x1())); }
        assert forall|p: VC| #[trigger] key_vcs(m, key_x())(p) implies p == vc2(1, 0) by {}
    }
    assert(has_value(m, key_x(), 10)) by { assert(m.contains(x1())); }
    assert(lub_of(2, holding().gvc, dep_or_version_vcs(d, m), vc2(1, 0))) by {
        let parts = dep_or_version_vcs(d, m);
        assert forall|p: VC| #[trigger] parts(p) implies p == vc2(1, 0) by {}
    }
    assert(integrated(2, holding(), d, visible()));
    lemma_extend(c, t, read_at_0(),
        Action::Read { client: 1, server: 0, key: key_x(), after: visible(), result: Entry { value: 10, vc: vc2(1, 0) } })
}

/// With two rounds, a write completes propagation and a migrating client
/// reads it at both servers; the second read integrates it on demand.
pub proof fn theorem_two_round_migrating_reads() -> (t: Seq<State>)
    ensures
        behavior(two_rounds(), t),
        t.last().history.len() == 3,
        t.last().history[1] is Read && t.last().history[1]->Read_vc == vc2(1, 0),
        t.last().history[2] is Read && t.last().history[2]->Read_vc == vc2(1, 0),
        t.last().servers[0].icache == Set::<Version>::empty(),
{
    let c = two_rounds();
    let t = lemma_two_clients(c);
    let t = lemma_write_x(c, t);
    let t = lemma_two_round_propagation(t);
    let t = lemma_two_round_reads(t);
    lemma_vcs();
    t
}

} // verus!
