//! Reachability checks for the paper's recovery rule.
use super::types::*;
use super::normal::*;
use super::recovery::*;
use super::behavior::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn config() -> Constants { Constants { shards: 2, f: 1 } }
pub open spec fn write_both() -> Txn { Txn { ops: map![0int => Op::Put { value: 10 }, 1int => Op::Put { value: 10 }] } }
pub open spec fn increment_x() -> Txn { Txn { ops: map![0int => Op::Add { delta: 1 }] } }
pub open spec fn read_x() -> Txn { Txn { ops: map![0int => Op::Read] } }
pub open spec fn b() -> Entry { Entry { id: 0, ts: 10 } }
pub open spec fn a() -> Entry { Entry { id: 1, ts: 20 } }
pub open spec fn r() -> Entry { Entry { id: 2, ts: 30 } }

pub open spec fn requests(n: int, e: Entry, gv: nat, lv: nat) -> Packet {
    packet(Kind::Request, -1, n, gv, lv, e)
}
pub open spec fn fast(n: int, e: Entry, gv: nat, lv: nat, prefix: Seq<Entry>, result: int) -> Packet {
    Packet { log: prefix, result, ..packet(Kind::Fast, n, -1, gv, lv, e) }
}
pub open spec fn bodies() -> Map<int, Txn> { map![0int => write_both(), 1int => increment_x()] }

pub proof fn lemma_submit_packet(s: State, c: Constants, id: int, txn: Txn, ts: int, n: int)
    requires member(c, n), txn.ops.dom().contains(shard(c, n)), s.views.len() > 0,
        0 <= shard(c, n) < s.views.last().len(),
    ensures submit(s, c, id, txn, ts).network.contains(requests(n, Entry { id, ts },
        (s.views.len() - 1) as nat, s.views.last()[shard(c, n)]))
{
    broadcast use {group_set_lib_default, group_set_properties, Set::lemma_set_map_insert_commute,
        range_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    let dests = members(c).filter(|n: int| txn.ops.dom().contains(shard(c, n)));
    let gv = (s.views.len() - 1) as nat;
    let f = |n: int| packet(Kind::Request, -1, n, gv, s.views[gv as int][shard(c, n)], Entry { id, ts });
    assert(dests.contains(n));
    assert(f(n) == requests(n, Entry { id, ts }, gv, s.views.last()[shard(c, n)]));
    dests.lemma_map_contains(f, f(n));
}

pub proof fn lemma_setup() -> (trace: Seq<State>)
    ensures behavior(trace, config()), trace.last().txns == bodies(),
        trace.last().nodes == initial(config()).nodes,
        trace.last().views == initial(config()).views,
        trace.last().completed == Map::<int, Completion>::empty(),
        trace.last().client_view == map![0int => 0nat, 1int => 0nat],
        trace.last().tick == 2,
        forall |n: int| 0 <= n < 6 ==> #[trigger] trace.last().network.contains(requests(n, b(), 0, 0)),
        forall |n: int| 0 <= n < 3 ==> #[trigger] trace.last().network.contains(requests(n, a(), 0, 0)),
{
    broadcast use {group_set_lib_default, group_set_properties, Set::lemma_set_map_insert_commute,
        range_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    let c = config();
    lemma_initial(c);
    reveal(enabled);
    reveal(apply);
    let first = Action::Submit { id: 0, txn: write_both(), ts: 10 };
    let t = lemma_extend(seq![initial(c)], c, first);
    let s1 = t.last();
    let second = Action::Submit { id: 1, txn: increment_x(), ts: 20 };
    let t = lemma_extend(t, c, second);
    assert forall |n: int| 0 <= n < 6 implies #[trigger] t.last().network.contains(requests(n, b(), 0, 0)) by {
        assert(n / 3 == 0 || n / 3 == 1);
        lemma_submit_packet(initial(c), c, 0, write_both(), 10, n);
    }
    assert forall |n: int| 0 <= n < 3 implies #[trigger] t.last().network.contains(requests(n, a(), 0, 0)) by {
        assert(n / 3 == 0);
        lemma_submit_packet(s1, c, 1, increment_x(), 20, n);
    }
    assert(t.last().txns =~= bodies());
    t
}

pub open spec fn delivered_node(s: State, n: int, e: Entry) -> Replica {
    if am_leader(s, config(), n) {
        Replica { clock: 100, queue: map![e.id => Pending { entry: e, executed: true }],
            seen: map![e.id => e], ..empty_replica() }
    } else {
        Replica { clock: 100, log: seq![e], seen: map![e.id => e], ..empty_replica() }
    }
}

pub proof fn lemma_deliver_and_release(trace: Seq<State>, n: int, e: Entry) -> (after: Seq<State>)
    requires behavior(trace, config()), 0 <= n < 6, trace.last().nodes.len() == 6,
        trace.last().nodes[n] == empty_replica(), trace.last().views == initial(config()).views,
        trace.last().txns.dom().contains(e.id), trace.last().txns[e.id].ops.dom().contains(shard(config(), n)),
        0 <= e.ts <= 100, trace.last().network.contains(requests(n, e, 0, 0)),
    ensures behavior(after, config()),
        after.last().nodes == trace.last().nodes.update(n, delivered_node(trace.last(), n, e)),
        after.last().network.contains(fast(n, e, 0, 0, Seq::empty(),
            if am_leader(trace.last(), config(), n) { return_op(0, trace.last().txns[e.id].ops[shard(config(), n)]) } else { 0 })),
        trace.last().network.subset_of(after.last().network),
        after.last().txns == trace.last().txns, after.last().views == trace.last().views,
        after.last().client_view == trace.last().client_view, after.last().completed == trace.last().completed,
        after.last().tick == trace.last().tick + 3,
{
    broadcast use {group_set_lib_default, group_set_properties, Set::lemma_set_map_insert_commute,
        range_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    let c = config();
    reveal(enabled);
    reveal(apply);
    let t = lemma_extend(trace, c, Action::Tick { node: n, time: 100 });
    let t = lemma_extend(t, c, Action::Receive { p: requests(n, e, 0, 0) });
    let t = lemma_extend(t, c, Action::Release { node: n, id: e.id });
    assert(t.last().nodes[n].queue =~= delivered_node(trace.last(), n, e).queue);
    assert(t.last().nodes[n].seen =~= delivered_node(trace.last(), n, e).seen);
    assert(t.last().nodes[n].log =~= delivered_node(trace.last(), n, e).log);
    assert(t.last().nodes =~= trace.last().nodes.update(n, delivered_node(trace.last(), n, e)));
    t
}

pub open spec fn before_recovery(s: State) -> bool {
    &&& s.nodes.len() == 6
    &&& s.views == initial(config()).views
    &&& s.txns == bodies()
    &&& s.completed.dom() == set![1int]
    &&& s.completed[1].results == map![0int => 0int]
    &&& s.completed[1].gv == 0
    &&& s.completed[1].tick < s.tick
    &&& s.tick == 18
    &&& s.nodes[0].status is Normal
    &&& s.nodes[1] == (Replica { clock: 100, log: seq![a()], seen: map![1int => a()], ..empty_replica() })
    &&& s.nodes[2] == s.nodes[1]
    &&& s.nodes[4] == (Replica { clock: 100, log: seq![b()], seen: map![0int => b()], ..empty_replica() })
    &&& s.nodes[5] == s.nodes[4]
}

/// B reaches only Y's followers. A then fast-commits in X with result zero.
pub proof fn lemma_fast_committed_trace() -> (trace: Seq<State>)
    ensures behavior(trace, config()), before_recovery(trace.last())
{
    broadcast use {group_set_lib_default, group_set_properties, Set::lemma_set_map_insert_commute,
        range_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    let c = config();
    let t = lemma_setup();
    let t = lemma_deliver_and_release(t, 4, b());
    let t = lemma_deliver_and_release(t, 5, b());
    let t = lemma_deliver_and_release(t, 0, a());
    let t = lemma_deliver_and_release(t, 1, a());
    let t = lemma_deliver_and_release(t, 2, a());
    let p0 = fast(0, a(), 0, 0, Seq::empty(), 0);
    let p1 = fast(1, a(), 0, 0, Seq::empty(), 0);
    let p2 = fast(2, a(), 0, 0, Seq::empty(), 0);
    let votes = map![0int => p0, 1int => p1, 2int => p2];
    assert(votes.dom() =~= set![0int, 1int, 2int]);
    assert(votes.dom().len() == 3);
    let leaders = map![0int => p0];
    let all_votes = map![0int => votes];
    assert(can_complete(t.last(), c, 1, leaders, all_votes, 20));
    reveal(enabled);
    reveal(apply);
    let t = lemma_extend(t, c, Action::Complete { id: 1, leaders, votes: all_votes, ts: 20 });
    assert(t.last().completed[1].results =~= map![0int => 0int]);
    t
}

pub open spec fn view_packet(n: int) -> Packet {
    packet(Kind::View, -2, n, 1, 1, blank_entry())
}
pub open spec fn report(n: int, e: Entry) -> Packet {
    Packet { log: seq![e], ..packet(Kind::Report, n, (n / 3) * 3 + 1, 1, 1, blank_entry()) }
}
pub open spec fn rebuilt(n: int, dst: int, e: Entry) -> Packet {
    Packet { log: seq![e], ..packet(Kind::Rebuilt, n, dst, 1, 1, blank_entry()) }
}
pub open spec fn recovery_views() -> Seq<Seq<nat>> { seq![seq![0nat, 0nat], seq![1nat, 1nat]] }
pub open spec fn follower(e: Entry) -> Replica {
    Replica { clock: 100, log: seq![e], seen: map![e.id => e], ..empty_replica() }
}
pub open spec fn reporting(e: Entry) -> Replica {
    Replica { gv: 1, lv: 1, status: Status::ViewChange, ..follower(e) }
}
pub open spec fn context_same(s: State, t: State) -> bool {
    s.txns == t.txns && s.views == t.views && s.completed == t.completed
        && s.client_view == t.client_view && s.invoked == t.invoked
}

pub proof fn lemma_enter(trace: Seq<State>, n: int, e: Entry) -> (after: Seq<State>)
    requires behavior(trace, config()), trace.last().nodes.len() == 6, 0 <= n < 6,
        trace.last().nodes[n] == follower(e), trace.last().views == recovery_views(),
        trace.last().network.contains(view_packet(n)),
    ensures behavior(after, config()), context_same(trace.last(), after.last()),
        after.last().nodes == trace.last().nodes.update(n, reporting(e)),
        trace.last().network.subset_of(after.last().network),
        after.last().network.contains(report(n, e)), after.last().tick == trace.last().tick + 1,
{
    broadcast use {group_set_lib_default, group_set_properties, Set::lemma_set_map_insert_commute,
        range_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    reveal(enabled); reveal(apply);
    assert(n / 3 == 0 || n / 3 == 1);
    assert(ids(Seq::<Entry>::empty()) =~= Set::<int>::empty());
    let t = lemma_extend(trace, config(), Action::EnterView { p: view_packet(n), pending: Seq::empty() });
    assert(t.last().nodes[n].log =~= seq![e]);
    t
}

pub proof fn lemma_view_packets(s: State, n: int)
    requires s.views == initial(config()).views, 0 <= n < 6,
    ensures new_view(s, config(), seq![1nat, 1nat]).network.contains(view_packet(n)),
{
    broadcast use {group_set_lib_default, group_set_properties, Set::lemma_set_map_insert_commute,
        range_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    assert(n / 3 == 0 || n / 3 == 1);
    let f = |n: int| packet(Kind::View, -2, n, s.views.len(), seq![1nat, 1nat][shard(config(), n)], blank_entry());
    lemma_int_range(0, 6);
    assert(config().shards == 2);
    assert(config().f == 1);
    assert(replicas(config()) == 3);
    assert(count(config()) == 6) by (compute);
    assert(members(config()).contains(n));
    assert(f(n) == view_packet(n));
    members(config()).lemma_map_contains(f, f(n));
}

pub proof fn lemma_reported_trace() -> (trace: Seq<State>)
    ensures behavior(trace, config()), trace.last().nodes.len() == 6,
        trace.last().views == recovery_views(), trace.last().txns == bodies(),
        trace.last().nodes[0].status is Down,
        trace.last().nodes[1] == reporting(a()), trace.last().nodes[2] == reporting(a()),
        trace.last().nodes[4] == reporting(b()), trace.last().nodes[5] == reporting(b()),
        trace.last().completed.dom() == set![1int],
        trace.last().completed[1].results == map![0int => 0int],
        trace.last().completed[1].gv == 0, trace.last().completed[1].tick < trace.last().tick,
        trace.last().network.contains(report(1, a())), trace.last().network.contains(report(2, a())),
        trace.last().network.contains(report(4, b())), trace.last().network.contains(report(5, b())),
{
    broadcast use {group_set_lib_default, group_set_properties, Set::lemma_set_map_insert_commute,
        range_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    reveal(enabled); reveal(apply);
    let t = lemma_fast_committed_trace();
    let s = t.last();
    assert(shard_members(config(), 0).filter(|n: int| s.nodes[n].status is Down) =~= Set::<int>::empty());
    let t = lemma_extend(t, config(), Action::Crash { node: 0 });
    let old = t.last();
    let t = lemma_extend(t, config(), Action::NewView { views: seq![1nat, 1nat] });
    assert(old.views[0] =~= seq![0nat, 0nat]);
    assert(t.last().views =~= recovery_views());
    lemma_view_packets(old, 1); lemma_view_packets(old, 2);
    lemma_view_packets(old, 4); lemma_view_packets(old, 5);
    let t = lemma_enter(t, 1, a());
    let t = lemma_enter(t, 2, a());
    let t = lemma_enter(t, 4, b());
    let t = lemma_enter(t, 5, b());
    t
}

pub proof fn lemma_singleton_rebuild(n: int, e: Entry)
    requires n == 1 || n == 4,
    ensures recovered_entries(config(), map![n => report(n, e), n + 1 => report(n + 1, e)], n) == set![e],
{
    broadcast use {group_set_lib_default, group_set_properties, Set::lemma_set_map_insert_commute,
        range_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    let batch = map![n => report(n, e), n + 1 => report(n + 1, e)];
    assert(batch.dom() =~= set![n, n + 1]);
    let f = |sender: int| batch[sender].log.skip(batch[sender].synced as int).to_set();
    assert(batch[n].log.skip(0) =~= seq![e]);
    assert(seq![e].to_set() =~= set![e]);
    assert(f(n) =~= set![e]);
    assert(batch[n + 1].log.skip(0) =~= seq![e]);
    assert(f(n + 1) =~= set![e]);
    assert(f(n) == set![e]);
    assert(f(n + 1) == set![e]);
    batch.dom().lemma_map_contains(f, set![e]);
    assert(batch.dom().map(f) =~= set![set![e]]);
    assert(tail_candidates(batch) =~= set![e]);
    assert(supporters(batch, e) =~= set![n, n + 1]);
    assert(recovered_entries(config(), batch, n) =~= set![e]);
}

pub proof fn lemma_rebuild(trace: Seq<State>, n: int, e: Entry) -> (after: Seq<State>)
    requires behavior(trace, config()), trace.last().nodes.len() == 6, n == 1 || n == 4,
        trace.last().views == recovery_views(), trace.last().nodes[n] == reporting(e),
        trace.last().network.contains(report(n, e)), trace.last().network.contains(report(n + 1, e)),
    ensures behavior(after, config()), context_same(trace.last(), after.last()),
        after.last().nodes == trace.last().nodes.update(n, Replica { status: Status::Rebuilt, ..reporting(e) }),
        trace.last().network.subset_of(after.last().network),
        after.last().network.contains(rebuilt(n, 1, e)), after.last().network.contains(rebuilt(n, 4, e)),
        after.last().tick == trace.last().tick + 1,
{
    broadcast use {group_set_lib_default, group_set_properties, Set::lemma_set_map_insert_commute,
        range_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    reveal(enabled); reveal(apply);
    let batch = map![n => report(n, e), n + 1 => report(n + 1, e)];
    assert(batch.dom() =~= set![n, n + 1]);
    lemma_singleton_rebuild(n, e);
    assert(am_leader(trace.last(), config(), n));
    assert(view_reports(trace.last(), config(), n, batch));
    assert(maximal_snapshot(batch, n));
    assert(seq![e].to_set() =~= set![e]);
    let t = lemma_extend(trace, config(), Action::Rebuild { node: n, replies: batch, selected: n, log: seq![e] });
    let f = |sh: int| Packet { log: seq![e], ..packet(Kind::Rebuilt, n,
        leader(trace.last(), config(), trace.last().nodes[n].gv, sh), trace.last().nodes[n].gv,
        trace.last().views[trace.last().nodes[n].gv as int][sh], blank_entry()) };
    assert(f(0) == rebuilt(n, 1, e));
    assert(f(1) == rebuilt(n, 4, e));
    lemma_int_range(0, 2);
    Set::range(0, config().shards).lemma_map_contains(f, f(0));
    Set::range(0, config().shards).lemma_map_contains(f, f(1));
    let output = Set::range(0, config().shards).map(f);
    assert(Set::range(0, config().shards).contains(0));
    assert(Set::range(0, config().shards).contains(1));
    assert(output.contains(rebuilt(n, 1, e)));
    assert(output.contains(rebuilt(n, 4, e)));
    assert(rebuild(trace.last(), config(), n, seq![e]).network == trace.last().network.union(output));
    assert(t.last().network == rebuild(trace.last(), config(), n, seq![e]).network);
    t
}

pub proof fn lemma_import(s: State)
    requires s.txns == bodies(),
    ensures merged_entries(s, config(), 1, map![0int => rebuilt(1, 1, a()), 1int => rebuilt(4, 1, b())]) == set![b(), a()],
{
    broadcast use {group_set_lib_default, group_set_properties, Set::lemma_set_map_insert_commute,
        range_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    let batch = map![0int => rebuilt(1, 1, a()), 1int => rebuilt(4, 1, b())];
    assert(batch.dom() =~= set![0int, 1int]);
    let f = |sh: int| batch[sh].log.to_set();
    assert(batch[0].log == seq![a()]);
    assert(batch[1].log == seq![b()]);
    assert(seq![a()].to_set() =~= set![a()]);
    assert(seq![b()].to_set() =~= set![b()]);
    assert(f(0) =~= set![a()]); assert(f(1) =~= set![b()]);
    batch.dom().lemma_map_contains(f, set![a()]);
    batch.dom().lemma_map_contains(f, set![b()]);
    assert(f(0) == set![a()]); assert(f(1) == set![b()]);
    assert(batch.dom().map(f) =~= set![set![a()], set![b()]]);
    assert(batch.dom().map(f).flatten() =~= set![a(), b()]);
    assert(shard(config(), 1) == 0) by (compute);
    assert(s.txns[a().id].ops.dom().contains(0));
    assert(s.txns[b().id].ops.dom().contains(0));
    assert(imported_entries(s, config(), 1, batch) =~= set![a(), b()]);
    assert(merged_entries(s, config(), 1, batch) =~= set![a(), b()]);
}

/// Algorithm 5 imports B before an already completed A, changing A's result.
pub proof fn lemma_recovery_changes_result() -> (trace: Seq<State>)
    ensures behavior(trace, config()), after_recovery(trace.last()), trace.last().txns == bodies(),
        trace.last().nodes[1].status is Normal, trace.last().nodes[1].gv == 1,
        trace.last().nodes[1].log == seq![b(), a()],
        trace.last().completed.dom().contains(1), trace.last().completed[1].gv == 0,
        trace.last().completed[1].results[0] == 0,
        return_op(eval(trace.last().txns, 0, trace.last().nodes[1].log.take(1)),
            trace.last().txns[1].ops[0]) == 10,
{
    broadcast use {group_set_lib_default, group_set_properties, Set::lemma_set_map_insert_commute,
        range_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    reveal(enabled); reveal(apply);
    let t = lemma_reported_trace();
    let t = lemma_rebuild(t, 1, a());
    let t = lemma_rebuild(t, 4, b());
    let batch = map![0int => rebuilt(1, 1, a()), 1int => rebuilt(4, 1, b())];
    lemma_import(t.last());
    assert(seq![b(), a()].to_set() =~= set![b(), a()]);
    assert(batch.dom() =~= Set::range(0, 2));
    assert(reconstruction_reports(t.last(), config(), 1, batch));
    let t = lemma_extend(t, config(), Action::Install { node: 1, replies: batch, log: seq![b(), a()] });
    assert(t.last().nodes[1].log.take(1) =~= seq![b()]);
    let p = Packet { dst: 1, ..start_x() };
    assert(shard_members(config(), 0).remove(1).contains(2));
    shard_members(config(), 0).remove(1).lemma_map_contains(|dst: int| Packet { dst, ..p }, start_x());
    assert(t.last().nodes[1] == recovered_x());
    assert(t.last().nodes[2] == reporting(a()));
    assert(t.last().completed[1].tick < t.last().tick);
    assert(t.last().network.contains(start_x()));
    reveal_with_fuel(eval, 2);
    t
}

pub open spec fn start_x() -> Packet {
    Packet { log: seq![b(), a()], synced: 2, last_normal: 1,
        ..packet(Kind::Start, 1, 2, 1, 1, blank_entry()) }
}
pub open spec fn recovered_x() -> Replica {
    Replica { gv: 1, lv: 1, last_normal: 1, clock: 100, log: seq![b(), a()],
        synced: 2, seen: log_seen(seq![b(), a()]), ..empty_replica() }
}
pub open spec fn after_recovery(s: State) -> bool {
    &&& s.nodes.len() == 6 && s.views == recovery_views()
    &&& s.nodes[1] == recovered_x() && s.nodes[2] == reporting(a())
    &&& s.txns == bodies() && s.completed.dom() == set![1int]
    &&& s.completed[1].results == map![0int => 0int]
    &&& s.completed[1].gv == 0 && s.completed[1].tick < s.tick
    &&& s.network.contains(start_x())
}

pub proof fn lemma_seen_ba()
    ensures log_seen(seq![b(), a()]) == map![0int => b(), 1int => a()],
{
    broadcast use {group_set_lib_default, group_set_properties, Set::lemma_set_map_insert_commute,
        range_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    let log = seq![b(), a()];
    assert(log.to_set() =~= set![b(), a()]);
    assert(ids(log) =~= set![0int, 1int]);
    assert(log.contains(b()) && log.contains(a()));
    let p0 = choose |e: Entry| #![trigger log.contains(e)] log.contains(e) && e.id == 0;
    let p1 = choose |e: Entry| #![trigger log.contains(e)] log.contains(e) && e.id == 1;
    assert(p0 == b() && p1 == a());
    assert(log_seen(log)[0] == b());
    assert(log_seen(log)[1] == a());
    assert(log_seen(log) =~= map![0int => b(), 1int => a()]);
}

/// A later read observes the replayed increment, so the changed result is visible.
pub proof fn lemma_bad_history() -> (trace: Seq<State>)
    ensures behavior(trace, config()),
        trace.last().txns == bodies().insert(2, read_x()),
        trace.last().completed.dom() == set![1int, 2int],
        trace.last().completed[1].results[0] == 0,
        trace.last().completed[2].results[0] == 11,
        trace.last().completed[1].tick < trace.last().invoked[2],
{
    broadcast use {group_set_lib_default, group_set_properties, Set::lemma_set_map_insert_commute,
        range_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    reveal(enabled); reveal(apply);
    reveal_with_fuel(eval, 4);
    lemma_seen_ba();
    let c = config();
    let t = lemma_recovery_changes_result();
    assert(current(t.last(), c, start_x()));
    let t = lemma_extend(t, c, Action::Start { p: start_x() });
    let old = t.last();
    let t = lemma_extend(t, c, Action::Submit { id: 2, txn: read_x(), ts: 30 });
    lemma_submit_packet(old, c, 2, read_x(), 30, 1);
    lemma_submit_packet(old, c, 2, read_x(), 30, 2);
    let t = lemma_extend(t, c, Action::Receive { p: requests(1, r(), 1, 1) });
    let t = lemma_extend(t, c, Action::Release { node: 1, id: 2 });
    let first = fast(1, r(), 1, 1, seq![b(), a()], 11);
    assert(t.last().network.contains(first));
    let timestamp = packet(Kind::Timestamp, 1, 1, 1, 1, r());
    let f = |sh: int| packet(Kind::Timestamp, 1, leader(t.last(), c, 1, sh), 1, t.last().views[1][sh], r());
    t.last().txns[2].ops.dom().lemma_map_contains(f, f(0));
    assert(t.last().network.contains(timestamp));
    let replies = map![0int => timestamp];
    let prev = t.last();
    assert(replies.dom().contains(0));
    assert(replies[0].entry.ts == 30);
    assert(timestamp_replies(prev, c, 1, 2, replies));
    assert(can_agree(prev, c, 1, 2, replies, 30));
    let t = lemma_extend(t, c, Action::Agree { node: 1, id: 2, replies, ts: 30 });
    let log = seq![b(), a(), r()];
    assert(prev.nodes[1].log.push(r()) =~= log);
    let sync_p = Packet { log, synced: 3, ..packet(Kind::Sync, 1, 2, 1, 1, r()) };
    let destinations = shard_members(c, 0).remove(1);
    let source = Packet { dst: 1, ..sync_p };
    assert(destinations.contains(2));
    destinations.lemma_map_contains(|dst: int| Packet { dst, ..source }, sync_p);
    assert(t.last().network.contains(sync_p));
    let t = lemma_extend(t, c, Action::Sync { p: sync_p });
    let slow = Packet { log, synced: 3, ..packet(Kind::Slow, 2, -1, 1, 1, r()) };
    let votes = map![1int => first, 2int => slow];
    assert(votes.dom().filter(|n: int| votes[n].kind is Slow) =~= set![2int]);
    assert(log.take(2) =~= seq![b(), a()]);
    let t = lemma_extend(t, c, Action::Complete { id: 2, leaders: map![0int => first],
        votes: map![0int => votes], ts: 30 });
    t
}

} // verus!
