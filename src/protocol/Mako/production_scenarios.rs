//! Constructive executions through the actual producer and network handlers.
use vstd::prelude::*;
use vstd::imap::IMap as Map;
use vstd::iset::ISet as Set;
use super::model as abs;
use super::model::{Bound, Tx, Stream, endpoint, shard, stream, bound_le};
use super::production::*;
use super::production_proof::*;
use super::watermark_math::*;
use super::scenarios as old;

verus! {

pub open spec fn empty(c: Settings) -> State {
    State { core: old::empty_state(c.protocol),
        reports: Map::new(|k: Stream| stream(c.protocol, k), |k| Bound::Finite(0)),
        local: Map::new(|p: (nat, int)| shard(c.protocol, p.1), |p| Bound::Finite(0)),
        views: Map::new(|p: (int, nat, int)| observer(c, p.0) && shard(c.protocol, p.2), |p| Bound::Finite(0)),
        sealed_reports: Set::empty(), sealed_local: Set::empty(), sealed_views: Set::empty(),
        worker_net: Set::empty(), gossip_net: Set::empty() }
}
pub proof fn start(c: Settings) -> (h: Seq<State>)
    requires abs::valid(c.protocol), c.observers > 0
    ensures behavior(c, h), inv(c, h.last()), h == seq![empty(c)]
{
    let s = empty(c);
    assert(initial(c, s));
    init_inv(c, s);
    seq![s]
}
pub proof fn take(c: Settings, h: Seq<State>, a: Action) -> (z: Seq<State>)
    requires behavior(c, h), inv(c, h.last()), step(c, h.last(), effect(c, h.last(), a), a)
    ensures behavior(c, z), inv(c, z.last()), z == h.push(effect(c, h.last(), a))
{
    let s2 = effect(c, h.last(), a);
    step_inv(c, h.last(), s2, a);
    assert(next(c, h.last(), s2));
    let z = h.push(s2);
    assert forall|i: int| 0 <= i < z.len() - 1 implies #[trigger] next(c, z[i], z[i+1]) by {
        if i < h.len() - 1 { assert(next(c, h[i], h[i+1])); }
    }
    z
}
// A finite schedule that samples and consumes every worker report. The core
// endpoints do not change during this schedule; arbitrary interleavings are
// covered by the general induction, not by this witness helper.
pub proof fn collect(c: Settings, h: Seq<State>, e: nat, sh: int, count: nat) -> (z: Seq<State>)
    requires behavior(c, h), inv(c, h.last()), shard(c.protocol, sh), count <= c.protocol.workers
    ensures behavior(c, z), inv(c, z.last()), z.last().core == h.last().core,
        z.last() == (State { reports: z.last().reports, sealed_reports: z.last().sealed_reports,
            worker_net: z.last().worker_net, ..h.last() }),
        forall|w: int| 0 <= w < count ==>
            #[trigger] z.last().reports[worker(e, sh, w)] == endpoint(h.last().core, worker(e, sh, w)) &&
            (z.last().sealed_reports.contains(worker(e, sh, w)) == h.last().core.closed.contains(worker(e, sh, w)))
    decreases count
{
    if count == 0 { h }
    else {
        let h2 = collect(c, h, e, sh, (count-1) as nat);
        let k = worker(e, sh, count as int-1);
        let m = report(h2.last(), k);
        reveal(step);
        let h3 = take(c, h2, Action::Sample { stream: k });
        let h4 = take(c, h3, Action::ReceiveWorker { report: m });
        order(h2.last().reports[k], m.value, m.value);
        assert forall|w: int| 0 <= w < count implies
            #[trigger] h4.last().reports[worker(e, sh, w)] == endpoint(h.last().core, worker(e, sh, w)) &&
            (h4.last().sealed_reports.contains(worker(e, sh, w)) == h.last().core.closed.contains(worker(e, sh, w))) by {
            if w < count-1 { assert(worker(e, sh, w) != k); }
        }
        h4
    }
}
pub proof fn produce(c: Settings, h: Seq<State>, e: nat, sh: int, o: int) -> (z: Seq<State>)
    requires behavior(c, h), inv(c, h.last()), shard(c.protocol, sh), observer(c, o)
    ensures behavior(c, z), inv(c, z.last()),
        z.last().core == abs::publish_result(c.protocol, h.last().core, e, sh,
            minimum(endpoints(c, h.last().core), e, sh, c.protocol.workers as nat)),
        z.last().views == h.last().views.insert((o, e, sh), minimum(endpoints(c, h.last().core), e, sh, c.protocol.workers as nat)),
        h.last().gossip_net.subset_of(z.last().gossip_net),
        h.last().sealed_views.subset_of(z.last().sealed_views),
        z.last().local[(e, sh)] == minimum(endpoints(c, h.last().core), e, sh, c.protocol.workers as nat),
        complete(c, h.last().core, e, sh) ==> z.last().sealed_views.contains((o, e, sh)) && z.last().sealed_local.contains((e, sh))
{
    reveal(step);
    let h2 = collect(c, h, e, sh, c.protocol.workers as nat);
    let ends = endpoints(c, h.last().core);
    assert forall|w: int| 0 <= w < c.protocol.workers implies #[trigger] h2.last().reports[worker(e, sh, w)] == ends[worker(e, sh, w)] by { }
    minimum_equal(h2.last().reports, ends, e, sh, c.protocol.workers as nat);
    if complete(c, h.last().core, e, sh) {
        assert forall|w: int| 0 <= w < c.protocol.workers implies #[trigger] h2.last().sealed_reports.contains(worker(e, sh, w)) by {
            assert(h2.last().reports[worker(e, sh, w)] == endpoint(h.last().core, worker(e, sh, w)));
        }
    }
    let h3 = take(c, h2, Action::Compute { epoch: e, shard: sh });
    let m = gossip(h3.last(), e, sh, o);
    let h4 = take(c, h3, Action::Send { epoch: e, shard: sh, observer: o });
    let z = take(c, h4, Action::Receive { message: m });
    lower_min(c, h.last().core, e, sh, h.last().views[(o, e, sh)]);
    assert(lower(c, h.last().core, e, sh, h.last().core.wm[(e, sh)]));
    lower_min(c, h.last().core, e, sh, h.last().core.wm[(e, sh)]);
    assert(z.last().views =~= h.last().views.insert((o, e, sh), minimum(ends, e, sh, c.protocol.workers as nat)));
    z
}

pub proof fn theorem_commit_through_production() -> (h: Seq<State>)
    ensures behavior(Settings { protocol: abs::Config { shards: 2, workers: 1 }, observers: 2 }, h),
        h.last().core.acked.contains(0), h.last().core.replayed.contains((0, 0)),
        h.last().core.tx == Map::<int, Tx>::empty().insert(0, old::both(0)),
        h.last().views[(0, 0, 0)] == Bound::Finite(1),
        h.last().views[(1, 0, 0)] == Bound::Finite(0)
{
    let c = Settings { protocol: abs::Config { shards: 2, workers: 1 }, observers: 2 };
    reveal(step); reveal(abs::step);
    reveal_with_fuel(minimum, 3);
    let h = start(c);
    old::both_valid(0);
    assert(abs::read_max(view(c, h.last(), 0), old::both(0), 0, 0));
    assert(abs::read_max(view(c, h.last(), 0), old::both(0), 1, 0));
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Begin { id: 0, tx: old::both(0) } });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Install { id: 0, shard: 0 } });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Install { id: 0, shard: 1 } });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Replicate { stream: worker(0, 0, 0), progress: 1 } });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Replicate { stream: worker(0, 1, 0), progress: 1 } });
    let h = produce(c, h, 0, 0, 0);
    let h = produce(c, h, 0, 1, 0);
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Ack { id: 0 } });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Replay { id: 0, shard: 0 } });
    h
}

pub open spec fn single_tx(w: int, v: nat) -> Tx {
    Tx { epoch: 0, vc: Map::new(|i: int| i == 0, |i: int| v),
        part: Map::empty().insert(0, w), deps: Set::empty() }
}
pub proof fn single_valid(w: int, v: nat)
    requires 0 <= w < 2, v > 0
    ensures abs::tx_valid(abs::Config { shards: 1, workers: 2 }, single_tx(w, v))
{
    assert(single_tx(w, v).vc.dom() =~= Set::new(|i: int| shard(abs::Config { shards: 1, workers: 2 }, i)));
    assert(single_tx(w, v).part.dom().contains(0));
}
/// An idle worker holds the minimum at zero. Once both workers have reported,
/// a transaction commits. Final reports survive reordered messages and can be
/// recollected after an observer restart, even in a later current epoch.
pub open spec fn two_settings() -> Settings {
    Settings { protocol: abs::Config { shards: 1, workers: 2 }, observers: 2 }
}
pub open spec fn stale_zero() -> Gossip {
    Gossip { dst: 0, epoch: 0, shard: 0, value: Bound::Finite(0), sealed: false }
}
pub proof fn two_worker_prefix() -> (h: Seq<State>)
    ensures behavior(two_settings(), h), inv(two_settings(), h.last()),
        h.last().core.epoch == 0, h.last().core.acked.contains(0),
        h.last().core.tx.dom().contains(1), h.last().core.tx[1] == single_tx(1, 2),
        h.last().core.progress[worker(0, 0, 0)] == 1, h.last().core.tail[worker(0, 0, 0)] == 1,
        h.last().core.progress[worker(0, 0, 1)] == 2, h.last().core.tail[worker(0, 0, 1)] == 2,
        !h.last().core.busy.dom().contains(worker(0, 0, 0)), !h.last().core.busy.dom().contains(worker(0, 0, 1)),
        h.last().gossip_net.contains(stale_zero())
{
    let c = Settings { protocol: abs::Config { shards: 1, workers: 2 }, observers: 2 };
    reveal(step); reveal(abs::step); reveal_with_fuel(minimum, 4);
    let h = start(c);
    let stale = gossip(h.last(), 0, 0, 0);
    let h = take(c, h, Action::Send { epoch: 0, shard: 0, observer: 0 });
    single_valid(0, 1);
    assert(abs::read_max(view(c, h.last(), 0), single_tx(0, 1), 0, 0));
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Begin { id: 0, tx: single_tx(0, 1) } });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Install { id: 0, shard: 0 } });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Replicate { stream: worker(0, 0, 0), progress: 1 } });
    let h = produce(c, h, 0, 0, 0);
    assert(h.last().views[(0, 0, 0)] == Bound::Finite(0));
    assert(h.last().core.tx[0].vc[0] == 1);
    assert(view(c, h.last(), 0).wm[(0, 0)] == Bound::Finite(0));
    assert(!abs::below_wm(c.protocol, view(c, h.last(), 0), h.last().core.tx[0]));
    single_valid(1, 2);
    assert(abs::read_max(view(c, h.last(), 0), single_tx(1, 2), 0, 0));
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Begin { id: 1, tx: single_tx(1, 2) } });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Install { id: 1, shard: 0 } });
    assert(h.last().core.tx.dom().contains(1));
    assert(h.last().core.installed.contains((1, 0)));
    assert(abs::key(h.last().core.tx[1], 0) == worker(0, 0, 1));
    assert(h.last().core.tx[1].vc[0] == 2);
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Replicate { stream: worker(0, 0, 1), progress: 2 } });
    let h = produce(c, h, 0, 0, 0);
    assert(h.last().views[(0, 0, 0)] == Bound::Finite(1));
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Ack { id: 0 } });
    h
}

pub proof fn theorem_two_workers_and_recovery() -> (h: Seq<State>)
    ensures behavior(Settings { protocol: abs::Config { shards: 1, workers: 2 }, observers: 2 }, h),
        h.last().core.acked.contains(0), h.last().core.acked.contains(1),
        h.last().views[(0, 0, 0)] == Bound::Infinity,
        h.last().views[(1, 0, 0)] == Bound::Infinity,
        h.last().views[(0, 2, 0)] == Bound::Finite(0),
        h.last().sealed_views.contains((0, 0, 0)), h.last().sealed_views.contains((1, 0, 0))
{
    let c = two_settings();
    reveal(step); reveal(abs::step); reveal_with_fuel(minimum, 4);
    let h = two_worker_prefix();
    let stale = stale_zero();
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Advance });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Close { stream: worker(0, 0, 0), good: true } });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Close { stream: worker(0, 0, 1), good: true } });
    let h = produce(c, h, 0, 0, 0);
    let final_message = gossip(h.last(), 0, 0, 0);
    let h = take(c, h, Action::Send { epoch: 0, shard: 0, observer: 0 });
    let h = take(c, h, Action::Receive { message: stale });
    assert(h.last().views[(0, 0, 0)] == Bound::Infinity);
    let h = take(c, h, Action::Finish { epoch: 0, observer: 0 });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Ack { id: 1 } });
    let h = take(c, h, Action::RestartObserver { observer: 0 });
    assert(h.last().views[(0, 0, 0)] == Bound::Finite(0));
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Advance });
    let h = take(c, h, Action::Receive { message: final_message });
    let h = take(c, h, Action::RestartCollector { epoch: 0, shard: 0 });
    assert(h.last().local[(0, 0)] == Bound::Finite(0));
    let h = produce(c, h, 0, 0, 1);
    h
}
pub proof fn theorem_rollback_through_produced_final_cut() -> (h: Seq<State>)
    ensures behavior(Settings { protocol: abs::Config { shards: 2, workers: 1 }, observers: 1 }, h),
        h.last().core.rolled.contains((0, 0)), !h.last().core.installed.contains((0, 1)),
        h.last().views[(0, 0, 0)] == Bound::Infinity, h.last().views[(0, 0, 1)] == Bound::Finite(0)
{
    let c = Settings { protocol: abs::Config { shards: 2, workers: 1 }, observers: 1 };
    reveal(step); reveal(abs::step); reveal_with_fuel(minimum, 3);
    let h = start(c);
    old::both_valid(0);
    assert(abs::read_max(view(c, h.last(), 0), old::both(0), 0, 0));
    assert(abs::read_max(view(c, h.last(), 0), old::both(0), 1, 0));
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Begin { id: 0, tx: old::both(0) } });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Install { id: 0, shard: 0 } });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Replicate { stream: worker(0, 0, 0), progress: 1 } });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Advance });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Close { stream: worker(0, 0, 0), good: true } });
    let h = take(c, h, Action::Core { observer: 0, action: abs::Action::Close { stream: worker(0, 1, 0), good: false } });
    let h = produce(c, h, 0, 0, 0);
    let h = produce(c, h, 0, 1, 0);
    let h = take(c, h, Action::Finish { epoch: 0, observer: 0 });
    assert(h.last().core.tx[0].vc[1] == 1);
    assert(view(c, h.last(), 0).wm[(0, 1)] == Bound::Finite(0));
    assert(!abs::below_wm(c.protocol, view(c, h.last(), 0), h.last().core.tx[0]));
    let h = take(c, h, Action::Rollback { id: 0, shard: 0, observer: 0 });
    h
}
} // verus!
