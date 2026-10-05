//! Constructive reachability proofs. These are not model-checker runs.
use vstd::prelude::*;
use vstd::imap::IMap as Map;
use vstd::iset::ISet as Set;
use super::model::*;
use super::invariants::*;
use super::safety::*;

verus! {

pub open spec fn empty_state(c: Config) -> State {
    State { epoch: 0, tx: Map::empty(),
        clock: Map::new(|p: (nat, int)| shard(c, p.1), |p| 0nat),
        tail: Map::new(|k: Stream| stream(c, k), |k| 0nat),
        progress: Map::new(|k: Stream| stream(c, k), |k| 0nat),
        busy: Map::empty(), installed: Set::empty(), durable: Set::empty(),
        closed: Set::empty(), infinity: Set::empty(),
        wm: Map::new(|p: (nat, int)| shard(c, p.1), |p| Bound::Finite(0)),
        finalized: Set::empty(), acked: Set::empty(), replayed: Set::empty(), rolled: Set::empty() }
}
pub proof fn start(c: Config) -> (h: Seq<State>)
    requires valid(c)
    ensures behavior(c, h), h.len() == 1, h[0] == empty_state(c), inv(c, h.last())
{
    let s = empty_state(c);
    assert(initial(c, s));
    init_inv(c, s);
    seq![s]
}
pub proof fn take(c: Config, h: Seq<State>, a: Action) -> (z: Seq<State>)
    requires behavior(c, h), inv(c, h.last()), step(c, h.last(), effect(c, h.last(), a), a)
    ensures behavior(c, z), inv(c, z.last()), z == h.push(effect(c, h.last(), a))
{
    let s = h.last();
    let s2 = effect(c, s, a);
    step_inv(c, s, s2, a);
    assert(next(c, s, s2));
    let z = h.push(s2);
    assert forall|i: int| 0 <= i < z.len() - 1 implies #[trigger] next(c, z[i], z[i+1]) by {
        if i < h.len() - 1 { assert(next(c, h[i], h[i+1])); }
    }
    z
}
pub open spec fn vec2(a: nat, b: nat) -> Map<int, nat> {
    Map::new(|i: int| 0 <= i < 2, |i: int| if i == 0 { a } else { b })
}
pub open spec fn both(e: nat) -> Tx {
    Tx { epoch: e, vc: vec2(1, 1), part: Map::empty().insert(0, 0).insert(1, 0), deps: Set::empty() }
}
pub open spec fn one(e: nat, a: nat, b: nat, deps: Set<int>) -> Tx {
    Tx { epoch: e, vc: vec2(a, b), part: Map::empty().insert(0, 0), deps }
}
pub open spec fn k(e: nat, i: int) -> Stream { Stream { epoch: e, shard: i, worker: 0 } }

pub proof fn both_valid(e: nat)
    ensures tx_valid(Config { shards: 2, workers: 1 }, both(e))
{
    let c = Config { shards: 2, workers: 1 };
    let t = both(e);
    assert(t.vc.dom() =~= Set::new(|i: int| shard(c, i)));
    assert(t.part.dom().contains(0));
    assert forall|i: int| #[trigger] t.part.dom().contains(i) implies
        shard(c, i) && 0 <= t.part[i] < c.workers && t.vc[i] > 0 by {
        assert(i == 0 || i == 1);
    }
}

pub proof fn theorem_normal_commit_reachable() -> (h: Seq<State>)
    ensures behavior(Config { shards: 2, workers: 1 }, h), h.last().acked.contains(0),
        h.last().durable.contains((0, 0)), h.last().durable.contains((0, 1)),
        h.last().replayed.contains((0, 0)), h.last().replayed.contains((0, 1))
{
    let c = Config { shards: 2, workers: 1 };
    reveal(step);
    let h = start(c);
    assert(both(0).vc.dom() =~= Set::new(|i: int| shard(c, i)));
    both_valid(0);
    assert(read_max(h.last(), both(0), 0, 0));
    assert(read_max(h.last(), both(0), 1, 0));
    let h = take(c, h, Action::Begin { id: 0, tx: both(0) });
    let h = take(c, h, Action::Install { id: 0, shard: 0 });
    let h = take(c, h, Action::Install { id: 0, shard: 1 });
    let h = take(c, h, Action::Replicate { stream: k(0, 0), progress: 1 });
    let h = take(c, h, Action::Replicate { stream: k(0, 1), progress: 1 });
    let h = take(c, h, Action::Publish { epoch: 0, shard: 0, bound: Bound::Finite(1) });
    let h = take(c, h, Action::Publish { epoch: 0, shard: 1, bound: Bound::Finite(1) });
    let h = take(c, h, Action::Ack { id: 0 });
    let h = take(c, h, Action::Replay { id: 0, shard: 0 });
    let h = take(c, h, Action::Replay { id: 0, shard: 1 });
    h
}

pub proof fn theorem_partial_failure_reachable() -> (h: Seq<State>)
    ensures behavior(Config { shards: 2, workers: 1 }, h),
        h.last().installed.contains((0, 0)), !h.last().installed.contains((0, 1)),
        h.last().rolled.contains((0, 0)), h.last().rolled.contains((1, 0)),
        h.last().acked.contains(2), !h.last().acked.contains(0), !h.last().acked.contains(1),
        h.last().tx[2].epoch == 1
{
    let c = Config { shards: 2, workers: 1 };
    reveal(step);
    let h = start(c);
    assert(both(0).vc.dom() =~= Set::new(|i: int| shard(c, i)));
    both_valid(0);
    assert(read_max(h.last(), both(0), 0, 0));
    assert(read_max(h.last(), both(0), 1, 0));
    let h = take(c, h, Action::Begin { id: 0, tx: both(0) });
    // The install at shard 1 never arrives. Shard 0 can expose its version.
    let h = take(c, h, Action::Install { id: 0, shard: 0 });
    assert(one(0, 2, 1, Set::empty().insert(0)).vc.dom() =~= Set::new(|i: int| shard(c, i)));
    assert(tx_valid(c, one(0, 2, 1, Set::empty().insert(0))));
    assert(h.last().tx[0] == both(0));
    assert(one(0, 2, 1, Set::empty().insert(0)).deps.contains(0));
    assert(h.last().tx[0].vc[0] == 1);
    assert(read_max(h.last(), one(0, 2, 1, Set::empty().insert(0)), 0, 1));
    assert(read_max(h.last(), one(0, 2, 1, Set::empty().insert(0)), 1, 1));
    let h = take(c, h, Action::Begin { id: 1, tx: one(0, 2, 1, Set::empty().insert(0)) });
    let h = take(c, h, Action::Install { id: 1, shard: 0 });
    // Supply the installed transaction witnessing the replicated endpoint.
    assert(h.last().tx.dom().contains(1));
    assert(h.last().installed.contains((1, 0)));
    assert(h.last().tx[1] == one(0, 2, 1, Set::empty().insert(0)));
    let h = take(c, h, Action::Replicate { stream: k(0, 0), progress: 2 });
    let h = take(c, h, Action::Advance);
    // Healthy new-epoch work runs before the old epoch is finalized.
    assert(one(1, 1, 0, Set::empty()).vc.dom() =~= Set::new(|i: int| shard(c, i)));
    assert(tx_valid(c, one(1, 1, 0, Set::empty())));
    assert(read_max(h.last(), one(1, 1, 0, Set::empty()), 0, 0));
    assert(read_max(h.last(), one(1, 1, 0, Set::empty()), 1, 0));
    let h = take(c, h, Action::Begin { id: 2, tx: one(1, 1, 0, Set::empty()) });
    let h = take(c, h, Action::Install { id: 2, shard: 0 });
    assert(h.last().installed.contains((2, 0)));
    assert(h.last().tx.dom().contains(2));
    let h = take(c, h, Action::Replicate { stream: k(1, 0), progress: 1 });
    let h = take(c, h, Action::Publish { epoch: 1, shard: 0, bound: Bound::Finite(1) });
    let h = take(c, h, Action::Ack { id: 2 });
    let h = take(c, h, Action::Close { stream: k(0, 0), good: true });
    let h = take(c, h, Action::Close { stream: k(0, 1), good: false });
    let h = take(c, h, Action::Finalize { epoch: 0 });
    // The missing shard is an explicit counterexample to both final cuts.
    assert(endpoint(h.last(), k(0, 1)) == Bound::Finite(0));
    assert(!covered(h.last().tx[0].vc[1], endpoint(h.last(), k(0, 1))));
    assert(!covered(h.last().tx[1].vc[1], endpoint(h.last(), k(0, 1))));
    let h = take(c, h, Action::Rollback { id: 0, shard: 0 });
    assert(!covered(h.last().tx[1].vc[1], endpoint(h.last(), k(0, 1))));
    let h = take(c, h, Action::Rollback { id: 1, shard: 0 });
    h
}
} // verus!
