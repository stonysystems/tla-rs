//! Reachable witnesses and rejected conflict transitions for the OCC machine.
use vstd::prelude::*;
use vstd::imap::IMap as Map;
use vstd::iset::ISet as Set;
use super::occ::*;
use super::occ_proof::*;

verus! {
pub open spec fn empty(c: Config) -> State {
    State { tx: Map::empty(), data: Map::new(|k: Key| key(c, k), |k: Key|
        Version { writer: None, value: c.base[k], serial: 0, ticket: 0, vc: zero(c) }),
        locks: Map::empty(), clocks: zero(c), installed: Set::empty(), serial: 0 }
}
pub proof fn start(c: Config) -> (h: Seq<State>)
    requires c.shards > 0, c.base.dom() == Set::new(|k: Key| key(c, k))
    ensures behavior(c, h), h == seq![empty(c)]
{
    let s = empty(c);
    assert(initial(c, s)); init_inv(c, s);
    seq![s]
}
pub proof fn take(c: Config, h: Seq<State>, a: Action) -> (z: Seq<State>)
    requires behavior(c, h), step(c, h.last(), effect(c, h.last(), a), a)
    ensures behavior(c, z), z == h.push(effect(c, h.last(), a))
{
    let z = h.push(effect(c, h.last(), a));
    assert(next(c, h.last(), z.last()));
    assert forall|i: int| 0 <= i < z.len()-1 implies #[trigger] next(c, z[i], z[i+1]) by {
        if i < h.len()-1 { assert(next(c, h[i], h[i+1])); }
    }
    z
}
pub open spec fn config() -> Config {
    Config { shards: 2, base: Map::new(|k: Key| 0 <= k.shard < 2, |k| 0int) }
}
pub open spec fn x() -> Key { Key { shard: 0, record: 0 } }
pub open spec fn y() -> Key { Key { shard: 1, record: 0 } }
// A blind writer can certify while another transaction's validation is pending.
pub proof fn write_one(c: Config, h: Seq<State>, id: int, k: Key, value: int) -> (z: Seq<State>)
    requires behavior(c, h), key(c, k), !h.last().tx.dom().contains(id), !h.last().locks.dom().contains(k)
    ensures behavior(c, z), z.last().tx[id].phase is Certified,
        z.last().data[k].writer == Some(id), z.last().data[k].value == value,
        z.last().data[k].serial == h.last().serial + 1,
        z.last().tx == h.last().tx.insert(id, z.last().tx[id]),
        z.last().locks == h.last().locks,
        z.last().clocks == h.last().clocks.insert(k.shard, h.last().clocks[k.shard] + 1),
        forall|sh: int| 0 <= sh < c.shards ==> #[trigger] z.last().tx[id].vc[sh] ==
            if sh == k.shard { h.last().clocks[sh] + 1 } else { 0 },
        forall|other: Key| key(c, other) && other != k ==> #[trigger] z.last().data[other] == h.last().data[other]
{
    reveal(step);
    let h = take(c, h, Action::Open { id });
    let h = take(c, h, Action::Write { id, key: k, value });
    let h = take(c, h, Action::Freeze { id });
    let h = take(c, h, Action::Lock { id, key: k });
    assert(h.last().tx[id].writes.dom().contains(k));
    let h = take(c, h, Action::GetClock { id, shard: k.shard });
    let h = take(c, h, Action::Check { id });
    let h = take(c, h, Action::Certify { id });
    assert(h.last().tx[id].writes.dom().contains(k));
    let z = take(c, h, Action::Install { id, shard: k.shard });
    z
}
pub proof fn theorem_speculative_read_and_commit() -> (h: Seq<State>)
    ensures behavior(config(), h), h.last().tx.dom().contains(0), h.last().tx.dom().contains(1), h.last().tx[1].phase is Certified,
        deps(h.last(), 1).contains(0), h.last().data[y()].value == 9,
        h.last().tx[0].vc[0] == 1, h.last().tx[0].vc[1] == 0,
        h.last().tx[1].vc[0] == 1, h.last().tx[1].vc[1] == 1,
        h.last().tx[0].phase is Certified,
        serializable(config(), h.last(), certified(h.last()))
{
    let c = config(); reveal(step);
    assert(c.base.dom() =~= Set::new(|k: Key| key(c, k)));
    let h = start(c);
    let h = write_one(c, h, 0, x(), 7);
    let h = take(c, h, Action::Open { id: 1 });
    let h = take(c, h, Action::Read { id: 1, key: x() });
    let h = take(c, h, Action::Write { id: 1, key: y(), value: 9 });
    let h = take(c, h, Action::Freeze { id: 1 });
    let h = take(c, h, Action::Lock { id: 1, key: y() });
    assert(h.last().tx[1].writes.dom().contains(y()));
    let h = take(c, h, Action::GetClock { id: 1, shard: 1 });
    let h = take(c, h, Action::Check { id: 1 });
    let h = take(c, h, Action::Validate { id: 1, index: 0 });
    let h = take(c, h, Action::Certify { id: 1 });
    assert(h.last().tx[1].writes.dom().contains(y()));
    let h = take(c, h, Action::Install { id: 1, shard: 1 });
    reveal_with_fuel(read_max, 2);
    assert(h.last().tx[1].reads[0].version.writer == Some(0));
    assert(deps(h.last(), 1).contains(0));
    behavior_inv(c, h, h.len()-1);
    certified_closed(c, h.last()); inv_serializable(c, h.last(), certified(h.last()));
    h
}
pub proof fn theorem_equal_value_does_not_hide_overwrite() -> (h: Seq<State>)
    ensures behavior(config(), h), h.last().data[x()].value == 0,
        h.last().tx[1].reads[0].version.value == 0,
        !validation(h.last(), 1, 0)
{
    let c = config(); reveal(step);
    assert(c.base.dom() =~= Set::new(|k: Key| key(c, k)));
    let h = start(c);
    let h = take(c, h, Action::Open { id: 1 });
    let h = take(c, h, Action::Read { id: 1, key: x() });
    let h = take(c, h, Action::Freeze { id: 1 });
    let h = take(c, h, Action::Check { id: 1 });
    let h = write_one(c, h, 0, x(), 0);
    behavior_inv(c, h, h.len()-1);
    super::occ_vectors::ticket_component(c, h.last(), x(), h.last().data[x()]);
    super::occ_vectors::ticket_component(c, h.last(), x(), h.last().tx[1].reads[0].version);
    assert(h.last().data[x()].ticket > 0);
    h
}
pub proof fn theorem_pending_writer_blocks_validation() -> (h: Seq<State>)
    ensures behavior(config(), h), !validation(h.last(), 1, 0),
        h.last().data[x()].vc == h.last().tx[1].reads[0].version.vc,
        h.last().locks[x()] == 0,
        h.last().tx.dom().contains(0), h.last().tx.dom().contains(1),
        h.last().tx[0].phase is Checking, h.last().tx[1].phase is Checking,
        h.last().tx[1].reads.len() == 1, h.last().tx[1].reads[0].key == x(),
        h.last().tx[1].writes.is_empty()
{
    let c = config(); reveal(step);
    assert(c.base.dom() =~= Set::new(|k: Key| key(c, k)));
    let h = start(c);
    let h = take(c, h, Action::Open { id: 1 });
    let h = take(c, h, Action::Read { id: 1, key: x() });
    let h = take(c, h, Action::Open { id: 0 });
    let h = take(c, h, Action::Write { id: 0, key: x(), value: 7 });
    let h = take(c, h, Action::Freeze { id: 0 });
    let h = take(c, h, Action::Lock { id: 0, key: x() });
    assert(h.last().tx[0].writes.dom().contains(x()));
    let h = take(c, h, Action::GetClock { id: 0, shard: 0 });
    let h = take(c, h, Action::Check { id: 0 });
    let h = take(c, h, Action::Freeze { id: 1 });
    let h = take(c, h, Action::Check { id: 1 });
    h
}
pub proof fn theorem_read_only_and_abort() -> (h: Seq<State>)
    ensures behavior(config(), h), h.last().tx[0].phase is Aborted,
        h.last().tx[1].phase is Certified, h.last().tx[1].writes.is_empty(),
        serializable(config(), h.last(), certified(h.last()))
{
    let c = config(); reveal(step);
    assert(c.base.dom() =~= Set::new(|k: Key| key(c, k)));
    let h = theorem_pending_writer_blocks_validation();
    let h = take(c, h, Action::Abort { id: 0 });
    let h = take(c, h, Action::Validate { id: 1, index: 0 });
    let h = take(c, h, Action::Certify { id: 1 });
    behavior_inv(c, h, h.len()-1);
    certified_closed(c, h.last()); inv_serializable(c, h.last(), certified(h.last()));
    h
}
pub open spec fn rollback_cut() -> Map<int, super::model::Bound> {
    Map::new(|sh: int| 0 <= sh < 2, |sh: int| super::model::Bound::Finite(if sh == 0 { 1 } else { 0 }))
}
pub proof fn theorem_vector_rollback_witness() -> (h: Seq<State>)
    ensures behavior(config(), h),
        super::occ_composition::vector_cut(config(), h.last(), rollback_cut()).contains(0),
        !super::occ_composition::vector_cut(config(), h.last(), rollback_cut()).contains(1),
        serializable(config(), h.last(), super::occ_composition::vector_cut(config(), h.last(), rollback_cut()))
{
    let h = theorem_speculative_read_and_commit();
    let cut = rollback_cut();
    super::occ_composition::theorem_vector_cut_serializable(config(), h, h.len()-1, cut);
    assert forall|sh: int| 0 <= sh < 2 implies super::model::covered(h.last().tx[0].vc[sh], #[trigger] cut[sh]) by {
        assert(sh == 0 || sh == 1);
    }
    assert(!super::model::covered(h.last().tx[1].vc[1], cut[1]));
    assert(super::occ_composition::vector_cut(config(), h.last(), cut).contains(0));
    assert(!super::occ_composition::vector_cut(config(), h.last(), cut).contains(1));
    let lost_writer = Map::new(|sh: int| 0 <= sh < 2, |sh: int| super::model::Bound::Finite(if sh == 0 { 0 } else { 1 }));
    super::occ_composition::theorem_vector_cut_serializable(config(), h, h.len()-1, lost_writer);
    assert(!super::model::covered(h.last().tx[0].vc[0], lost_writer[0]));
    assert(!super::model::covered(h.last().tx[1].vc[0], lost_writer[0]));
    assert(!super::occ_composition::vector_cut(config(), h.last(), lost_writer).contains(0));
    assert(!super::occ_composition::vector_cut(config(), h.last(), lost_writer).contains(1));
    h
}
/// A concrete pair of OCC and producer histories satisfies the composition
/// interface and reaches a durable two-shard commit.
pub proof fn theorem_occ_production_commit() -> (histories: (Seq<State>, Seq<super::production::State>))
    ensures behavior(config(), histories.0),
        super::production::behavior(super::production::Settings { protocol: super::model::Config { shards: 2, workers: 1 }, observers: 2 }, histories.1),
        super::occ_composition::correspondence(config(), histories.0.last(),
            super::production::Settings { protocol: super::model::Config { shards: 2, workers: 1 }, observers: 2 }, histories.1.last(), 0),
        histories.0.last().tx[0].phase is Certified, histories.1.last().core.acked.contains(0),
        serializable(config(), histories.0.last(), certified(histories.0.last()))
{
    let c = config(); reveal(step);
    assert(c.base.dom() =~= Set::new(|k: Key| key(c, k)));
    let h = start(c);
    let h = take(c, h, Action::Open { id: 0 });
    let h = take(c, h, Action::Write { id: 0, key: x(), value: 7 });
    let h = take(c, h, Action::Write { id: 0, key: y(), value: 9 });
    let h = take(c, h, Action::Freeze { id: 0 });
    let h = take(c, h, Action::Lock { id: 0, key: x() });
    let h = take(c, h, Action::Lock { id: 0, key: y() });
    assert(h.last().tx[0].writes.dom().contains(x()));
    let h = take(c, h, Action::GetClock { id: 0, shard: 0 });
    assert(h.last().tx[0].writes.dom().contains(y()));
    let h = take(c, h, Action::GetClock { id: 0, shard: 1 });
    let h = take(c, h, Action::Check { id: 0 });
    let h = take(c, h, Action::Certify { id: 0 });
    assert(h.last().tx[0].writes.dom().contains(x()));
    let h = take(c, h, Action::Install { id: 0, shard: 0 });
    assert(h.last().tx[0].writes.dom().contains(y()));
    let h = take(c, h, Action::Install { id: 0, shard: 1 });
    assert(h.last().tx[0].vc =~= super::scenarios::vec2(1, 1));
    let ph = super::production_scenarios::theorem_commit_through_production();
    let pc = super::production::Settings { protocol: super::model::Config { shards: 2, workers: 1 }, observers: 2 };
    assert(super::occ_composition::correspondence(c, h.last(), pc, ph.last(), 0));
    super::occ_composition::theorem_occ_and_watermark_safety(c, h, h.len()-1, pc, ph, ph.len()-1, 0);
    theorem_occ_serializable(c, h, h.len()-1);
    (h, ph)
}
} // verus!
