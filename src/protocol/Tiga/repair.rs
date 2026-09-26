//! Candidate recovery repair. This is a separate transition, not Algorithm 5.
//! It preserves reconstructed prefixes and can block if they are incompatible.
use super::types::*;
use super::recovery::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn payloads(batch: Map<int, Packet>) -> Map<int, Seq<Entry>> {
    Map::new(batch.dom(), |sh: int| batch[sh].log)
}
#[verifier::opaque]
pub open spec fn pool(logs: Map<int, Seq<Entry>>) -> Set<int> {
    logs.dom().map(|sh: int| ids(logs[sh])).flatten()
}
pub open spec fn id_sequence(log: Seq<Entry>) -> Seq<int> {
    log.map_values(|e: Entry| e.id)
}
pub open spec fn projection(txns: Map<int, Txn>, sh: int, order: Seq<int>) -> Seq<int> {
    order.filter(|id: int| txns[id].ops.dom().contains(sh))
}
#[verifier::opaque]
pub open spec fn valid_order(txns: Map<int, Txn>, logs: Map<int, Seq<Entry>>, order: Seq<int>) -> bool {
    &&& order.no_duplicates()
    &&& order.to_set() == pool(logs)
    &&& forall |sh: int| #[trigger] logs.dom().contains(sh) ==> {
        let local = projection(txns, sh, order);
        &&& local.len() >= logs[sh].len()
        &&& local.take(logs[sh].len() as int) == id_sequence(logs[sh])
    }
}
// A deterministic choice over the shared payloads. A concrete implementation
// can topologically sort the prefix constraints with a fixed tie-break rule.
// The choice does not inspect client completions or expected return values.
#[verifier::opaque]
pub open spec fn agreed_order(txns: Map<int, Txn>, logs: Map<int, Seq<Entry>>) -> Seq<int> {
    choose |order: Seq<int>| valid_order(txns, logs, order)
}
pub open spec fn stamped(order: Seq<int>) -> Seq<Entry> {
    Seq::new(order.len(), |i: int| Entry { id: order[i], ts: i + 1 })
}
#[verifier::opaque]
pub open spec fn local_log(txns: Map<int, Txn>, logs: Map<int, Seq<Entry>>, sh: int) -> Seq<Entry> {
    stamped(agreed_order(txns, logs)).filter(|e: Entry| txns[e.id].ops.dom().contains(sh))
}
pub open spec fn prefix_ids(old: Seq<Entry>, new: Seq<Entry>) -> bool {
    old.len() <= new.len() && forall |i: int| 0 <= i < old.len() ==> #[trigger] old[i].id == new[i].id
}
pub open spec fn can_repair(s: State, c: Constants, n: int, batch: Map<int, Packet>) -> bool {
    &&& valid_constants(c) && s.nodes.len() == count(c)
    &&& batch.dom().contains(shard(c, n))
    &&& member(c, n) && s.nodes[n].status is Rebuilt && am_leader(s, c, n)
    &&& reconstruction_reports(s, c, n, batch)
    &&& batch[shard(c, n)].log == s.nodes[n].log
    &&& exists |order: Seq<int>| valid_order(s.txns, payloads(batch), order)
}
pub open spec fn repair(s: State, c: Constants, n: int, batch: Map<int, Packet>) -> State {
    install(s, c, n, local_log(s.txns, payloads(batch), shard(c, n)))
}

pub proof fn lemma_projection(txns: Map<int, Txn>, sh: int, order: Seq<int>)
    ensures id_sequence(stamped(order).filter(|e: Entry| txns[e.id].ops.dom().contains(sh)))
        == projection(txns, sh, order),
    decreases order.len(),
{
    broadcast use vstd::seq_lib::group_seq_properties;
    if order.len() > 0 {
        lemma_projection(txns, sh, order.drop_last());
        assert(stamped(order).drop_last() =~= stamped(order.drop_last()));
        assert(stamped(order) =~= stamped(order.drop_last()).push(Entry { id: order.last(), ts: order.len() as int }));
        assert(order =~= order.drop_last().push(order.last()));
        let keep = |e: Entry| txns[e.id].ops.dom().contains(sh);
        stamped(order.drop_last()).lemma_filter_push(Entry { id: order.last(), ts: order.len() as int }, keep);
        order.drop_last().lemma_filter_push(order.last(), |id: int| txns[id].ops.dom().contains(sh));
        let prefix = stamped(order.drop_last()).filter(keep);
        let last = Entry { id: order.last(), ts: order.len() as int };
        assert(id_sequence(prefix.push(last)) =~= id_sequence(prefix).push(last.id));
        assert(id_sequence(stamped(order).filter(keep)) =~= projection(txns, sh, order));
    } else {
        assert(stamped(order) =~= Seq::<Entry>::empty());
        assert(id_sequence(stamped(order).filter(|e: Entry| txns[e.id].ops.dom().contains(sh))) =~= Seq::<int>::empty());
        assert(projection(txns, sh, order) =~= Seq::<int>::empty());
    }
}

pub proof fn lemma_repair_prefix(s: State, c: Constants, n: int, batch: Map<int, Packet>)
    requires can_repair(s, c, n, batch),
    ensures prefix_ids(s.nodes[n].log, repair(s, c, n, batch).nodes[n].log),
{
    reveal(agreed_order); reveal(valid_order); reveal(local_log);
    let logs = payloads(batch);
    let order = agreed_order(s.txns, logs);
    assert(valid_order(s.txns, logs, order));
    let sh = shard(c, n);
    lemma_projection(s.txns, sh, order);
    assert(logs.dom().contains(sh));
    assert(projection(s.txns, sh, order).take(logs[sh].len() as int) == id_sequence(logs[sh]));
    assert forall |i: int| 0 <= i < s.nodes[n].log.len()
        implies #[trigger] s.nodes[n].log[i].id == repair(s, c, n, batch).nodes[n].log[i].id by {
        assert(id_sequence(logs[sh])[i] == logs[sh][i].id);
    }
}

pub proof fn lemma_eval_ids(txns: Map<int, Txn>, sh: int, old: Seq<Entry>, new: Seq<Entry>)
    requires old.len() == new.len(), prefix_ids(old, new),
    ensures eval(txns, sh, old) == eval(txns, sh, new),
    decreases old.len(),
{
    if old.len() > 0 {
        assert(prefix_ids(old.drop_last(), new.drop_last()));
        lemma_eval_ids(txns, sh, old.drop_last(), new.drop_last());
        assert(old.last().id == new.last().id);
    }
}

/// A universal local guarantee, conditional on the collected reconstruction.
/// It does not assume that the rebuilt prefix itself preserves every commit.
pub proof fn lemma_repair_preserves_results(s: State, c: Constants, n: int, batch: Map<int, Packet>, i: int)
    requires can_repair(s, c, n, batch), 0 <= i < s.nodes[n].log.len(),
    ensures {
        let old = s.nodes[n].log;
        let new = repair(s, c, n, batch).nodes[n].log;
        &&& i < new.len()
        &&& new[i].id == old[i].id
        &&& return_op(eval(s.txns, shard(c, n), old.take(i)), s.txns[old[i].id].ops[shard(c, n)])
            == return_op(eval(s.txns, shard(c, n), new.take(i)), s.txns[new[i].id].ops[shard(c, n)])
    },
{
    lemma_repair_prefix(s, c, n, batch);
    let old = s.nodes[n].log;
    let new = repair(s, c, n, batch).nodes[n].log;
    assert(prefix_ids(old.take(i), new.take(i)));
    lemma_eval_ids(s.txns, shard(c, n), old.take(i), new.take(i));
}

pub proof fn lemma_same_payloads_same_order(txns: Map<int, Txn>, left: Map<int, Packet>, right: Map<int, Packet>)
    requires payloads(left) == payloads(right),
    ensures agreed_order(txns, payloads(left)) == agreed_order(txns, payloads(right)),
{}

} // verus!
