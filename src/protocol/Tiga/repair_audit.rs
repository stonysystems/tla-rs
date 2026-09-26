//! Regression proof for the separate prefix-preserving recovery candidate.
use super::types::*;
use super::recovery::*;
use super::repair::*;
use super::audit::*;
use super::behavior::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn example_logs() -> Map<int, Seq<Entry>> {
    map![0int => seq![a()], 1int => seq![b()]]
}
pub proof fn lemma_example_pool()
    ensures pool(example_logs()) == set![0int, 1int],
{
    broadcast use {group_set_lib_default, group_set_properties, Set::lemma_set_map_insert_commute,
        vstd::seq_lib::lemma_seq_contains, vstd::seq_lib::lemma_seq_contains_after_push,
        vstd::seq_lib::lemma_seq_empty_contains_nothing, Seq::to_set_ensures};
    reveal(pool);
    let logs = example_logs();
    assert(logs.dom() =~= set![0int, 1int]);
    assert(seq![a()].to_set() =~= set![a()]);
    assert(seq![b()].to_set() =~= set![b()]);
    assert(ids(logs[0]) =~= set![1int]);
    assert(ids(logs[1]) =~= set![0int]);
    assert(logs.dom().map(|sh: int| ids(logs[sh])) =~= set![set![1int], set![0int]]);
    let sets = logs.dom().map(|sh: int| ids(logs[sh]));
    assert(sets.contains(set![0int]));
    assert(sets.contains(set![1int]));
    sets.lemma_flatten_contains(0);
    sets.lemma_flatten_contains(1);
    assert(pool(logs) =~= set![0int, 1int]);
}

pub proof fn lemma_example_valid()
    ensures valid_order(bodies(), example_logs(), seq![1int, 0int]),
{
    broadcast use {group_set_lib_default, group_set_properties,
        vstd::seq_lib::lemma_seq_contains, vstd::seq_lib::lemma_seq_contains_after_push,
        vstd::seq_lib::lemma_seq_empty_contains_nothing, Seq::to_set_ensures};
    lemma_example_pool();
    reveal(valid_order);
    reveal_with_fuel(Seq::filter, 3);
    let logs = example_logs();
    assert(logs.dom() =~= set![0int, 1int]);
    assert(seq![1int, 0int].to_set() =~= set![0int, 1int]);
    assert(projection(bodies(), 0, seq![1int, 0int]) =~= seq![1int, 0int]);
    assert(projection(bodies(), 1, seq![1int, 0int]) =~= seq![0int]);
    assert(id_sequence(logs[0]) =~= seq![1int]);
    assert(id_sequence(logs[1]) =~= seq![0int]);
    assert(projection(bodies(), 0, seq![1int, 0int]).take(1) =~= seq![1int]);
    assert(projection(bodies(), 1, seq![1int, 0int]).take(1) =~= seq![0int]);
}

pub proof fn lemma_example_order()
    ensures agreed_order(bodies(), example_logs()) == seq![1int, 0int],
        local_log(bodies(), example_logs(), 0) == seq![Entry { id: 1, ts: 1 }, Entry { id: 0, ts: 2 }],
        local_log(bodies(), example_logs(), 1) == seq![Entry { id: 0, ts: 2 }],
{
    broadcast use {group_set_lib_default, group_set_properties,
        vstd::seq_lib::lemma_seq_contains, vstd::seq_lib::lemma_seq_contains_after_push,
        vstd::seq_lib::lemma_seq_empty_contains_nothing, Seq::to_set_ensures};
    reveal(valid_order);
    reveal_with_fuel(Seq::filter, 3);
    lemma_example_pool();
    reveal(agreed_order); reveal(local_log);
    lemma_example_valid();
    let order = agreed_order(bodies(), example_logs());
    assert(valid_order(bodies(), example_logs(), order));
    order.unique_seq_to_set();
    assert(order.len() == 2);
    assert(order.to_set().contains(order[0]));
    assert(order.to_set().contains(order[1]));
    assert(order[0] != order[1]);
    assert(order[0] == 0 || order[0] == 1);
    assert(order[1] == 0 || order[1] == 1);
    assert(projection(bodies(), 0, order) =~= order);
    assert(example_logs().dom().contains(0));
    assert(projection(bodies(), 0, order).take(1) == id_sequence(example_logs()[0]));
    assert(id_sequence(example_logs()[0]) =~= seq![1int]);
    assert(order[0] == 1);
    assert(order =~= seq![1int, 0int]);
    assert(stamped(order) =~= seq![Entry { id: 1, ts: 1 }, Entry { id: 0, ts: 2 }]);
    assert(local_log(bodies(), example_logs(), 0) =~= stamped(order));
    assert(local_log(bodies(), example_logs(), 1) =~= seq![Entry { id: 0, ts: 2 }]);
}

/// Reach the same recovery input, then apply the candidate transition.
/// This proves this regression is fixed, not whole-protocol safety.
pub proof fn theorem_import_regression_fixed() -> (witness: (Seq<State>, State))
    ensures behavior(witness.0, config()),
        can_repair(witness.0.last(), config(), 1,
            map![0int => rebuilt(1, 1, a()), 1int => rebuilt(4, 1, b())]),
        witness.1 == repair(witness.0.last(), config(), 1,
            map![0int => rebuilt(1, 1, a()), 1int => rebuilt(4, 1, b())]),
        witness.1.nodes[1].status is Normal,
        witness.1.nodes[1].log == seq![Entry { id: 1, ts: 1 }, Entry { id: 0, ts: 2 }],
        witness.1.completed[1].results[0] == 0,
        return_op(eval(witness.1.txns, 0, witness.1.nodes[1].log.take(0)), witness.1.txns[1].ops[0]) == 0,
        eval(witness.1.txns, 0, witness.1.nodes[1].log) == 10,
{
    broadcast use {group_set_lib_default, group_set_properties,
        vstd::seq_lib::lemma_seq_contains, vstd::seq_lib::lemma_seq_contains_after_push,
        vstd::seq_lib::lemma_seq_empty_contains_nothing, Seq::to_set_ensures};
    let t = lemma_reported_trace();
    let t = lemma_rebuild(t, 1, a());
    let t = lemma_rebuild(t, 4, b());
    let batch = map![0int => rebuilt(1, 1, a()), 1int => rebuilt(4, 1, b())];
    assert(payloads(batch) =~= example_logs());
    assert(batch.dom() =~= Set::range(0, 2));
    lemma_example_pool();
    lemma_example_order();
    lemma_example_valid();
    assert(valid_order(t.last().txns, payloads(batch), seq![1int, 0int]));
    assert(count(config()) == 6) by (compute);
    assert(shard(config(), 1) == 0) by (compute);
    assert(batch.dom().contains(0));
    assert(reconstruction_reports(t.last(), config(), 1, batch));
    assert(can_repair(t.last(), config(), 1, batch));
    lemma_repair_preserves_results(t.last(), config(), 1, batch, 0);
    let after = repair(t.last(), config(), 1, batch);
    reveal_with_fuel(eval, 3);
    (t, after)
}

} // verus!
