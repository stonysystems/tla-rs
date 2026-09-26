//! A client-history specification, permitting completion of pending transactions.
use super::types::*;
use super::behavior::*;
use super::audit::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn serial_value(txns: Map<int, Txn>, sh: int, order: Seq<int>) -> int
    decreases order.len()
{
    if order.len() == 0 { 0 } else {
        let old = serial_value(txns, sh, order.drop_last());
        if txns[order.last()].ops.dom().contains(sh) {
            apply_op(old, txns[order.last()].ops[sh])
        } else { old }
    }
}

pub open spec fn serial_history(s: State, order: Seq<int>) -> bool {
    &&& order.no_duplicates()
    &&& order.to_set().subset_of(s.txns.dom())
    // Pending operations may be omitted or included once in a completion.
    &&& s.completed.dom().subset_of(order.to_set())
    &&& forall |i: int, j: int| #![trigger order[i], order[j]] 0 <= i < order.len() && 0 <= j < order.len()
        && s.completed.dom().contains(order[i])
        && s.completed[order[i]].tick < s.invoked[order[j]]
        ==> i < j
    &&& forall |i: int, sh: int| #![trigger serial_value(s.txns, sh, order.take(i))] 0 <= i < order.len() && s.completed.dom().contains(order[i])
        && s.txns[order[i]].ops.dom().contains(sh)
        ==> s.completed[order[i]].results[sh] == return_op(serial_value(s.txns, sh, order.take(i)),
            s.txns[order[i]].ops[sh])
}
pub open spec fn strictly_serializable(s: State) -> bool {
    exists |order: Seq<int>| serial_history(s, order)
}

pub proof fn lemma_three_orders(order: Seq<int>, ia: int, ir: int)
    requires order.no_duplicates(), order.to_set().subset_of(set![0int, 1int, 2int]),
        0 <= ia < ir < order.len(), order[ia] == 1, order[ir] == 2,
    ensures order == seq![1int, 2int] || order == seq![0int, 1int, 2int]
        || order == seq![1int, 0int, 2int] || order == seq![1int, 2int, 0int],
{
    broadcast use {group_set_lib_default, group_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    order.unique_seq_to_set();
    lemma_len_subset(order.to_set(), set![0int, 1int, 2int]);
    assert(order.len() <= 3);
    assert(2 <= order.len());
    assert(order.to_set().contains(order[0]));
    assert(order.to_set().contains(order[1]));
    assert(order[0] == 0 || order[0] == 1 || order[0] == 2);
    assert(order[1] == 0 || order[1] == 1 || order[1] == 2);
    if order.len() == 2 {
        assert(order =~= seq![1int, 2int]);
    } else {
        assert(order.to_set().contains(order[2]));
        assert(order[2] == 0 || order[2] == 1 || order[2] == 2);
        assert(order[0] != order[1] && order[0] != order[2] && order[1] != order[2]);
        if order[0] == 0 { assert(order =~= seq![0int, 1int, 2int]); }
        else if order[1] == 0 { assert(order =~= seq![1int, 0int, 2int]); }
        else { assert(order =~= seq![1int, 2int, 0int]); }
    }
}

pub proof fn lemma_history_impossible(s: State, order: Seq<int>)
    requires s.txns == bodies().insert(2, read_x()), s.completed.dom() == set![1int, 2int],
        s.completed[1].results[0] == 0, s.completed[2].results[0] == 11,
        s.completed[1].tick < s.invoked[2],
    ensures !serial_history(s, order),
{
    broadcast use {group_set_lib_default, group_set_properties, vstd::seq_lib::group_seq_properties, Seq::to_set_ensures};
    reveal_with_fuel(serial_value, 4);
    if serial_history(s, order) {
        assert(order.to_set().contains(1)); assert(order.to_set().contains(2));
        assert(order.contains(1)); assert(order.contains(2));
        let ia = order.lemma_contains_to_index(1);
        let ir = order.lemma_contains_to_index(2);
        assert(ia < ir);
        assert(s.txns.dom() =~= set![0int, 1int, 2int]);
        lemma_three_orders(order, ia, ir);
        assert(s.completed[1].results[0] == return_op(serial_value(s.txns, 0, order.take(ia)), s.txns[1].ops[0]));
        assert(s.completed[2].results[0] == return_op(serial_value(s.txns, 0, order.take(ir)), s.txns[2].ops[0]));
        if order == seq![0int, 1int, 2int] {
            assert(ia == 1);
            assert(order.take(ia) =~= seq![0int]);
        } else if order == seq![1int, 0int, 2int] {
            assert(ir == 2);
            assert(order.take(ir) =~= seq![1int, 0int]);
        } else {
            assert(ir == 1);
            assert(order.take(ir) =~= seq![1int]);
        }
        assert(false);
    }
}

/// An initialized execution violates the external strict-serializability spec.
pub proof fn theorem_published_recovery_counterexample() -> (trace: Seq<State>)
    ensures behavior(trace, config()), !strictly_serializable(trace.last()),
{
    let trace = lemma_bad_history();
    assert forall |order: Seq<int>| !#[trigger] serial_history(trace.last(), order) by {
        lemma_history_impossible(trace.last(), order);
    }
    trace
}

} // verus!
