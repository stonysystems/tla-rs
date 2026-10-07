//! Diagnostic: try the original goals at the already extracted bad-index states.
use vstd::prelude::*;
use super::zookeeper as model;
use super::zookeeper_bad_index as trace;
use super::zookeeper_trace_ids as ids;
verus! {
pub proof fn integrity_at_concrete_state()
    ensures model::integrity(trace::state(197),trace::constants())
{ ids::geometry(); reveal(trace::state); reveal(trace::state_197); }
pub proof fn global_order_at_concrete_state()
    ensures model::global_primary_order(trace::state(191),trace::constants())
{ ids::geometry(); reveal(trace::state); reveal(trace::state_191); }
pub proof fn local_order_at_concrete_state()
    ensures model::local_primary_order(trace::state(191),trace::constants())
{ ids::geometry(); reveal(trace::state); reveal(trace::state_191); }
}
