// Generated induction probe. Not part of the successful proof harness.
#![allow(non_snake_case)]
#[path="../../../src/protocol/TLAPSBench/mod.rs"] pub mod TLAPSBench;
use vstd::prelude::*;
use TLAPSBench::etcd as model;
use TLAPSBench::etcd_election as proofs;
verus! {
proof fn init(c:model::Constants)
    requires model::valid_constants(c)
    ensures model::committed_is_durable(model::initial(c),c)
{  }
proof fn preserve(s:model::LState,c:model::Constants,a:model::Action)
    requires model::valid_constants(c), proofs::inductive(s,c), model::committed_is_durable(s,c), model::enabled(s,c,a)
    ensures model::committed_is_durable(model::apply(s,c,a),c)
{ reveal(model::enabled); reveal(model::apply); reveal(model::receive_enabled); reveal(model::receive); proofs::preserve_inductive(s,c,a); }
}
