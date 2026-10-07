// Generated induction probe. Not part of the successful proof harness.
#![allow(non_snake_case)]
#[path="../../../src/protocol/TLAPSBench/mod.rs"] pub mod TLAPSBench;
use vstd::prelude::*;
use TLAPSBench::hashicorp as model;
use TLAPSBench::hashicorp_config as proofs;
verus! {
proof fn init(c:model::Constants)
    requires model::valid_constants(c)
    ensures model::leader_completeness(model::initial(c))
{  }
proof fn preserve(s:model::LState,c:model::Constants,a:model::Action)
    requires model::valid_constants(c), proofs::inductive(s,c), model::leader_completeness(s), model::enabled(s,c,a)
    ensures model::leader_completeness(model::apply(s,c,a))
{ reveal(model::enabled); reveal(model::protocol_apply); reveal(model::receive_enabled); reveal(model::receive); proofs::preserve_inductive(s,c,a); }
}
