// Generated induction probe. Not part of the successful proof harness.
#![allow(non_snake_case)]
#[path="../../../src/protocol/TLAPSBench/mod.rs"] pub mod TLAPSBench;
use vstd::prelude::*;
use TLAPSBench::open_addressing as model;
use TLAPSBench::open_addressing_proof as proofs;
verus! {
proof fn init(c:model::Constants)
    requires model::valid_constants(c)
    ensures model::consistent(model::initial(c),c)
{  }
proof fn preserve(s:model::LState,c:model::Constants,a:model::Action)
    requires model::valid_constants(c), proofs::completion_inv(s,c) && model::sorted(s), model::consistent(s,c), model::enabled(s,c,a)
    ensures model::consistent(model::apply(s,c,a),c)
{ reveal(model::enabled); reveal(model::apply); reveal(model::thread_step); proofs::preserve_completion(s,c,a); proofs::preserve_sorted(s,c,a); }
}
