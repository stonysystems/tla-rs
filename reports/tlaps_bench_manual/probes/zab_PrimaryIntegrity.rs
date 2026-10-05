// Generated induction probe. Not part of the successful proof harness.
#![allow(non_snake_case)]
#[path="../../../src/protocol/TLAPSBench/mod.rs"] pub mod TLAPSBench;
use vstd::prelude::*;
use TLAPSBench::zab as model;
use TLAPSBench::zab_proof as proofs;
verus! {
proof fn init(c:model::Constants)
    requires model::valid_constants(c)
    ensures model::primary_integrity(model::initial(c),c)
{ proofs::initial_goals(c); }
proof fn preserve(s:model::LState,c:model::Constants,a:model::Action)
    requires model::valid_constants(c), true, model::primary_integrity(s,c), model::enabled(s,c,a)
    ensures model::primary_integrity(model::apply(s,c,a),c)
{ reveal(model::enabled); reveal(model::apply);  }
}
