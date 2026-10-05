// Generated induction probe. Not part of the successful proof harness.
#![allow(non_snake_case)]
#[path="../../../src/protocol/TLAPSBench/mod.rs"] pub mod TLAPSBench;
use vstd::prelude::*;
use TLAPSBench::cahill as model;
use TLAPSBench::cahill_proof as proofs;
verus! {
proof fn init(c:model::Constants)
    requires model::valid_constants(c)
    ensures model::serializable(model::initial(c),c)
{ proofs::initial_serializable(c); }
proof fn preserve(s:model::LState,c:model::Constants,a:model::Action)
    requires model::valid_constants(c), true, model::serializable(s,c), model::enabled(s,c,a)
    ensures model::serializable(model::apply(s,c,a),c)
{ reveal(model::enabled); reveal(model::apply); reveal(model::commit); reveal(model::read); reveal(model::acquire);  }
}
