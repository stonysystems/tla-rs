// Generated induction probe. Not part of the successful proof harness.
#![allow(non_snake_case)]
#[path="../../../src/protocol/TLAPSBench/mod.rs"] pub mod TLAPSBench;
use vstd::prelude::*;
use TLAPSBench::mongodb as model;
use TLAPSBench::mongodb_proof as proofs;
verus! {
proof fn init(c:model::Constants,catalog:IMap<int,int>)
    requires model::valid_constants(c),model::valid_catalog(c,catalog)
    ensures model::snapshot_isolation(model::initial(c,catalog),c)
{ proofs::initial_snapshot_isolation(c,catalog); }
proof fn preserve(s:model::LState,c:model::Constants,a:model::Action)
    requires model::valid_constants(c), model::single_write_per_key(s,c), model::snapshot_isolation(s,c), model::enabled(s,c,a),model::single_write_per_key(model::apply(s,c,a),c)
    ensures model::snapshot_isolation(model::apply(s,c,a),c)
{ reveal(model::enabled); reveal(model::apply);  }
}
