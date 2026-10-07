// Generated induction probe. Not part of the successful proof harness.
#![allow(non_snake_case)]
#[path="../../../src/protocol/TLAPSBench/mod.rs"] pub mod TLAPSBench;
use vstd::prelude::*;
use TLAPSBench::flash as model;
use TLAPSBench::flash_proof as proofs;
verus! {
proof fn init(c:model::Constants,home:int,data:int)
    requires model::valid_constants(c), c.nodes.contains(home), c.data.contains(data)
    ensures model::mem_data(model::initial(c,home,data))
{  }
proof fn preserve(s:model::LState,c:model::Constants,a:model::Action)
    requires model::valid_constants(c), proofs::typed(s,c), model::mem_data(s), model::enabled(s,c,a)
    ensures model::mem_data(model::apply(s,c,a))
{ reveal(model::enabled); reveal(model::apply); proofs::preserve_typed(s,c,a); }
}
