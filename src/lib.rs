#![allow(unused_imports)]
#![allow(unused_attributes)]
// Logical/concrete identifiers retain their correspondence with the verified specs.
#![allow(non_snake_case)]
#![verifier::deprecated_postcondition_mut_ref_style(true)]
#![verus::trusted]
use vstd::prelude::*;

mod common;
mod generated;
mod implementation;
mod protocol;
mod services;
mod verus_extra;
mod native_runtime;

pub use common::native::io_s::WirePacket;
pub use native_runtime::{NativeReplica, RslParameters};
