// Compiles only against a vstd that tracks hash-table well-formedness
// (verus-lang/verus#3494). scripts/verus_cfg.sh uses it to decide whether to
// pass `--cfg vstd_hash_wf`.
#[allow(unused_imports)]
use vstd::std_specs::hash::{hash_map_wf, hash_set_wf};
use vstd::prelude::*;

verus! {
}
