//! Hash-table well-formedness across Verus versions.
//!
//! Since verus-lang/verus#3494, vstd only describes what a `HashMap` or
//! `HashSet` operation does when the table is well formed (each entry stored
//! where its key's hash says): `new` builds well-formed tables, `insert` and
//! `remove` keep them well formed, and `clone` does so when the key type
//! clones to equal values. Older vstd releases assumed it of every table and
//! have no name for it.
//!
//! Code that must verify with both carries `hash_set_ok` / `hash_map_ok`
//! instead. The build passes `--cfg vstd_hash_wf` when the vstd in use has the
//! predicates (see scripts/verus_cfg.sh); without it they are `true`.
use std::collections::{HashMap, HashSet};
use vstd::prelude::*;

verus! {

/// The set is well formed (vstd's `hash_set_wf`).
#[cfg(vstd_hash_wf)]
pub open spec fn hash_set_ok<K, S>(s: &HashSet<K, S>) -> bool {
    vstd::std_specs::hash::hash_set_wf(s)
}

/// Older vstd releases assume every set is well formed.
#[cfg(not(vstd_hash_wf))]
pub open spec fn hash_set_ok<K, S>(s: &HashSet<K, S>) -> bool {
    true
}

/// The map is well formed (vstd's `hash_map_wf`).
#[cfg(vstd_hash_wf)]
pub open spec fn hash_map_ok<K, V, S>(m: &HashMap<K, V, S>) -> bool {
    vstd::std_specs::hash::hash_map_wf(m)
}

/// Older vstd releases assume every map is well formed.
#[cfg(not(vstd_hash_wf))]
pub open spec fn hash_map_ok<K, V, S>(m: &HashMap<K, V, S>) -> bool {
    true
}

} // verus!
