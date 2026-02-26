// Exec helper functions for Raft protocol
// These implement exec versions of spec helper functions u64_inc/u64_dec

use crate::protocol::Raft::raft::*;
use vstd::prelude::*;
use vstd::set::*;

verus! {

pub exec fn Cu64_inc(x: &u64) -> (result: u64)
requires
    *x < u64::MAX,
ensures
    result == u64_inc(*x),
{
    *x + 1
}

pub exec fn Cu64_dec(x: &u64) -> (result: u64)
requires
    *x > 0,
ensures
    result == u64_dec(*x),
{
    *x - 1
}

/// Helper proof: membership in a set implies membership in its map image.
pub proof fn lemma_set_map_contains(s: Set<u64>, x: u64)
requires
    s.contains(x),
ensures
    s.map(|v: u64| v as int).contains(x as int),
{
}

/// Helper proof: non-membership in a set implies non-membership in its map image.
pub proof fn lemma_set_map_not_contains(s: Set<u64>, x: u64)
requires
    !s.contains(x),
ensures
    !s.map(|v: u64| v as int).contains(x as int),
{
    let f = |v: u64| v as int;
    if s.map(f).contains(x as int) {
        let z = choose |z: u64| s.contains(z) && (z as int) == (x as int);
        assert(z == x);
        assert(false);
    }
}

} // verus!
