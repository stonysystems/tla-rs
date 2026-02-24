// Exec helper functions for Raft protocol
// These implement exec versions of spec helper functions u64_inc/u64_dec

use crate::protocol::Raft::raft::*;
use vstd::prelude::*;

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

} // verus!
