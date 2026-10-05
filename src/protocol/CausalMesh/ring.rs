//! Ring arithmetic for propagation chains over servers 0..n-1.
//! A version created at `origin` is at server `at(n, origin, h)` after h hops.
use vstd::prelude::*;

verus! {

pub open spec fn server(n: nat, s: int) -> bool { 0 <= s < n }

pub open spec fn at(n: nat, origin: int, hop: nat) -> int { (origin + hop) % (n as int) }

pub open spec fn succ(n: nat, s: int) -> int { (s + 1) % (n as int) }

pub proof fn lemma_at_server(n: nat, origin: int, hop: nat)
    requires n > 0, server(n, origin)
    ensures server(n, at(n, origin, hop))
{
    vstd::arithmetic::div_mod::lemma_mod_bound(origin + hop, n as int);
}

pub proof fn lemma_at_zero(n: nat, origin: int)
    requires n > 0, server(n, origin)
    ensures at(n, origin, 0) == origin
{
    vstd::arithmetic::div_mod::lemma_small_mod(origin as nat, n);
}

pub proof fn lemma_at_succ(n: nat, origin: int, hop: nat)
    requires n > 0, server(n, origin)
    ensures at(n, origin, hop + 1) == succ(n, at(n, origin, hop))
{
    let m = n as int;
    let x = origin + hop;
    assert((x + 1) % m == ((x % m) + 1) % m) by (nonlinear_arith) requires m > 0 {
        vstd::arithmetic::div_mod::lemma_add_mod_noop(x, 1, m);
        vstd::arithmetic::div_mod::lemma_mod_twice(1, m);
    }
}

/// After n more hops a version is back at the same server.
pub proof fn lemma_at_period(n: nat, origin: int, hop: nat)
    requires n > 0, server(n, origin)
    ensures at(n, origin, hop + n) == at(n, origin, hop)
{
    let m = n as int;
    vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(origin + hop, m);
}

/// Every server occurs among any n consecutive hops.
pub proof fn lemma_at_covers(n: nat, origin: int, start: nat, s: int)
    requires n > 0, server(n, origin), server(n, s)
    ensures exists|h: nat| start <= h < start + n && #[trigger] at(n, origin, h) == s
{
    let m = n as int;
    let base = (origin + start) % m;
    let d: int = if s >= base { s - base } else { s - base + m };
    let h = (start + d) as nat;
    assert(0 <= d < m);
    assert(at(n, origin, h) == s) by {
        vstd::arithmetic::div_mod::lemma_add_mod_noop(origin + start, d, m);
        vstd::arithmetic::div_mod::lemma_small_mod(d as nat, n);
        if s >= base {
            vstd::arithmetic::div_mod::lemma_small_mod(s as nat, n);
        } else {
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(s, m);
            vstd::arithmetic::div_mod::lemma_small_mod(s as nat, n);
        }
        vstd::arithmetic::div_mod::lemma_mod_bound(origin + start, m);
    }
}

} // verus!
