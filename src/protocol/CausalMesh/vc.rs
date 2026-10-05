//! Vector clocks of a fixed width: one counter per cache server.
use vstd::prelude::*;

verus! {

pub type VC = Seq<nat>;

pub open spec fn well_formed(n: nat, a: VC) -> bool { a.len() == n }

pub open spec fn zero(n: nat) -> VC { Seq::new(n, |i: int| 0nat) }

pub open spec fn le(a: VC, b: VC) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= b[i]
}

pub open spec fn max_nat(x: nat, y: nat) -> nat { if x >= y { x } else { y } }

pub open spec fn join(a: VC, b: VC) -> VC {
    Seq::new(a.len(), |i: int| max_nat(a[i], b[i]))
}

/// The version a server assigns: its clock with its own entry incremented.
pub open spec fn tick(a: VC, i: int) -> VC { a.update(i, a[i] + 1) }

pub proof fn lemma_le_refl(a: VC)
    ensures le(a, a)
{}

pub proof fn lemma_le_trans(a: VC, b: VC, c: VC)
    requires le(a, b), le(b, c)
    ensures le(a, c)
{
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i] <= c[i] by {
        assert(a[i] <= b[i] && b[i] <= c[i]);
    }
}

pub proof fn lemma_le_antisym(a: VC, b: VC)
    requires le(a, b), le(b, a)
    ensures a == b
{
    assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
        assert(a[i] <= b[i] && b[i] <= a[i]);
    }
    assert(a =~= b);
}

pub proof fn lemma_zero_le(n: nat, a: VC)
    requires a.len() == n
    ensures le(zero(n), a)
{}

/// Join is the least upper bound of equal-width clocks.
pub proof fn lemma_join_lub(a: VC, b: VC)
    requires a.len() == b.len()
    ensures
        join(a, b).len() == a.len(),
        le(a, join(a, b)),
        le(b, join(a, b)),
        forall|c: VC| le(a, c) && le(b, c) ==> #[trigger] le(join(a, b), c),
{
    let j = join(a, b);
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i] <= j[i] by {}
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] b[i] <= j[i] by {}
    assert forall|c: VC| le(a, c) && le(b, c) implies #[trigger] le(join(a, b), c) by {
        assert forall|i: int| 0 <= i < j.len() implies #[trigger] j[i] <= c[i] by {
            assert(a[i] <= c[i] && b[i] <= c[i]);
        }
    }
}

pub proof fn lemma_join_comm(a: VC, b: VC)
    requires a.len() == b.len()
    ensures join(a, b) == join(b, a)
{
    assert(join(a, b) =~= join(b, a));
}

pub proof fn lemma_join_le_absorb(a: VC, b: VC)
    requires le(a, b)
    ensures join(b, a) == b, join(a, b) == b
{
    assert(join(b, a) =~= b);
    assert(join(a, b) =~= b);
}

pub proof fn lemma_tick(a: VC, i: int)
    requires 0 <= i < a.len()
    ensures
        tick(a, i).len() == a.len(),
        le(a, tick(a, i)),
        tick(a, i)[i] == a[i] + 1,
        !le(tick(a, i), a),
{
    let t = tick(a, i);
    assert forall|j: int| 0 <= j < a.len() implies #[trigger] a[j] <= t[j] by {}
}

} // verus!
