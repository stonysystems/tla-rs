
use builtin::*;
use builtin_macros::*;
use vstd::*;

verus! {
    pub enum UpperBound {
        UpperBoundFinite{
            n:int,
        },
        UpperBoundInfinite{},
    }

    pub open spec fn LeqUpperBound(x:int, u:UpperBound) -> bool 
    {
        match u {
            UpperBound::UpperBoundFinite{n} => x <= n,
            UpperBound::UpperBoundInfinite {} => true,
        }
    }

    pub open spec fn LtUpperBound(x:int, u:UpperBound) -> bool
    {
        match u {
            UpperBound::UpperBoundFinite{n} => x < n,
            UpperBound::UpperBoundInfinite {} => true,
        }
    }

    pub open spec fn UpperBoundedAddition(x:int, y:int, u:UpperBound) -> int
    {
        if LtUpperBound(x+y, u) {
            x+y
        } else {
            u->n
        }
    }
}