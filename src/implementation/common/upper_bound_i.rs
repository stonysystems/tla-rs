use crate::protocol::common::upper_bound::*;
use vstd::prelude::*;

verus! {
    pub enum CUpperBound {
        CUpperBoundFinite { n: int },
        CUpperBoundInfinite,
    }

    impl CUpperBound {
        pub open spec fn valid(self) -> bool {
            match self {
                CUpperBound::CUpperBoundFinite { n } => true,
                CUpperBound::CUpperBoundInfinite => true,
            }
        }

        pub open spec fn abstractable(self) -> bool {
            true
        }

        pub open spec fn view(self) -> UpperBound {
            match self {
                CUpperBound::CUpperBoundFinite { n } => UpperBound::UpperBoundFinite { n },
                CUpperBound::CUpperBoundInfinite => UpperBound::UpperBoundInfinite{},
            }
        }

        pub open spec fn CLeqUpperBound(x: int, u:CUpperBound) -> bool {
            match u {
                CUpperBound::CUpperBoundFinite{n} => x<= n,
                CUpperBound::CUpperBoundInfinite => true
            }
        }

    }
}
