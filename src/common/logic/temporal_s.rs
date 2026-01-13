#![allow(unused_imports)]
#![allow(non_camel_case_types)]
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {
    pub type temporal = Map<int, bool>;
    pub type Behavior<S> = Map<int, S>;

    pub open spec fn stepmap(f: Map<int, bool>) -> temporal {
        f
    }

    proof fn predicate_stempmap(f: Map<int, bool>)
        ensures forall |i:int| f.contains_key(i) ==> sat(i, stepmap(f)) =~= #[trigger] f[i]
    {}

    pub open spec fn sat(s:int, t:temporal) -> bool {
        t.contains_key(s) && t[s]
    }

    pub open spec fn and(x:temporal, y:temporal) -> temporal
    {
        stepmap(Map::new(|i:int| i == i, |i:int|  sat(i, x) && sat(i, y)))
    }

    proof fn predicate_and(x: temporal, y: temporal)
    ensures  forall |i:int| #![trigger sat(i, and(x, y))] sat(i, and(x, y)) == (sat(i, x) && sat(i, y))
    {}

    pub open spec fn or(x:temporal, y:temporal) -> temporal {
        stepmap(Map::new(|i:int| i == i, |i:int| sat(i, x) || sat(i, y)))
    }

    proof fn predicate_or(x: temporal, y: temporal)
    ensures  forall |i:int| #![trigger sat(i, or(x, y))] sat(i, or(x, y)) == (sat(i, x) || sat(i, y)) {}

    pub open spec fn temporal_imply(x:temporal, y:temporal) -> temporal
    {
        stepmap(Map::new(|i:int| i == i,  |i:int| sat(i, x) ==> sat(i, y)))
    }

    proof fn predicate_temporal_imply(x: temporal, y: temporal)
    ensures  forall |i:int| #![trigger sat(i, temporal_imply(x, y))] sat(i, temporal_imply(x, y)) == (sat(i, x) ==> sat(i, y))
    {}

    pub open spec fn equiv(x: temporal, y: temporal) -> temporal {
        stepmap(Map::new(|i:int| i == i,  |i:int| sat(i, x) <==> sat(i, y)))
    }

    proof fn predicate_equiv(x:temporal, y:temporal)
    ensures  forall |i:int| #![trigger sat(i, equiv(x, y))] sat(i, equiv(x, y)) == (sat(i, x) <==> sat(i, y))
    {
    }

    pub open spec fn not(x:temporal) -> temporal
    {
        stepmap(Map::new(|i:int| i == i,  |i:int| !sat(i, x)))
    }

    proof fn predicate_not(x: temporal)
    ensures  forall |i:int| #![trigger sat(i, not(x))] sat(i, not(x)) == !sat(i, x) {}

    pub open spec fn nextstep(i:int) -> int
    {
        i+1
    }


    pub open spec fn next(x:temporal) -> temporal
    {
        stepmap(Map::new(|i:int| i == i,  |i:int| sat(nextstep(i), x)))
    }

    proof fn predicate_next(x: temporal)
    ensures  forall |i:int| #![trigger sat(i, next(x))] sat(i, next(x)) == sat(nextstep(i), x)
    {}

    pub open spec fn always(x:temporal) -> temporal
    {
        stepmap(Map::new(|i:int| i == i, |i: int| forall |j:int| i <= j ==> sat(j, x)))
    }

    pub open spec fn eventual(x:temporal) -> temporal
    {
      stepmap(Map::new(|i: int| i == i, |i: int| exists |j: int| i <= j && sat(j, x)))
    }

} // !verus
