#![allow(unused_imports)]
use super::heuristics_i::*;
use super::temporal_s::*;
use crate::common::collections::maps2::*;

use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {
    ///////////////////
    // DEFINITIONS
    ///////////////////

    pub open spec fn eventualStep(start:int, x:temporal) -> (step:int)
    {
        let end = choose |end: int| TLe(start, end) && sat(end, x);
        end
    }

    pub proof fn lemma_eventualStep(start: int, x: temporal)
        requires sat(start, eventual(x))
        ensures  sat(eventualStep(start, x), x),
        TLe(start, eventualStep(start, x))
    {
        TemporalAssist();
    }

    /*
        this needs to be proven. It works in proof mode, but I've no idea why it just breaks if I'm trying to prove the exact same spec function
    */
    pub open spec fn earliestStepBetween(start:int, end:int, x:temporal) -> (pos:int)
        decreases end - start
            when sat(end, x) && TLe(start, end)
    {
        if (sat(start, x)) {
            start
        } else {
            earliestStepBetween(start + 1, end, x)
        }
    }

    /*
        EXAMPLE: Recursive spec with proofs to a lemma + spec
    */
    pub proof fn lemma_earliestStepBetween(start:int, end:int, x:temporal)
    requires sat(end, x),
            TLe(start, end)
    ensures  sat(earliestStepBetween(start, end, x), x),
            TLe(start, earliestStepBetween(start, end, x)),
            TLe(earliestStepBetween(start, end, x), end),
            forall |i: int| start <= i < earliestStepBetween(start, end, x) ==> !sat(i, x),
    decreases end - start
    {
        // predicate_sat
        if (sat(start, x)) {
            let pos = earliestStepBetween(start, end, x);
            assert(sat(pos, x));
            assert(TLe(start, pos));
            assert(TLe(pos, end));
            assert(forall |i: int| start <= i < pos ==> !sat(i, x));
        } else {
            lemma_earliestStepBetween(start+1, end, x);
            let pos = earliestStepBetween(start+1, end, x);
            assert(sat(pos, x));
            assert(TLe(start, pos));
            assert(TLe(pos, end));
            assert(forall |i: int| start <= i < pos ==> !sat(i, x));
        }
    }

    pub open spec fn earliestStep(start:int, x:temporal)-> int
        recommends sat(start, eventual(x))
    {
        earliestStepBetween(start, eventualStep(start, x), x)
    }

    pub proof fn lemma_earliestStep(start: int, x: temporal)
        requires sat(start, eventual(x))
        ensures  sat(earliestStep(start, x), x),
                TLe(start, earliestStep(start, x)),
                forall |i: int| start <= i < earliestStep(start, x) ==> !sat(i, x)
    {
        lemma_eventualStep(start, x);
        lemma_earliestStepBetween(start, eventualStep(start, x), x);
    }

    // ///////////////////
    // // LEMMAS
    // ///////////////////

    // // []A ==> A
    // // <>A <== A
    pub proof fn TemporalNow(i:int, x:temporal)
    ensures  sat(i, always(x)) ==> sat(i, x),
            sat(i, eventual(x)) <== sat(i, x)
    {
        TemporalAssist();
    }

    // // [][]A = []A
    // // <><>A = <>A
    pub proof fn TemporalIdempotent(i:int, x:temporal)
    ensures  sat(i, always(always(x))) == sat(i, always(x)),
            sat(i, eventual(eventual(x))) == sat(i, eventual(x))
    {
        TemporalAssist();
        /*
        reveal always();
        reveal eventual();
        */
    }

    // // <>[]A ==> []<>A
    pub proof fn TemporalEventuallyAlwaysImpliesAlwaysEventually(i:int, x:temporal)
    ensures  sat(i, eventual(always(x))) ==> sat(i, always(eventual(x)))
    {
        TemporalBlast();
    }

    // // <>!A = ![]A
    // // []!A = !<>A
    pub proof fn TemporalNot(i:int, x:temporal)
    ensures  sat(i, eventual(not(x))) <==> !sat(i, always(x)),
            sat(i, always(not(x))) <==> !sat(i, eventual(x))
    {
        TemporalAssist();
        /*
        reveal always();
        reveal eventual();
        */
    }

    // // [](A&&B) = []A && []B
    // // <>(A&&B) ==> <>A && <>B
    // // <>(A&&B) <== []A && <>B
    // // <>(A&&B) <== <>A && []B
    pub proof fn TemporalAnd(i:int, x:temporal, y:temporal)
        ensures  sat(i, always(and(x, y))) <==> sat(i, always(x)) && sat(i, always(y)),
                sat(i, eventual(and(x, y))) ==> sat(i, eventual(x)) && sat(i, eventual(y)),
                sat(i, eventual(and(x, y))) <== sat(i, always(x)) && sat(i, eventual(y)),
                sat(i, eventual(and(x, y))) <== sat(i, eventual(x)) && sat(i, always(y))
        {
            TemporalAssist();
            // reveal eventual();
            // reveal always();
        }

    // // [](A||B) <== []A || []B
    // // [](A||B) ==> []A || <>B
    // // [](A||B) ==> <>A || []B
    // // <>(A||B) = <>A || <>B
    pub proof fn TemporalOr(i:int, x:temporal, y:temporal)
    ensures  sat(i, always(or(x, y))) <== sat(i, always(x)) || sat(i, always(y)),
            sat(i, always(or(x, y))) ==> sat(i, always(x)) || sat(i, eventual(y)),
            sat(i, always(or(x, y))) ==> sat(i, eventual(x)) || sat(i, always(y)),
            sat(i, eventual(or(x, y))) <==> sat(i, eventual(x)) || sat(i, eventual(y))
        {
            TemporalAssist();
            // reveal eventual();
            // reveal always();
        }

    // // [](A==>B) ==> ([]A ==> []B)
    // // [](A==>B) ==> (<>A ==> <>B)
    // // [](A==>B) <== (<>A ==> []B)
    // // <>(A==>B) = ([]A ==> <>B)
    pub proof fn TemporalImply(i:int, x:temporal, y:temporal)
        ensures  sat(i, always(temporal_imply(x, y))) ==> (sat(i, always(x)) ==> sat(i, always(y))),
                sat(i, always(temporal_imply(x, y))) ==> (sat(i, eventual(x)) ==> sat(i, eventual(y))),
                sat(i, always(temporal_imply(x, y))) <== (sat(i, eventual(x)) ==> sat(i, always(y))),
                sat(i, eventual(temporal_imply(x, y))) <==> (sat(i, always(x)) ==> sat(i, eventual(y)))
        {
            TemporalAssist();
            // reveal eventual();
            // reveal always();
        }

    pub proof fn TemporalAlways(i:int, x:temporal)
        requires forall |j: int| i <= j ==> sat(j, x)
        ensures  sat(i, always(x))
        {
            TemporalAssist();
            assert(forall |j: int| TLe(i, j) ==> sat(j, x));
        }

    pub proof fn TemporalEventually(i1:int, i2:int, x:temporal)
        requires i1 <= i2,
                sat(i2, x)
        ensures sat(i1, eventual(x))
        {
            TemporalAssist();
        }

    pub proof fn ValidAlways(i:int, x:temporal)
        requires (forall |j:int| sat(j, x))
        ensures  sat(i, always(x))
        {
            TemporalAssist();
        }

    pub proof fn ValidImply(i:int, x:temporal, y:temporal)
        requires forall |j:int| sat(j, x) ==> sat(j, y)
        ensures  sat(i, always(x)) ==> sat(i, always(y)),
                sat(i, eventual(x)) ==> sat(i, eventual(y))
        {
            TemporalAssist();
        }

    pub proof fn ValidEquiv(i:int, x:temporal, y:temporal)
        requires forall |j:int| sat(j, x) <==> sat(j, y)
        ensures  sat(i, always(x)) <==> sat(i, always(y)),
            sat(i, eventual(x)) <==> sat(i, eventual(y))
        {
            TemporalAssist();
        // reveal eventual();
        // reveal always();
        }

    pub proof fn TemporalDeduceFromAlways(i:int, j:int, x:temporal)
        requires i <= j,
                sat(i, always(x))
        ensures sat(j, x)
        {
            TemporalAssist();
            assert(TLe(i, j));
        }

    pub proof fn TemporalDeduceFromEventual(i:int, x:temporal) -> (j:int)
        requires sat(i, eventual(x))
        ensures  i <= j,
        sat(j, x)
        {
            TemporalAssist();
            let j = choose |z: int| TLe(i, z) && sat(z, x);
            return j;
        }

    pub proof fn Lemma_EventuallyAlwaysImpliesLaterEventuallyAlways(
        i:int,
        j:int,
        x:temporal
    )
    requires i <= j,
            sat(i, eventual(always(x)))
    ensures  sat(j, eventual(always(x)))
    {
    TemporalAssist();
    let k = choose |k: int| #![auto] TLe(i, k) && sat(k, always(x));
    let l = if k > j {k} else {j};
    assert(TLe(k, l) && TLe(j, l));
    }

    pub proof fn Lemma_AlwaysImpliesLaterAlways(
        i:int,
        j:int,
        x:temporal
    )
        requires i <= j
        ensures  sat(i, always(x)) ==> sat(j, always(x))
    {
        TemporalAssist();
        assert(TLe(i, j));
    }

    pub proof fn Lemma_EventuallyNowButNotNextMeansNow(x:temporal, i:int)
        ensures sat(i, eventual(x)) && !sat(i+1, eventual(x)) ==> sat(i, x)
    {
        TemporalAssist();
    }

    pub proof fn Lemma_EventuallyImpliesEarlierEventually(
        i:int,
        j:int,
        x:temporal
        )
        requires i <= j
        ensures  sat(j, eventual(x)) ==> sat(i, eventual(x))
    {
        TemporalAssist();
        assert(TLe(i, j));
    }

    pub proof fn TemporalAlwaysEventualImpliesAlwaysEventualWithDifferentStartPoint(i:int, j:int, x:temporal)
        ensures  sat(i, always(eventual(x))) ==> sat(j, always(eventual(x)))
    {
        TemporalAssist();

        if sat(i, always(eventual(x))) && i > j {
            assert(sat(i, eventual(x)));
        }
    }
} // !verus
