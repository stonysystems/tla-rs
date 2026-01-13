#![allow(unused_imports)]
use super::temporal_s::*;
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {

pub open spec fn eventuallywithin(x: temporal, span:int, timefun:Map<int, int>) -> temporal
{
    stepmap(Map::new(|j: int| j == j, |j: int| sat(j, eventual(beforeabsolutetime(x, timefun[j] + span, timefun)))))
}

pub proof fn predicate_eventuallywithin(x: temporal, span: int, timefun: Map<int, int>)
ensures forall |i: int| #![trigger sat(i, eventuallywithin(x, span, timefun))] sat(i, eventuallywithin(x, span, timefun)) <==> sat(i, eventual(beforeabsolutetime(x, timefun[i] + span, timefun)))
{}

pub open spec fn alwayswithin(x:temporal, span:int, timefun:Map<int, int>) -> temporal
{
    stepmap(Map::new(|j: int| j == j, |j: int| sat(j, always(untilabsolutetime(x, timefun[j] + span, timefun)))))
}

pub proof fn predicate_alwayswithin(x: temporal, span: int, timefun:Map<int, int>)
ensures  forall |i: int| #![trigger sat(i, alwayswithin(x, span, timefun))] sat(i, alwayswithin(x, span, timefun)) <==> sat(i, always(untilabsolutetime(x, timefun[i] + span, timefun))) {}

pub open spec fn before(t:int, timefun:Map<int, int>) -> temporal {
    stepmap(Map::new(|i: int| i == i, |i: int| timefun[i] <= t))
}

pub proof fn predicate_before(t: int, timefun: Map<int, int>)
ensures  forall |i: int| #![trigger sat(i, before(t, timefun))] sat(i, before(t, timefun)) <==> timefun[i] <= t,
{}

pub open spec fn after(t:int, timefun:Map<int, int>) -> temporal
{
    stepmap(Map::new(|i: int| i == i, |i: int| timefun[i] >= t))
}

pub proof fn predicate_after(t: int, timefun: Map<int, int>)
ensures  forall |i: int| #![trigger sat(i, after(t, timefun))] sat(i, after(t, timefun)) <==> (timefun[i] >= t){}

pub open spec fn nextbefore(action:temporal, t:int, timefun:Map<int, int>) -> temporal
{
    and(action, next(before(t, timefun)))
}

pub open spec fn nextafter(action:temporal, t:int, timefun:Map<int, int>) -> temporal

{
    and(action, next(after(t, timefun)))
}

pub open spec fn eventuallynextwithin(action:temporal, span:int, timefun:Map<int, int>) -> temporal
{
    stepmap(Map::new(|i: int| i == i, |i: int| sat(i, eventual(nextbefore(action, timefun[i] + span, timefun)))))
}

pub proof fn predicate_eventuallynextwithin(action:temporal, span:int, timefun:Map<int, int>)
ensures  forall |i: int|  #![trigger sat(i, eventuallynextwithin(action, span, timefun))]
           sat(i, eventuallynextwithin(action, span, timefun)) <==> sat(i, eventual(nextbefore(action, timefun[i] + span, timefun)))
{}

pub open spec fn beforeabsolutetime(x:temporal, t:int, timefun:Map<int, int>) -> temporal
{
    and(x, before(t, timefun))
}


pub proof fn predicate_beforeabsolutetime(x:temporal, t:int, timefun:Map<int, int>)
ensures  forall |i: int|  #![trigger sat(i, beforeabsolutetime(x, t, timefun))]
           sat(i, beforeabsolutetime(x, t, timefun)) <==>
           sat(i, x) && timefun[i] <= t,
    {}



pub open spec fn untilabsolutetime(x:temporal, t:int, timefun:Map<int, int>) -> temporal
{
    temporal_imply(before(t, timefun), x)
}

pub proof fn predicate_untilabsolutetime(x:temporal, t:int, timefun:Map<int, int>)
ensures  forall |i: int|  #![trigger sat(i, untilabsolutetime(x, t, timefun))]
           sat(i, untilabsolutetime(x, t, timefun)) <==>
           timefun[i] <= t ==> sat(i, x)
           {}

pub open spec fn actionsWithin(i1:int, i2:int, x:temporal) -> Set<int>
{
    Set::new(|i: int| i1 <= i < i2 && sat(i, x))
}

pub open spec fn countWithin(i1:int, i2:int, x:temporal) -> nat
{
    actionsWithin(i1, i2, x).len()
}

} // !verus
