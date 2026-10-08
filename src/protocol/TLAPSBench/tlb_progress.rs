//! The benchmark's NonStarvation theorem, using its exact fairness groups.
use vstd::prelude::*;
use super::tlb::*;
use super::tlb_proof as safety;
use super::tlb_temporal::*;
use super::tlb_liveness::*;
use super::tlb_quiescence::*;
use super::temporal::Behavior;
verus! {
pub open spec fn update_rank(pc: Pc) -> nat {
    match pc { Pc::InitiatorUpdateEntry => 3, Pc::InitiatorMaybeRefreshOwnTlb => 2, Pc::InitiatorUnlockPmap => 1, _ => 0 }
}
pub proof fn update_step(s: LState, c: Constants, p: int, a: Step)
    requires safety::inductive(s, c), c.processors.contains(p), safety::updated(s.procs[p].pc), enabled_step(s, c, p, a)
    ensures step(s, c, p, a).procs[p].writepmap == s.procs[p].writepmap,
        (step(s, c, p, a).procs[p].pc == Pc::InitiatorReactivate && !step(s, c, p, a).plock[s.procs[p].writepmap])
        || (safety::updated(step(s, c, p, a).procs[p].pc)
            && update_rank(step(s, c, p, a).procs[p].pc) < update_rank(s.procs[p].pc))
{ reveal(enabled_step); reveal(step); }
pub proof fn updated_done(b: Behavior<LState>, c: Constants, p: int, start: int) -> (end: int)
    requires fair_spec(b, c), c.processors.contains(p), start >= 0, safety::updated(b[start].procs[p].pc)
    ensures end >= start, b[end].procs[p].pc == Pc::InitiatorReactivate,
        b[end].procs[p].writepmap == b[start].procs[p].writepmap, !b[end].plock[b[start].procs[p].writepmap]
    decreases update_rank(b[start].procs[p].pc)
{
    let k = local_progress(b, c, p, start);
    safety_at(b, c, k);
    let a = take_witness(b[k], b[k+1], c, Group::Processor(p));
    match a { Action::Step { p: q, step: t } => { update_step(b[k], c, p, t); }, _ => {} }
    if b[k+1].procs[p].pc == Pc::InitiatorReactivate { k+1 }
    else { updated_done(b, c, p, k+1) }
}
pub proof fn owner_done(b: Behavior<LState>, c: Constants, p: int, start: int) -> (end: int)
    requires fair_spec(b, c), c.processors.contains(p), start >= 0, safety::pmap_owner(b[start].procs[p].pc)
    ensures end >= start, b[end].procs[p].pc == Pc::InitiatorReactivate,
        b[end].procs[p].writepmap == b[start].procs[p].writepmap, !b[end].plock[b[start].procs[p].writepmap]
{
    let sent = if safety::sending(b[start].procs[p].pc) { sending_done(b, c, p, start) } else { start };
    let waited = if b[sent].procs[p].pc == Pc::InitiatorWaitForQuiescence { quiescence_done(b, c, p, sent) } else { sent };
    updated_done(b, c, p, waited)
}
pub proof fn pmap_released(b: Behavior<LState>, c: Constants, m: int, start: int)
    requires fair_spec(b, c), c.pmaps.contains(m), start >= 0
    ensures exists |k: int| #![trigger b[k]] k >= start && !b[k].plock[m]
{
    reveal(pmap_ownership);
    if b[start].plock[m] {
        safety_at(b, c, start);
        let p = choose |p: int| c.processors.contains(p) && #[trigger] owns_pmap(b[start], p, m);
        let end = owner_done(b, c, p, start);
        assert(!b[end].plock[m]);
    } else { assert(!b[start].plock[m]); }
}
pub open spec fn blocked(pc: Pc) -> bool {
    pc == Pc::Boot || pc == Pc::InitiatorLockPmap || pc == Pc::ResponderLockAction
}
pub open spec fn blocked_group(pc: Pc, p: int) -> Group {
    match pc { Pc::Boot => Group::Boot(p), Pc::InitiatorLockPmap => Group::Pmap(p), _ => Group::Responder(p) }
}
pub proof fn blocked_enabled(s: LState, c: Constants, p: int, m: int)
    requires safety::inductive(s, c), c.processors.contains(p), c.pmaps.contains(m), !s.plock[m], blocked(s.procs[p].pc),
        s.procs[p].pc == Pc::InitiatorLockPmap ==> s.procs[p].writepmap == m,
        s.procs[p].pc == Pc::ResponderLockAction ==> s.procs[p].userpmap == m
    ensures group_enabled(s, c, blocked_group(s.procs[p].pc, p))
{
    reveal(enabled_step);
    let t = match s.procs[p].pc { Pc::Boot => Step::Boot(m), Pc::InitiatorLockPmap => Step::AcquirePmapLock, _ => Step::AcquireResponderLock };
    enabled_group(s, c, p, t, blocked_group(s.procs[p].pc, p));
}
pub proof fn blocked_progress(b: Behavior<LState>, c: Constants, p: int, start: int) -> (k: int)
    requires fair_spec(b, c), c.processors.contains(p), start >= 0, blocked(b[start].procs[p].pc)
    ensures k >= start, same_control(b[start].procs[p], b[k].procs[p]),
        group_taken(b[k], b[k+1], c, Group::Processor(p))
{
    if !taken_after(b, c, Group::Processor(p), start) {
        safety_at(b, c, start);
        let pc = b[start].procs[p].pc;
        let g = blocked_group(pc, p);
        let m = if pc == Pc::Boot { choose |m: int| c.pmaps.contains(m) }
            else if pc == Pc::InitiatorLockPmap { b[start].procs[p].writepmap } else { b[start].procs[p].userpmap };
        assert forall |i: int| i >= 0 implies #[trigger] enabled_after(b, c, g, i) by {
            let tail = if i >= start { i } else { start };
            pmap_released(b, c, m, tail);
            let free = choose |j: int| #![trigger b[j]] j >= tail && !b[j].plock[m];
            quiet_interval(b, c, p, start, free);
            safety_at(b, c, free);
            blocked_enabled(b[free], c, p, m);
            assert(group_enabled(b[free], c, g));
        }
        strong_fairness(b, c, p);
        assert(strong_fair(b, c, g));
        assert(taken_after(b, c, g, start));
        let k = choose |k: int| k >= start && #[trigger] group_taken(b[k], b[k+1], c, g);
        let a = take_witness(b[k], b[k+1], c, g);
        assert(handles(Group::Processor(p), a));
        record_take(b[k], b[k+1], c, a, Group::Processor(p));
        assert(taken_after(b, c, Group::Processor(p), start));
    }
    let end = choose |k: int| k >= start && #[trigger] group_taken(b[k], b[k+1], c, Group::Processor(p));
    first_take(b, c, p, start, end)
}
pub open spec fn progress_rank(pc: Pc) -> nat {
    match pc {
        Pc::MainChoose => 12, Pc::InitiatorDeactivate => 11, Pc::InitiatorLockPmap => 10,
        Pc::InitiatorReactivate | Pc::ResponderUnlockAction => 8,
        Pc::MainHandleInterrupt | Pc::ResponderReactivate => 7,
        Pc::ResponderCheck => 6, Pc::ResponderDeactivate => 5, Pc::ResponderLockAction => 4,
        Pc::ResponderRefreshTlb => 3, Pc::Boot => 1, Pc::MainCheck | Pc::ResponderClearActionNeeded => 0,
        _ => 9,
    }
}
pub proof fn progress_step(s: LState, c: Constants, p: int, a: Step)
    requires safety::inductive(s, c), c.processors.contains(p), !makes_progress(s, p), !safety::pmap_owner(s.procs[p].pc), enabled_step(s, c, p, a)
    ensures progress_rank(step(s, c, p, a).procs[p].pc) < progress_rank(s.procs[p].pc)
{ reveal(enabled_step); reveal(step); }
pub proof fn progress_at(b: Behavior<LState>, c: Constants, p: int, start: int) -> (end: int)
    requires fair_spec(b, c), c.processors.contains(p), start >= 0
    ensures end >= start, makes_progress(b[end], p)
    decreases progress_rank(b[start].procs[p].pc)
{
    if makes_progress(b[start], p) { start }
    else if safety::pmap_owner(b[start].procs[p].pc) {
        let end = owner_done(b, c, p, start);
        progress_at(b, c, p, end)
    } else {
        let k = if blocked(b[start].procs[p].pc) { blocked_progress(b, c, p, start) } else { local_progress(b, c, p, start) };
        safety_at(b, c, k);
        let a = take_witness(b[k], b[k+1], c, Group::Processor(p));
        match a { Action::Step { p: q, step: t } => { progress_step(b[k], c, p, t); }, _ => {} }
        progress_at(b, c, p, k+1)
    }
}
pub open spec fn progress_after(b: Behavior<LState>, p: int, start: int) -> bool {
    exists |end: int| end >= start && #[trigger] makes_progress(b[end], p)
}
pub open spec fn nonstarvation(b: Behavior<LState>, c: Constants) -> bool {
    forall |p: int, start: int| c.processors.contains(p) && start >= 0 ==> #[trigger] progress_after(b, p, start)
}
// ivy_examples_tlb_Liveness: Spec => NonStarvation.
pub proof fn liveness(b: Behavior<LState>, c: Constants)
    requires fair_spec(b, c)
    ensures nonstarvation(b, c)
{
    assert forall |p: int, start: int| c.processors.contains(p) && start >= 0 implies #[trigger] progress_after(b, p, start) by {
        let end = progress_at(b, c, p, start);
        assert(makes_progress(b[end], p));
    }
}
} // verus!
