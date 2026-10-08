//! Finite quiescence loops under the source's per-processor weak fairness.
use vstd::prelude::*;
use super::tlb::*;
use super::tlb_proof as safety;
use super::tlb_temporal::*;
use super::tlb_liveness::*;
use super::temporal::Behavior;
verus! {
pub open spec fn waits(s: LState, p: int, m: int) -> bool {
    s.procs[p].pc == Pc::InitiatorWaitForQuiescence && s.procs[p].writepmap == m
}
pub open spec fn waiting_tail(b: Behavior<LState>, p: int, m: int, start: int) -> bool {
    forall |k: int| k >= start ==> #[trigger] waits(b[k], p, m)
}
pub open spec fn late(t: LProcessor) -> bool {
    !t.active || t.pc == Pc::MainHandleInterrupt || t.pc == Pc::ResponderCheck || t.pc == Pc::ResponderDeactivate
}
pub open spec fn active_rank(t: LProcessor) -> nat {
    match t.pc {
        Pc::MainCheck => 5, Pc::MainChoose => 4, Pc::InitiatorDeactivate => 3,
        Pc::MainHandleInterrupt => 2, Pc::ResponderCheck => 1, _ => 0,
    }
}
pub proof fn target_step(s: LState, c: Constants, a: Action, p: int, q: int, m: int)
    requires safety::inductive(s, c), enabled(s, c, a), c.processors.contains(p), c.processors.contains(q), p != q,
        waits(s, p, m), waits(apply(s, c, a), p, m), s.procs[q].pc != Pc::Boot
    ensures apply(s, c, a).procs[q].pc != Pc::Boot,
        apply(s, c, a).procs[q].userpmap == s.procs[q].userpmap,
        s.procs[q].userpmap == m ==> (
            (late(s.procs[q]) ==> late(apply(s, c, a).procs[q]))
            && (s.procs[q].pc == Pc::ResponderLockAction ==> apply(s, c, a).procs[q].pc == Pc::ResponderLockAction)
            && (s.procs[q].active && handles(Group::Processor(q), a) ==>
                (!apply(s, c, a).procs[q].active || active_rank(apply(s, c, a).procs[q]) < active_rank(s.procs[q]))
                && (late(s.procs[q]) && !apply(s, c, a).procs[q].active ==> apply(s, c, a).procs[q].pc == Pc::ResponderLockAction)))
{
    reveal(step); reveal(enabled_step);
    assert(safety::local_inv(s, c, p)); assert(safety::local_inv(s, c, q));
    assert(safety::pair_inv(s, c, p, q));
    match a {
        Action::Step { p: r, step: t } => { assert(safety::local_inv(s, c, r)); },
        _ => {},
    }
}
pub proof fn target_until(b: Behavior<LState>, c: Constants, p: int, q: int, m: int, start: int, end: int)
    requires fair_spec(b, c), c.processors.contains(p), c.processors.contains(q), p != q, 0 <= start <= end,
        waiting_tail(b, p, m, start), b[start].procs[q].pc != Pc::Boot
    ensures b[end].procs[q].pc != Pc::Boot, b[end].procs[q].userpmap == b[start].procs[q].userpmap,
        b[start].procs[q].userpmap == m ==> (
            (late(b[start].procs[q]) ==> late(b[end].procs[q]))
            && (b[start].procs[q].pc == Pc::ResponderLockAction ==> b[end].procs[q].pc == Pc::ResponderLockAction))
    decreases end-start
{
    if end > start {
        target_until(b, c, p, q, m, start, end-1);
        safety_at(b, c, end-1);
        reveal(next);
        let a = choose |a: Action| #[trigger] enabled(b[end-1], c, a) && b[end] == apply(b[end-1], c, a);
        target_step(b[end-1], c, a, p, q, m);
    }
}
pub proof fn active_nonblocking(s: LState, c: Constants, q: int)
    requires safety::inductive(s, c), c.processors.contains(q), s.procs[q].active, s.procs[q].pc != Pc::Boot
    ensures nonblocking(s.procs[q].pc)
{ assert(safety::local_inv(s, c, q)); }
pub proof fn active_event(b: Behavior<LState>, c: Constants, p: int, q: int, m: int, start: int) -> (k: int)
    requires fair_spec(b, c), c.processors.contains(p), c.processors.contains(q), p != q, start >= 0,
        waiting_tail(b, p, m, start), b[start].procs[q].pc != Pc::Boot,
        b[start].procs[q].userpmap == m, b[start].procs[q].active
    ensures k >= start, b[k+1].procs[q].pc != Pc::Boot, b[k+1].procs[q].userpmap == m,
        late(b[start].procs[q]) ==> late(b[k+1].procs[q]),
        !b[k+1].procs[q].active || active_rank(b[k+1].procs[q]) < active_rank(b[start].procs[q]),
        late(b[start].procs[q]) && !b[k+1].procs[q].active ==> b[k+1].procs[q].pc == Pc::ResponderLockAction
{
    safety_at(b, c, start);
    active_nonblocking(b[start], c, q);
    let k = local_progress(b, c, q, start);
    safety_at(b, c, k);
    let a = take_witness(b[k], b[k+1], c, Group::Processor(q));
    target_step(b[k], c, a, p, q, m);
    k
}
pub proof fn active_finishes(b: Behavior<LState>, c: Constants, p: int, q: int, m: int, start: int) -> (end: int)
    requires fair_spec(b, c), c.processors.contains(p), c.processors.contains(q), p != q, start >= 0,
        waiting_tail(b, p, m, start), b[start].procs[q].pc != Pc::Boot,
        b[start].procs[q].userpmap == m, b[start].procs[q].active
    ensures end >= start, !b[end].procs[q].active, b[end].procs[q].userpmap == m,
        late(b[start].procs[q]) ==> b[end].procs[q].pc == Pc::ResponderLockAction
    decreases active_rank(b[start].procs[q])
{
    let k = active_event(b, c, p, q, m, start);
    assert(waiting_tail(b, p, m, k+1));
    assert(b[k+1].procs[q].userpmap == m);
    if !b[k+1].procs[q].active { k+1 }
    else {
        assert(active_rank(b[k+1].procs[q]) < active_rank(b[start].procs[q]));
        let end = active_finishes(b, c, p, q, m, k+1);
        assert(late(b[start].procs[q]) ==> late(b[k+1].procs[q]));
        end
    }
}
pub open spec fn quiet_tail(b: Behavior<LState>, q: int, m: int, start: int) -> bool {
    forall |k: int| #![trigger b[k]] k >= start ==> !b[k].procs[q].active || b[k].procs[q].userpmap != m
}
pub proof fn target_quiet(b: Behavior<LState>, c: Constants, p: int, q: int, m: int, start: int)
    requires fair_spec(b, c), c.processors.contains(p), c.processors.contains(q), p != q, start >= 0,
        waiting_tail(b, p, m, start), b[start].procs[q].pc != Pc::Boot
    ensures exists |end: int| end >= start && #[trigger] quiet_tail(b, q, m, end)
{
    if b[start].procs[q].userpmap != m {
        assert forall |k: int| #![trigger b[k]] k >= start implies b[k].procs[q].userpmap != m by {
            target_until(b, c, p, q, m, start, k);
        }
        assert(quiet_tail(b, q, m, start));
    } else {
        let inactive = if b[start].procs[q].active { active_finishes(b, c, p, q, m, start) } else { start };
        if quiet_tail(b, q, m, inactive) {
            assert(exists |end: int| end >= start && #[trigger] quiet_tail(b, q, m, end));
        } else {
            let awake = choose |k: int| #![trigger b[k]] k >= inactive && b[k].procs[q].active && b[k].procs[q].userpmap == m;
            safety_at(b, c, inactive);
            assert(safety::local_inv(b[inactive], c, q));
            target_until(b, c, p, q, m, inactive, awake);
            let stopped = active_finishes(b, c, p, q, m, awake);
            assert forall |k: int| #![trigger b[k]] k >= stopped implies !b[k].procs[q].active by {
                target_until(b, c, p, q, m, stopped, k);
                safety_at(b, c, k);
                assert(safety::local_inv(b[k], c, q));
            }
            assert(quiet_tail(b, q, m, stopped));
        }
    }
}
pub proof fn quiescence_progress(b: Behavior<LState>, c: Constants, p: int, start: int) -> (k: int)
    requires fair_spec(b, c), c.processors.contains(p), start >= 0, b[start].procs[p].pc == Pc::InitiatorWaitForQuiescence
    ensures k >= start, same_control(b[start].procs[p], b[k].procs[p]),
        group_taken(b[k], b[k+1], c, Group::Processor(p))
{
    if !taken_after(b, c, Group::Processor(p), start) {
        let m = b[start].procs[p].writepmap;
        assert forall |i: int| i >= start implies #[trigger] waits(b[i], p, m) by {
            quiet_interval(b, c, p, start, i);
        }
        safety_at(b, c, start);
        let todo = b[start].procs[p].todo;
        let free = if todo.is_empty() { start }
        else {
            let q = todo.choose();
            assert(safety::pair_inv(b[start], c, p, q));
            target_quiet(b, c, p, q, m, start);
            choose |end: int| end >= start && #[trigger] quiet_tail(b, q, m, end)
        };
        assert forall |i: int| i >= free implies #[trigger] group_enabled(b[i], c, Group::Processor(p)) by {
            quiet_interval(b, c, p, start, i);
            safety_at(b, c, i);
            reveal(enabled_step);
            let t = if todo.is_empty() { Step::ExitQuiescence } else { Step::WaitQuiescence(todo.choose()) };
            enabled_group(b[i], c, p, t, Group::Processor(p));
        }
        weak_event(b, c, p, free);
        let j = choose |j: int| j >= free && #[trigger] group_taken(b[j], b[j+1], c, Group::Processor(p));
        assert(taken_after(b, c, Group::Processor(p), start));
    }
    let end = choose |k: int| k >= start && #[trigger] group_taken(b[k], b[k+1], c, Group::Processor(p));
    first_take(b, c, p, start, end)
}
pub proof fn quiescence_step(s: LState, c: Constants, p: int, a: Step)
    requires inductive(s, c), c.processors.contains(p), s.procs[p].pc == Pc::InitiatorWaitForQuiescence, enabled_step(s, c, p, a)
    ensures step(s, c, p, a).procs[p].pc == Pc::InitiatorUpdateEntry
        || step(s, c, p, a).procs[p].pc == Pc::InitiatorWaitForQuiescence
            && step(s, c, p, a).procs[p].todo.len() < s.procs[p].todo.len(),
        step(s, c, p, a).procs[p].writepmap == s.procs[p].writepmap
{
    todo_finite(s, c, p);
    reveal(step); reveal(enabled_step);
    match a { Step::WaitQuiescence(q) => { vstd::iset::lemma_iset_remove_len(s.procs[p].todo, q); }, _ => {} }
}
pub proof fn quiescence_done(b: Behavior<LState>, c: Constants, p: int, start: int) -> (end: int)
    requires fair_spec(b, c), c.processors.contains(p), start >= 0, b[start].procs[p].pc == Pc::InitiatorWaitForQuiescence
    ensures end >= start, b[end].procs[p].pc == Pc::InitiatorUpdateEntry,
        b[end].procs[p].writepmap == b[start].procs[p].writepmap
    decreases b[start].procs[p].todo.len()
{
    let k = quiescence_progress(b, c, p, start);
    safety_at(b, c, k);
    let a = take_witness(b[k], b[k+1], c, Group::Processor(p));
    match a { Action::Step { p: q, step: t } => { quiescence_step(b[k], c, p, t); }, _ => {} }
    if b[k+1].procs[p].pc == Pc::InitiatorUpdateEntry { k+1 }
    else { quiescence_done(b, c, p, k+1) }
}
} // verus!
