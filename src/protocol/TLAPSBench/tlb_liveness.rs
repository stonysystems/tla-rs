//! Progress through TLB action locks and shootdown phases.
use vstd::prelude::*;
use super::tlb::*;
use super::tlb_proof as safety;
use super::tlb_temporal::*;
use super::temporal::Behavior;
verus! {
pub open spec fn nonblocking(pc: Pc) -> bool {
    pc != Pc::Boot && pc != Pc::InitiatorLockPmap && pc != Pc::InitiatorLockAction
    && pc != Pc::InitiatorWaitForQuiescence && pc != Pc::ResponderLockAction
}
pub proof fn local_enabled(s: LState, c: Constants, p: int)
    requires valid_constants(c), safety::inductive(s, c), c.processors.contains(p), nonblocking(s.procs[p].pc)
    ensures group_enabled(s, c, Group::Processor(p))
{
    reveal(enabled_step);
    let t = s.procs[p];
    let a = match t.pc {
        Pc::MainCheck => Step::MainCheck,
        Pc::MainChoose => Step::SkipInitiator,
        Pc::MainHandleInterrupt => Step::HandleInterrupt,
        Pc::InitiatorDeactivate => Step::BeginShootdown(choose |m: int| c.pmaps.contains(m)),
        Pc::InitiatorForSend => if t.todo.is_empty() { Step::ExitSend } else { Step::SelectCpu(t.todo.choose()) },
        Pc::InitiatorCheckCpuPmap => Step::CheckCpuPmap,
        Pc::InitiatorSetActionNeeded => Step::SetActionNeeded,
        Pc::InitiatorUnlockAction => Step::UnlockAction,
        Pc::InitiatorInterrupt => Step::InterruptCpu,
        Pc::InitiatorUpdateEntry => Step::UpdateEntry(choose |e: int| c.entries.contains(e)),
        Pc::InitiatorMaybeRefreshOwnTlb => Step::MaybeRefreshOwnTlb,
        Pc::InitiatorUnlockPmap => Step::UnlockPmap,
        Pc::InitiatorReactivate => Step::ReactivateInitiator,
        Pc::ResponderCheck => Step::CheckActionNeeded,
        Pc::ResponderDeactivate => Step::DeactivateResponder,
        Pc::ResponderRefreshTlb => Step::RefreshTlb,
        Pc::ResponderClearActionNeeded => Step::ClearActionNeeded,
        Pc::ResponderUnlockAction => Step::UnlockResponder,
        Pc::ResponderReactivate => Step::ReactivateResponder,
        _ => Step::MainCheck,
    };
    assert(enabled_step(s, c, p, a));
    enabled_group(s, c, p, a, Group::Processor(p));
}
pub proof fn first_take(b: Behavior<LState>, c: Constants, p: int, start: int, end: int) -> (k: int)
    requires fair_spec(b, c), c.processors.contains(p), 0 <= start <= end,
        group_taken(b[end], b[end+1], c, Group::Processor(p))
    ensures start <= k <= end, group_taken(b[k], b[k+1], c, Group::Processor(p)),
        same_control(b[start].procs[p], b[k].procs[p]),
        forall |i: int| start <= i < k ==> !#[trigger] group_taken(b[i], b[i+1], c, Group::Processor(p))
    decreases end-start
{
    if group_taken(b[start], b[start+1], c, Group::Processor(p)) { start }
    else {
        safety_at(b, c, start);
        quiet_step(b[start], b[start+1], c, p);
        let k = first_take(b, c, p, start+1, end);
        assert forall |i: int| start <= i < k implies !#[trigger] group_taken(b[i], b[i+1], c, Group::Processor(p)) by {
            if i > start { assert(start+1 <= i < k); }
        }
        k
    }
}
pub proof fn local_progress(b: Behavior<LState>, c: Constants, p: int, start: int) -> (k: int)
    requires fair_spec(b, c), c.processors.contains(p), start >= 0, nonblocking(b[start].procs[p].pc)
    ensures k >= start, same_control(b[start].procs[p], b[k].procs[p]),
        group_taken(b[k], b[k+1], c, Group::Processor(p))
{
    if !taken_after(b, c, Group::Processor(p), start) {
        assert forall |i: int| i >= start implies #[trigger] group_enabled(b[i], c, Group::Processor(p)) by {
            quiet_interval(b, c, p, start, i);
            safety_at(b, c, i);
            local_enabled(b[i], c, p);
        }
        weak_event(b, c, p, start);
    }
    let end = choose |k: int| k >= start && #[trigger] group_taken(b[k], b[k+1], c, Group::Processor(p));
    first_take(b, c, p, start, end)
}
pub open spec fn owner_rank(t: LProcessor) -> nat {
    match t.pc {
        Pc::InitiatorSetActionNeeded => 2, Pc::InitiatorUnlockAction => 1,
        Pc::ResponderRefreshTlb => 3, Pc::ResponderClearActionNeeded => 2,
        Pc::ResponderUnlockAction => 1, _ => 0,
    }
}
pub proof fn owner_step(s: LState, c: Constants, a: Action, p: int, q: int)
    requires safety::inductive(s, c), c.processors.contains(p), c.processors.contains(q),
        safety::owns_action(s.procs[p], p, q), enabled(s, c, a), apply(s, c, a).procs[q].actionlock
    ensures safety::owns_action(apply(s, c, a).procs[p], p, q),
        owner_rank(apply(s, c, a).procs[p]) <= owner_rank(s.procs[p]),
        handles(Group::Processor(p), a) ==> owner_rank(apply(s, c, a).procs[p]) < owner_rank(s.procs[p])
{
    reveal(step); reveal(enabled_step);
    assert(safety::local_inv(s, c, p));
    assert(safety::pair_inv(s, c, p, q));
    match a {
        Action::Step { p: r, step: t } => {
            assert(safety::local_inv(s, c, r));
            assert(safety::pair_inv(s, c, p, r));
            assert(safety::pair_inv(s, c, r, p));
        },
        _ => {},
    }
}
pub proof fn owner_until(b: Behavior<LState>, c: Constants, p: int, q: int, start: int, end: int)
    requires fair_spec(b, c), c.processors.contains(p), c.processors.contains(q), 0 <= start <= end,
        safety::owns_action(b[start].procs[p], p, q),
        forall |k: int| #![trigger b[k]] start <= k <= end ==> b[k].procs[q].actionlock
    ensures safety::owns_action(b[end].procs[p], p, q), owner_rank(b[end].procs[p]) <= owner_rank(b[start].procs[p])
    decreases end-start
{
    if end > start {
        owner_until(b, c, p, q, start, end-1);
        safety_at(b, c, end-1);
        reveal(next);
        let a = choose |a: Action| #[trigger] enabled(b[end-1], c, a) && b[end] == apply(b[end-1], c, a);
        owner_step(b[end-1], c, a, p, q);
    }
}
pub proof fn cannot_hold_action_forever(b: Behavior<LState>, c: Constants, p: int, q: int, start: int)
    requires fair_spec(b, c), c.processors.contains(p), c.processors.contains(q), start >= 0,
        safety::owns_action(b[start].procs[p], p, q),
        forall |k: int| #![trigger b[k]] k >= start ==> b[k].procs[q].actionlock
    ensures false
    decreases owner_rank(b[start].procs[p])
{
    weak_fairness(b, c, p);
    assert(fair_after(b, c, Group::Processor(p), start));
    let k = choose |k: int| k >= start && #[trigger] fair_event(b, c, Group::Processor(p), k);
    owner_until(b, c, p, q, start, k);
    safety_at(b, c, k);
    local_enabled(b[k], c, p);
    let a = take_witness(b[k], b[k+1], c, Group::Processor(p));
    owner_step(b[k], c, a, p, q);
    cannot_hold_action_forever(b, c, p, q, k+1);
}
pub proof fn action_released(b: Behavior<LState>, c: Constants, q: int, start: int)
    requires fair_spec(b, c), c.processors.contains(q), start >= 0
    ensures exists |k: int| #![trigger b[k]] k >= start && !b[k].procs[q].actionlock
{
    reveal(safety::action_ownership);
    if !(exists |k: int| #![trigger b[k]] k >= start && !b[k].procs[q].actionlock) {
        safety_at(b, c, start);
        let p = choose |p: int| #![trigger c.processors.contains(p)] c.processors.contains(p) && safety::owns_action(b[start].procs[p], p, q);
        cannot_hold_action_forever(b, c, p, q, start);
    }
}
pub proof fn waiting_lock_free_step(s: LState, c: Constants, a: Action, p: int)
    requires safety::inductive(s, c), c.processors.contains(p), enabled(s, c, a),
        s.procs[p].pc == Pc::InitiatorLockAction, !s.procs[s.procs[p].currentcpu].actionlock,
        apply(s, c, a).procs[p].pc == Pc::InitiatorLockAction
    ensures !apply(s, c, a).procs[apply(s, c, a).procs[p].currentcpu].actionlock
{
    reveal(step); reveal(enabled_step);
    let q = s.procs[p].currentcpu;
    assert(safety::local_inv(s, c, p));
    match a {
        Action::Step { p: r, step: t } => {
            assert(safety::local_inv(s, c, r));
            assert(safety::pair_inv(s, c, p, r));
            assert(safety::pair_inv(s, c, r, p));
        },
        _ => {},
    }
}
pub proof fn waiting_lock_free_until(b: Behavior<LState>, c: Constants, p: int, start: int, end: int)
    requires fair_spec(b, c), c.processors.contains(p), 0 <= start <= end,
        !b[start].procs[b[start].procs[p].currentcpu].actionlock,
        forall |k: int| #![trigger b[k]] start <= k <= end ==> b[k].procs[p].pc == Pc::InitiatorLockAction
    ensures !b[end].procs[b[end].procs[p].currentcpu].actionlock
    decreases end-start
{
    if end > start {
        waiting_lock_free_until(b, c, p, start, end-1);
        safety_at(b, c, end-1);
        reveal(next);
        let a = choose |a: Action| #[trigger] enabled(b[end-1], c, a) && b[end] == apply(b[end-1], c, a);
        waiting_lock_free_step(b[end-1], c, a, p);
    }
}
pub proof fn waiting_lock_progress(b: Behavior<LState>, c: Constants, p: int, start: int) -> (k: int)
    requires fair_spec(b, c), c.processors.contains(p), start >= 0,
        b[start].procs[p].pc == Pc::InitiatorLockAction
    ensures k >= start, same_control(b[start].procs[p], b[k].procs[p]),
        group_taken(b[k], b[k+1], c, Group::Processor(p))
{
    if !taken_after(b, c, Group::Processor(p), start) {
        assert forall |i: int| #![trigger b[i]] i >= start implies b[i].procs[p].pc == Pc::InitiatorLockAction by {
            quiet_interval(b, c, p, start, i);
        }
        safety_at(b, c, start);
        let q = b[start].procs[p].currentcpu;
        action_released(b, c, q, start);
        let free = choose |i: int| #![trigger b[i]] i >= start && !b[i].procs[q].actionlock;
        quiet_interval(b, c, p, start, free);
        weak_fairness(b, c, p);
        assert(fair_after(b, c, Group::Processor(p), free));
        let k = choose |k: int| k >= free && #[trigger] fair_event(b, c, Group::Processor(p), k);
        waiting_lock_free_until(b, c, p, free, k);
        safety_at(b, c, k);
        reveal(enabled_step);
        enabled_group(b[k], c, p, Step::AcquireActionLock, Group::Processor(p));
        assert(group_taken(b[k], b[k+1], c, Group::Processor(p)));
        assert(taken_after(b, c, Group::Processor(p), start));
    }
    let end = choose |k: int| k >= start && #[trigger] group_taken(b[k], b[k+1], c, Group::Processor(p));
    first_take(b, c, p, start, end)
}
pub open spec fn send_rank(t: LProcessor) -> nat {
    6*t.todo.len() + match t.pc {
        Pc::InitiatorCheckCpuPmap => 5nat, Pc::InitiatorLockAction => 4nat,
        Pc::InitiatorSetActionNeeded => 3, Pc::InitiatorUnlockAction => 2,
        Pc::InitiatorInterrupt => 1, _ => 0,
    }
}
pub proof fn sending_step(s: LState, c: Constants, p: int, a: Step)
    requires inductive(s, c), c.processors.contains(p), safety::sending(s.procs[p].pc), enabled_step(s, c, p, a)
    ensures step(s, c, p, a).procs[p].pc == Pc::InitiatorWaitForQuiescence
        || safety::sending(step(s, c, p, a).procs[p].pc)
            && send_rank(step(s, c, p, a).procs[p]) < send_rank(s.procs[p]),
        step(s, c, p, a).procs[p].writepmap == s.procs[p].writepmap
{
    todo_finite(s, c, p);
    reveal(step); reveal(enabled_step);
    assert(safety::local_inv(s, c, p));
    match a {
        Step::SelectCpu(q) => { vstd::iset::lemma_iset_remove_len(s.procs[p].todo, q); },
        _ => {},
    }
}
pub proof fn sending_done(b: Behavior<LState>, c: Constants, p: int, start: int) -> (end: int)
    requires fair_spec(b, c), c.processors.contains(p), start >= 0, safety::sending(b[start].procs[p].pc)
    ensures end >= start, b[end].procs[p].pc == Pc::InitiatorWaitForQuiescence,
        b[end].procs[p].writepmap == b[start].procs[p].writepmap
    decreases send_rank(b[start].procs[p])
{
    let k = if b[start].procs[p].pc == Pc::InitiatorLockAction {
        waiting_lock_progress(b, c, p, start)
    } else { local_progress(b, c, p, start) };
    safety_at(b, c, k);
    let a = take_witness(b[k], b[k+1], c, Group::Processor(p));
    match a {
        Action::Step { p: q, step: t } => { sending_step(b[k], c, p, t); },
        _ => {},
    }
    if b[k+1].procs[p].pc == Pc::InitiatorWaitForQuiescence { k+1 }
    else { sending_done(b, c, p, k+1) }
}
} // verus!
