use vstd::prelude::*;
use super::tlb::*;
use super::temporal::Behavior;
verus! {
pub open spec fn sending(pc: Pc) -> bool {
    pc == Pc::InitiatorForSend || selected(pc)
}
pub open spec fn selected(pc: Pc) -> bool {
    pc == Pc::InitiatorCheckCpuPmap || pc == Pc::InitiatorLockAction || pc == Pc::InitiatorSetActionNeeded
    || pc == Pc::InitiatorUnlockAction || pc == Pc::InitiatorInterrupt
}
pub open spec fn pmap_owner(pc: Pc) -> bool {
    sending(pc) || pc == Pc::InitiatorWaitForQuiescence || updated(pc)
}
pub open spec fn updated(pc: Pc) -> bool {
    pc == Pc::InitiatorUpdateEntry || pc == Pc::InitiatorMaybeRefreshOwnTlb || pc == Pc::InitiatorUnlockPmap
}
pub open spec fn writer_action_owner(pc: Pc) -> bool {
    pc == Pc::InitiatorSetActionNeeded || pc == Pc::InitiatorUnlockAction
}
pub open spec fn responder_action_owner(pc: Pc) -> bool {
    pc == Pc::ResponderRefreshTlb || pc == Pc::ResponderClearActionNeeded || pc == Pc::ResponderUnlockAction
}
pub open spec fn owns_action(t: LProcessor, p: int, q: int) -> bool {
    responder_action_owner(t.pc) && p == q || writer_action_owner(t.pc) && t.currentcpu == q
}
pub open spec fn inactive(pc: Pc) -> bool {
    pc == Pc::InitiatorLockPmap || pmap_owner(pc) || pc == Pc::InitiatorReactivate
    || pc == Pc::ResponderLockAction || responder_action_owner(pc) || pc == Pc::ResponderReactivate
}
pub open spec fn early_responder(pc: Pc) -> bool {
    pc == Pc::ResponderCheck || pc == Pc::ResponderDeactivate || pc == Pc::ResponderLockAction
}
pub open spec fn stale_allowed(t: LProcessor) -> bool {
    (t.pc == Pc::InitiatorMaybeRefreshOwnTlb && t.userpmap == t.writepmap)
    || t.actionneeded && (t.interrupt || early_responder(t.pc) || t.pc == Pc::ResponderRefreshTlb) && (
        inactive(t.pc) && t.pc != Pc::ResponderClearActionNeeded && t.pc != Pc::ResponderUnlockAction
        || t.pc == Pc::MainHandleInterrupt && t.interrupt
        || t.pc == Pc::ResponderCheck || t.pc == Pc::ResponderDeactivate)
}
pub open spec fn sent_to(t: LProcessor, q: int) -> bool {
    pmap_owner(t.pc) && (!sending(t.pc) || !t.todo.contains(q) && !(selected(t.pc) && t.currentcpu == q))
}
pub open spec fn quiesced(t: LProcessor, q: int) -> bool {
    updated(t.pc) || t.pc == Pc::InitiatorWaitForQuiescence && !t.todo.contains(q)
}
pub open spec fn local_inv(s: LState, c: Constants, p: int) -> bool {
    let t = s.procs[p];
    (t.active == !inactive(t.pc))
    && (pmap_owner(t.pc) ==> s.plock[t.writepmap])
    && (selected(t.pc) ==> t.currentcpu != p && s.procs[t.currentcpu].pc != Pc::Boot)
    && (selected(t.pc) && t.pc != Pc::InitiatorCheckCpuPmap ==> s.procs[t.currentcpu].userpmap == t.writepmap)
    && (writer_action_owner(t.pc) ==> s.procs[t.currentcpu].actionlock)
    && (responder_action_owner(t.pc) ==> t.actionlock)
    && (t.pc != Pc::Boot && !stale_allowed(t) ==> t.tlb == s.pentry[t.userpmap])
    && (t.pc == Pc::InitiatorUnlockAction || t.pc == Pc::InitiatorInterrupt ==> s.procs[t.currentcpu].actionneeded)
    && (t.pc == Pc::InitiatorInterrupt ==> !responder_action_owner(s.procs[t.currentcpu].pc))
}
pub open spec fn pair_inv(s: LState, c: Constants, p: int, q: int) -> bool {
    let t = s.procs[p]; let r = s.procs[q];
    (t.todo.contains(q) ==> p != q && r.pc != Pc::Boot)
    && (pmap_owner(t.pc) && pmap_owner(r.pc) && t.writepmap == r.writepmap ==> p == q)
    && (p != q && writer_action_owner(t.pc) && writer_action_owner(r.pc) ==> t.currentcpu != r.currentcpu)
    && (writer_action_owner(t.pc) && t.currentcpu == q ==> !responder_action_owner(r.pc))
    && (p != q && r.pc != Pc::Boot && r.userpmap == t.writepmap && sent_to(t, q) ==>
        r.actionneeded && !responder_action_owner(r.pc) && (r.interrupt || early_responder(r.pc)))
    && (p != q && r.pc != Pc::Boot && r.userpmap == t.writepmap && quiesced(t, q) ==>
        !r.active || r.pc == Pc::MainHandleInterrupt && r.interrupt
        || r.pc == Pc::ResponderCheck || r.pc == Pc::ResponderDeactivate)
}
pub open spec fn inductive(s: LState, c: Constants) -> bool {
    type_ok(s, c) && no_error(s)
    && (forall |p: int| c.processors.contains(p) ==> #[trigger] local_inv(s, c, p))
    && (forall |p: int, q: int| c.processors.contains(p) && c.processors.contains(q) ==> #[trigger] pair_inv(s, c, p, q))
    && action_ownership(s, c)
}
#[verifier::opaque]
pub open spec fn action_ownership(s: LState, c: Constants) -> bool {
    forall |q: int| c.processors.contains(q) && s.procs[q].actionlock ==>
        exists |p: int| c.processors.contains(p) && owns_action(s.procs[p], p, q)
}
pub proof fn initial_inductive(s: LState, c: Constants)
    requires init(s, c)
    ensures inductive(s, c)
{ reveal(action_ownership); }
pub proof fn preserve_local(s: LState, c: Constants, p: int, a: Step, q: int)
    requires inductive(s, c), enabled_step(s, c, p, a), c.processors.contains(q)
    ensures local_inv(step(s, c, p, a), c, q)
{
    reveal(enabled_step); reveal(step);
    let u = step(s, c, p, a);
    assert(local_inv(s, c, p)); assert(local_inv(s, c, q));
    assert(pair_inv(s, c, p, q)); assert(pair_inv(s, c, q, p));
    assert(local_inv(s, c, s.procs[p].currentcpu));
    assert(pair_inv(s, c, p, s.procs[p].currentcpu));
    match a {
        Step::Boot(_) => { assert(local_inv(u, c, q)); },
        Step::MainCheck => { assert(local_inv(u, c, q)); },
        Step::ChooseInitiator => { assert(local_inv(u, c, q)); },
        Step::SkipInitiator => { assert(local_inv(u, c, q)); },
        Step::HandleInterrupt => { assert(local_inv(u, c, q)); },
        Step::BeginShootdown(_) => { assert(local_inv(u, c, q)); },
        Step::AcquirePmapLock => { assert(local_inv(u, c, q)); },
        Step::SelectCpu(cpu) => { assert(pair_inv(s, c, p, cpu)); assert(local_inv(u, c, q)); },
        Step::ExitSend => { assert(local_inv(u, c, q)); },
        Step::CheckCpuPmap => { assert(local_inv(u, c, q)); },
        Step::AcquireActionLock => { assert(local_inv(u, c, q)); },
        Step::SetActionNeeded => { assert(local_inv(u, c, q)); },
        Step::UnlockAction => { assert(local_inv(u, c, q)); },
        Step::InterruptCpu => { assert(local_inv(u, c, q)); },
        Step::WaitQuiescence(_) => { assert(local_inv(u, c, q)); },
        Step::ExitQuiescence => { assert(local_inv(u, c, q)); },
        Step::UpdateEntry(_) => { assert(local_inv(u, c, q)); },
        Step::MaybeRefreshOwnTlb => { assert(local_inv(u, c, q)); },
        Step::UnlockPmap => { assert(local_inv(u, c, q)); },
        Step::ReactivateInitiator => { assert(local_inv(u, c, q)); },
        Step::CheckActionNeeded => { assert(local_inv(u, c, q)); },
        Step::DeactivateResponder => { assert(local_inv(u, c, q)); },
        Step::AcquireResponderLock => { assert(local_inv(u, c, q)); },
        Step::RefreshTlb => { assert(local_inv(u, c, q)); },
        Step::ClearActionNeeded => { assert(local_inv(u, c, q)); },
        Step::UnlockResponder => { assert(local_inv(u, c, q)); },
        Step::ReactivateResponder => { assert(local_inv(u, c, q)); },
    }
}
pub proof fn preserve_pair(s: LState, c: Constants, p: int, a: Step, q: int, r: int)
    requires inductive(s, c), enabled_step(s, c, p, a), c.processors.contains(q), c.processors.contains(r)
    ensures pair_inv(step(s, c, p, a), c, q, r)
{
    reveal(enabled_step); reveal(step);
    let u = step(s, c, p, a);
    assert(local_inv(s, c, p)); assert(local_inv(s, c, q)); assert(local_inv(s, c, r));
    assert(pair_inv(s, c, q, r)); assert(pair_inv(s, c, p, q)); assert(pair_inv(s, c, p, r));
    assert(pair_inv(s, c, q, p)); assert(pair_inv(s, c, r, p));
    match a {
        Step::Boot(_) => { assert(pair_inv(u, c, q, r)); },
        Step::MainCheck => { assert(pair_inv(u, c, q, r)); },
        Step::ChooseInitiator => { assert(pair_inv(u, c, q, r)); },
        Step::SkipInitiator => { assert(pair_inv(u, c, q, r)); },
        Step::HandleInterrupt => { assert(pair_inv(u, c, q, r)); },
        Step::BeginShootdown(_) => { assert(pair_inv(u, c, q, r)); },
        Step::AcquirePmapLock => { assert(pair_inv(u, c, q, r)); },
        Step::SelectCpu(_) => { assert(pair_inv(u, c, q, r)); },
        Step::ExitSend => { assert(pair_inv(u, c, q, r)); },
        Step::CheckCpuPmap => { assert(pair_inv(u, c, q, r)); },
        Step::AcquireActionLock => { assert(pair_inv(u, c, q, r)); },
        Step::SetActionNeeded => { assert(pair_inv(u, c, q, r)); },
        Step::UnlockAction => { assert(pair_inv(u, c, q, r)); },
        Step::InterruptCpu => { assert(pair_inv(u, c, q, r)); },
        Step::WaitQuiescence(_) => { assert(pair_inv(u, c, q, r)); },
        Step::ExitQuiescence => { assert(pair_inv(u, c, q, r)); },
        Step::UpdateEntry(_) => { assert(pair_inv(u, c, q, r)); },
        Step::MaybeRefreshOwnTlb => { assert(pair_inv(u, c, q, r)); },
        Step::UnlockPmap => { assert(pair_inv(u, c, q, r)); },
        Step::ReactivateInitiator => { assert(pair_inv(u, c, q, r)); },
        Step::CheckActionNeeded => { assert(pair_inv(u, c, q, r)); },
        Step::DeactivateResponder => { assert(pair_inv(u, c, q, r)); },
        Step::AcquireResponderLock => { assert(pair_inv(u, c, q, r)); },
        Step::RefreshTlb => { assert(pair_inv(u, c, q, r)); },
        Step::ClearActionNeeded => { assert(pair_inv(u, c, q, r)); },
        Step::UnlockResponder => { assert(pair_inv(u, c, q, r)); },
        Step::ReactivateResponder => { assert(pair_inv(u, c, q, r)); },
    }
}
pub proof fn preserve_error(s: LState, c: Constants, p: int, a: Step)
    requires inductive(s, c), enabled_step(s, c, p, a)
    ensures no_error(step(s, c, p, a))
{
    reveal(action_ownership);
    reveal(enabled_step); reveal(step);
    assert(local_inv(s, c, p));
    if a == Step::AcquireResponderLock && s.procs[p].actionlock {
        let owner = choose |owner: int| c.processors.contains(owner) && owns_action(s.procs[owner], owner, p);
        assert(local_inv(s, c, owner));
        assert(false);
    }
}
pub proof fn preserve_type(s: LState, c: Constants, p: int, a: Step)
    requires type_ok(s, c), enabled_step(s, c, p, a)
    ensures type_ok(step(s, c, p, a), c)
{
    reveal(enabled_step); reveal(step);
    let u = step(s, c, p, a);
    assert(u.procs.dom() =~= c.processors);
    assert(u.plock.dom() =~= c.pmaps);
    assert(u.pentry.dom() =~= c.pmaps);
}
pub proof fn preserve_ownership(s: LState, c: Constants, p: int, a: Step)
    requires inductive(s, c), enabled_step(s, c, p, a)
    ensures action_ownership(step(s, c, p, a), c)
{
    reveal(action_ownership);
    reveal(enabled_step); reveal(step);
    let u = step(s, c, p, a);
    assert(local_inv(s, c, p));
    assert forall |q: int| c.processors.contains(q) && u.procs[q].actionlock implies
        exists |owner: int| c.processors.contains(owner) && owns_action(u.procs[owner], owner, q) by {
        if a == Step::AcquireResponderLock && q == p || a == Step::AcquireActionLock && q == s.procs[p].currentcpu {
            assert(owns_action(u.procs[p], p, q));
        } else {
            assert(s.procs[q].actionlock);
            let owner = choose |owner: int| c.processors.contains(owner) && owns_action(s.procs[owner], owner, q);
            assert(local_inv(s, c, owner));
            assert(pair_inv(s, c, p, owner));
            assert(owns_action(u.procs[owner], owner, q));
        }
    }
}
pub proof fn preserve_inductive(s: LState, c: Constants, p: int, a: Step)
    requires inductive(s, c), enabled_step(s, c, p, a)
    ensures inductive(step(s, c, p, a), c)
{
    let u = step(s, c, p, a);
    preserve_error(s, c, p, a);
    preserve_type(s, c, p, a);
    preserve_ownership(s, c, p, a);
    assert forall |q: int| c.processors.contains(q) implies #[trigger] local_inv(u, c, q) by {
        preserve_local(s, c, p, a, q);
    }
    assert forall |q: int, r: int| c.processors.contains(q) && c.processors.contains(r)
        implies #[trigger] pair_inv(u, c, q, r) by {
        preserve_pair(s, c, p, a, q, r);
    }
}
pub open spec fn safety_spec(b: Behavior<LState>, c: Constants) -> bool {
    valid_constants(c) && init(b[0], c)
    && (forall |k: int| k >= 0 ==> b.dom().contains(k))
    && forall |k: int| k >= 0 ==> #[trigger] next(b[k], b[k+1], c)
}
pub proof fn safety_at(b: Behavior<LState>, c: Constants, k: int)
    requires safety_spec(b, c), k >= 0
    ensures inductive(b[k], c), no_error(b[k])
    decreases k
{
    if k == 0 { initial_inductive(b[0], c); }
    else {
        safety_at(b, c, k-1);
        let i = k-1;
        assert(next(b[i], b[i+1], c));
        reveal(next);
        let a = choose |a: Action| #[trigger] enabled(b[i], c, a) && b[i+1] == apply(b[i], c, a);
        match a {
            Action::Stutter => {},
            Action::Step { p, step: a } => { preserve_inductive(b[i], c, p, a); },
        }
    }
}
// ivy_examples_tlb_Safety: SafetySpec => []NoError.
pub proof fn safety(b: Behavior<LState>, c: Constants)
    requires safety_spec(b, c)
    ensures forall |k: int| k >= 0 ==> #[trigger] no_error(b[k])
{
    assert forall |k: int| k >= 0 implies #[trigger] no_error(b[k]) by { safety_at(b, c, k); }
}
} // verus!
