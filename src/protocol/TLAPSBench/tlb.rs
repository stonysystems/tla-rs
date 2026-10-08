//! Handwritten Ivy TLB shootdown model. Processor/PMap/PageEntry may be infinite.
use vstd::prelude::*;
verus! {
pub enum Pc {
    Boot, MainCheck, MainChoose, MainHandleInterrupt,
    InitiatorDeactivate, InitiatorLockPmap, InitiatorForSend, InitiatorCheckCpuPmap,
    InitiatorLockAction, InitiatorSetActionNeeded, InitiatorUnlockAction,
    InitiatorInterrupt, InitiatorWaitForQuiescence, InitiatorUpdateEntry,
    InitiatorMaybeRefreshOwnTlb, InitiatorUnlockPmap, InitiatorReactivate,
    ResponderCheck, ResponderDeactivate, ResponderLockAction, ResponderRefreshTlb,
    ResponderClearActionNeeded, ResponderUnlockAction, ResponderReactivate,
}
pub struct LProcessor {
    pub pc: Pc, pub userpmap: int, pub writepmap: int, pub currentcpu: int,
    pub actionlock: bool, pub actionneeded: bool, pub active: bool, pub interrupt: bool,
    pub tlb: int, pub todo: ISet<int>,
}
pub struct Constants { pub processors: ISet<int>, pub pmaps: ISet<int>, pub entries: ISet<int> }
pub struct LState {
    pub procs: IMap<int, LProcessor>, pub plock: IMap<int, bool>, pub pentry: IMap<int, int>, pub error: bool,
}
pub open spec fn valid_constants(c: Constants) -> bool {
    !c.processors.is_empty() && !c.pmaps.is_empty() && !c.entries.is_empty()
}
pub open spec fn type_ok(s: LState, c: Constants) -> bool {
    s.procs.dom() == c.processors && s.plock.dom() == c.pmaps && s.pentry.dom() == c.pmaps
    && (forall |p: int| #![trigger s.procs[p]] c.processors.contains(p) ==> c.pmaps.contains(s.procs[p].userpmap)
        && c.pmaps.contains(s.procs[p].writepmap) && c.processors.contains(s.procs[p].currentcpu)
        && c.entries.contains(s.procs[p].tlb) && s.procs[p].todo.subset_of(c.processors))
    && forall |m: int| #![trigger c.pmaps.contains(m)] c.pmaps.contains(m) ==> c.entries.contains(s.pentry[m])
}
pub open spec fn init(s: LState, c: Constants) -> bool {
    type_ok(s, c) && !s.error
    && (forall |p: int| #![trigger c.processors.contains(p)] c.processors.contains(p) ==> s.procs[p].pc == Pc::Boot
        && !s.procs[p].actionlock && !s.procs[p].actionneeded && s.procs[p].active
        && !s.procs[p].interrupt && s.procs[p].todo.is_empty())
    && forall |m: int| c.pmaps.contains(m) ==> !s.plock[m]
}
pub enum Step {
    Boot(int), MainCheck, ChooseInitiator, SkipInitiator, HandleInterrupt, BeginShootdown(int),
    AcquirePmapLock, SelectCpu(int), ExitSend, CheckCpuPmap, AcquireActionLock, SetActionNeeded,
    UnlockAction, InterruptCpu, WaitQuiescence(int), ExitQuiescence, UpdateEntry(int),
    MaybeRefreshOwnTlb, UnlockPmap, ReactivateInitiator, CheckActionNeeded, DeactivateResponder,
    AcquireResponderLock, RefreshTlb, ClearActionNeeded, UnlockResponder, ReactivateResponder,
}
pub enum Action { Step { p: int, step: Step }, Stutter }
pub open spec fn todo(s: LState, c: Constants, p: int) -> ISet<int> {
    c.processors.filter(|q: int| s.procs[q].pc != Pc::Boot && q != p)
}
#[verifier::opaque]
pub open spec fn enabled_step(s: LState, c: Constants, p: int, a: Step) -> bool {
    let t = s.procs[p];
    c.processors.contains(p) && match a {
        Step::Boot(m) => c.pmaps.contains(m) && t.pc == Pc::Boot && !s.plock[m],
        Step::MainCheck => t.pc == Pc::MainCheck,
        Step::ChooseInitiator | Step::SkipInitiator => t.pc == Pc::MainChoose,
        Step::HandleInterrupt => t.pc == Pc::MainHandleInterrupt,
        Step::BeginShootdown(m) => c.pmaps.contains(m) && t.pc == Pc::InitiatorDeactivate,
        Step::AcquirePmapLock => t.pc == Pc::InitiatorLockPmap && !s.plock[t.writepmap],
        Step::SelectCpu(q) => c.processors.contains(q) && t.pc == Pc::InitiatorForSend && t.todo.contains(q),
        Step::ExitSend => t.pc == Pc::InitiatorForSend && (forall |q: int| c.processors.contains(q) ==> !t.todo.contains(q)),
        Step::CheckCpuPmap => t.pc == Pc::InitiatorCheckCpuPmap,
        Step::AcquireActionLock => t.pc == Pc::InitiatorLockAction && !s.procs[t.currentcpu].actionlock,
        Step::SetActionNeeded => t.pc == Pc::InitiatorSetActionNeeded,
        Step::UnlockAction => t.pc == Pc::InitiatorUnlockAction,
        Step::InterruptCpu => t.pc == Pc::InitiatorInterrupt,
        Step::WaitQuiescence(q) => c.processors.contains(q) && t.pc == Pc::InitiatorWaitForQuiescence && t.todo.contains(q)
            && (!s.procs[q].active || s.procs[q].userpmap != t.writepmap),
        Step::ExitQuiescence => t.pc == Pc::InitiatorWaitForQuiescence && (forall |q: int| c.processors.contains(q) ==> !t.todo.contains(q)),
        Step::UpdateEntry(e) => c.entries.contains(e) && t.pc == Pc::InitiatorUpdateEntry,
        Step::MaybeRefreshOwnTlb => t.pc == Pc::InitiatorMaybeRefreshOwnTlb,
        Step::UnlockPmap => t.pc == Pc::InitiatorUnlockPmap,
        Step::ReactivateInitiator => t.pc == Pc::InitiatorReactivate,
        Step::CheckActionNeeded => t.pc == Pc::ResponderCheck,
        Step::DeactivateResponder => t.pc == Pc::ResponderDeactivate,
        // The source checks plock here, and asserts actionlock was free.
        Step::AcquireResponderLock => t.pc == Pc::ResponderLockAction && !s.plock[t.userpmap],
        Step::RefreshTlb => t.pc == Pc::ResponderRefreshTlb,
        Step::ClearActionNeeded => t.pc == Pc::ResponderClearActionNeeded,
        Step::UnlockResponder => t.pc == Pc::ResponderUnlockAction,
        Step::ReactivateResponder => t.pc == Pc::ResponderReactivate,
    }
}
pub open spec fn replace(s: LState, p: int, t: LProcessor) -> LState { LState { procs: s.procs.insert(p, t), ..s } }
#[verifier::opaque]
pub open spec fn step(s: LState, c: Constants, p: int, a: Step) -> LState {
    let t = s.procs[p];
    match a {
        Step::Boot(m) => replace(s, p, LProcessor { pc: Pc::MainCheck, userpmap: m, tlb: s.pentry[m], ..t }),
        Step::MainCheck => LState { error: s.error || t.tlb != s.pentry[t.userpmap],
            ..replace(s, p, LProcessor { pc: Pc::MainChoose, ..t }) },
        Step::ChooseInitiator => replace(s, p, LProcessor { pc: Pc::InitiatorDeactivate, ..t }),
        Step::SkipInitiator => replace(s, p, LProcessor { pc: Pc::MainHandleInterrupt, ..t }),
        Step::HandleInterrupt => replace(s, p, LProcessor { pc: if t.interrupt { Pc::ResponderCheck } else { Pc::MainCheck }, interrupt: false, ..t }),
        Step::BeginShootdown(m) => replace(s, p, LProcessor { pc: Pc::InitiatorLockPmap, active: false, writepmap: m, ..t }),
        Step::AcquirePmapLock => LState { plock: s.plock.insert(t.writepmap, true),
            ..replace(s, p, LProcessor { pc: Pc::InitiatorForSend, todo: todo(s, c, p), ..t }) },
        Step::SelectCpu(q) => replace(s, p, LProcessor { pc: Pc::InitiatorCheckCpuPmap, currentcpu: q, todo: t.todo.remove(q), ..t }),
        Step::ExitSend => replace(s, p, LProcessor { pc: Pc::InitiatorWaitForQuiescence, todo: todo(s, c, p), ..t }),
        Step::CheckCpuPmap => replace(s, p, LProcessor { pc: if s.procs[t.currentcpu].userpmap == t.writepmap { Pc::InitiatorLockAction } else { Pc::InitiatorForSend }, ..t }),
        Step::AcquireActionLock => { let u = replace(s, t.currentcpu, LProcessor { actionlock: true, ..s.procs[t.currentcpu] }); replace(u, p, LProcessor { pc: Pc::InitiatorSetActionNeeded, ..u.procs[p] }) },
        Step::SetActionNeeded => { let u = replace(s, t.currentcpu, LProcessor { actionneeded: true, ..s.procs[t.currentcpu] }); replace(u, p, LProcessor { pc: Pc::InitiatorUnlockAction, ..u.procs[p] }) },
        Step::UnlockAction => { let u = replace(s, t.currentcpu, LProcessor { actionlock: false, ..s.procs[t.currentcpu] }); LState { error: s.error || !s.procs[t.currentcpu].actionlock, ..replace(u, p, LProcessor { pc: Pc::InitiatorInterrupt, ..u.procs[p] }) } },
        Step::InterruptCpu => { let u = replace(s, t.currentcpu, LProcessor { interrupt: true, ..s.procs[t.currentcpu] }); replace(u, p, LProcessor { pc: Pc::InitiatorForSend, ..u.procs[p] }) },
        Step::WaitQuiescence(q) => replace(s, p, LProcessor { todo: t.todo.remove(q), ..t }),
        Step::ExitQuiescence => replace(s, p, LProcessor { pc: Pc::InitiatorUpdateEntry, ..t }),
        Step::UpdateEntry(e) => LState { pentry: s.pentry.insert(t.writepmap, e), ..replace(s, p, LProcessor { pc: Pc::InitiatorMaybeRefreshOwnTlb, ..t }) },
        Step::MaybeRefreshOwnTlb => replace(s, p, LProcessor { pc: Pc::InitiatorUnlockPmap, tlb: if t.userpmap == t.writepmap { s.pentry[t.writepmap] } else { t.tlb }, ..t }),
        Step::UnlockPmap => LState { plock: s.plock.insert(t.writepmap, false), error: s.error || !s.plock[t.writepmap],
            ..replace(s, p, LProcessor { pc: Pc::InitiatorReactivate, ..t }) },
        Step::ReactivateInitiator => replace(s, p, LProcessor { pc: Pc::MainHandleInterrupt, active: true, ..t }),
        Step::CheckActionNeeded => replace(s, p, LProcessor { pc: if t.actionneeded { Pc::ResponderDeactivate } else { Pc::MainCheck }, ..t }),
        Step::DeactivateResponder => replace(s, p, LProcessor { pc: Pc::ResponderLockAction, active: false, ..t }),
        Step::AcquireResponderLock => LState { error: s.error || t.actionlock,
            ..replace(s, p, LProcessor { pc: Pc::ResponderRefreshTlb, actionlock: true, ..t }) },
        Step::RefreshTlb => replace(s, p, LProcessor { pc: Pc::ResponderClearActionNeeded, tlb: s.pentry[t.userpmap], ..t }),
        Step::ClearActionNeeded => replace(s, p, LProcessor { pc: Pc::ResponderUnlockAction, actionneeded: false, ..t }),
        Step::UnlockResponder => LState { error: s.error || !t.actionlock,
            ..replace(s, p, LProcessor { pc: Pc::ResponderReactivate, actionlock: false, ..t }) },
        Step::ReactivateResponder => replace(s, p, LProcessor { pc: Pc::ResponderCheck, active: true, ..t }),
    }
}
pub open spec fn enabled(s: LState, c: Constants, a: Action) -> bool {
    match a { Action::Step { p, step: a } => enabled_step(s, c, p, a), Action::Stutter => true }
}
pub open spec fn apply(s: LState, c: Constants, a: Action) -> LState {
    match a { Action::Step { p, step: a } => step(s, c, p, a), Action::Stutter => s }
}
#[verifier::opaque]
pub open spec fn next(s: LState, u: LState, c: Constants) -> bool {
    exists |a: Action| #[trigger] enabled(s, c, a) && u == apply(s, c, a)
}
pub open spec fn no_error(s: LState) -> bool { !s.error }
pub open spec fn makes_progress(s: LState, p: int) -> bool {
    s.procs[p].pc == Pc::MainCheck || s.procs[p].pc == Pc::ResponderClearActionNeeded
}
} // verus!
