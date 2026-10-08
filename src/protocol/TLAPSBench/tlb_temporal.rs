//! Source fairness and reachable-state facts for TLB progress.
use vstd::prelude::*;
use super::tlb::*;
use super::tlb_proof as safety;
use super::temporal::Behavior;
verus! {
pub enum Group { Processor(int), Boot(int), Pmap(int), Responder(int) }
pub open spec fn handles(g: Group, a: Action) -> bool {
    match a {
        Action::Stutter => false,
        Action::Step { p, step: t } => match g {
            Group::Processor(q) => p == q,
            Group::Boot(q) => p == q && matches!(t, Step::Boot(_)),
            Group::Pmap(q) => p == q && t == Step::AcquirePmapLock,
            Group::Responder(q) => p == q && t == Step::AcquireResponderLock,
        },
    }
}
#[verifier::opaque]
pub open spec fn group_enabled(s: LState, c: Constants, g: Group) -> bool {
    exists |a: Action| handles(g, a) && #[trigger] enabled(s, c, a) && apply(s, c, a) != s
}
#[verifier::opaque]
pub open spec fn group_taken(s: LState, u: LState, c: Constants, g: Group) -> bool {
    s != u && exists |a: Action| handles(g, a) && #[trigger] enabled(s, c, a) && u == apply(s, c, a)
}
pub open spec fn fair_event(b: Behavior<LState>, c: Constants, g: Group, k: int) -> bool {
    !group_enabled(b[k], c, g) || group_taken(b[k], b[k+1], c, g)
}
pub open spec fn fair_after(b: Behavior<LState>, c: Constants, g: Group, start: int) -> bool {
    exists |k: int| k >= start && #[trigger] fair_event(b, c, g, k)
}
pub open spec fn enabled_after(b: Behavior<LState>, c: Constants, g: Group, start: int) -> bool {
    exists |k: int| k >= start && #[trigger] group_enabled(b[k], c, g)
}
pub open spec fn taken_after(b: Behavior<LState>, c: Constants, g: Group, start: int) -> bool {
    exists |k: int| k >= start && #[trigger] group_taken(b[k], b[k+1], c, g)
}
pub open spec fn weak_fair(b: Behavior<LState>, c: Constants, g: Group) -> bool {
    forall |start: int| start >= 0 ==> #[trigger] fair_after(b, c, g, start)
}
pub open spec fn infinitely_enabled(b: Behavior<LState>, c: Constants, g: Group) -> bool {
    forall |start: int| start >= 0 ==> #[trigger] enabled_after(b, c, g, start)
}
pub open spec fn infinitely_taken(b: Behavior<LState>, c: Constants, g: Group) -> bool {
    forall |start: int| start >= 0 ==> #[trigger] taken_after(b, c, g, start)
}
pub open spec fn strong_fair(b: Behavior<LState>, c: Constants, g: Group) -> bool {
    infinitely_enabled(b, c, g) ==> infinitely_taken(b, c, g)
}
#[verifier::opaque]
pub open spec fn fair_spec(b: Behavior<LState>, c: Constants) -> bool {
    safety::safety_spec(b, c)
    && forall |p: int| #![trigger c.processors.contains(p)] c.processors.contains(p) ==> weak_fair(b, c, Group::Processor(p))
        && strong_fair(b, c, Group::Boot(p)) && strong_fair(b, c, Group::Pmap(p))
        && strong_fair(b, c, Group::Responder(p))
}
pub open spec fn booted(s: LState, c: Constants) -> ISet<int> {
    c.processors.filter(|p: int| s.procs[p].pc != Pc::Boot)
}
pub open spec fn owns_pmap(s: LState, p: int, m: int) -> bool {
    safety::pmap_owner(s.procs[p].pc) && s.procs[p].writepmap == m
}
#[verifier::opaque]
pub open spec fn pmap_ownership(s: LState, c: Constants) -> bool {
    forall |m: int| c.pmaps.contains(m) && s.plock[m] ==>
        exists |p: int| c.processors.contains(p) && #[trigger] owns_pmap(s, p, m)
}
pub open spec fn inductive(s: LState, c: Constants) -> bool {
    safety::inductive(s, c) && booted(s, c).finite() && pmap_ownership(s, c)
}
pub proof fn initial(s: LState, c: Constants)
    requires init(s, c)
    ensures inductive(s, c)
{
    reveal(pmap_ownership);
    safety::initial_inductive(s, c);
    assert(booted(s, c) =~= ISet::<int>::empty());
}
pub proof fn preserve_booted(s: LState, c: Constants, p: int, a: Step)
    requires inductive(s, c), enabled_step(s, c, p, a)
    ensures booted(step(s, c, p, a), c).finite()
{
    reveal(enabled_step); reveal(step);
    let u = step(s, c, p, a);
    assert(booted(u, c).subset_of(booted(s, c).insert(p)));
    vstd::iset_lib::lemma_iset_subset_finite(booted(s, c).insert(p), booted(u, c));
}
pub proof fn preserve_pmap_owner(s: LState, c: Constants, p: int, a: Step, m: int)
    requires inductive(s, c), enabled_step(s, c, p, a), c.pmaps.contains(m), step(s, c, p, a).plock[m]
    ensures exists |q: int| c.processors.contains(q) && #[trigger] owns_pmap(step(s, c, p, a), q, m)
{
    reveal(pmap_ownership);
    reveal(enabled_step); reveal(step);
    let u = step(s, c, p, a);
    assert(safety::local_inv(s, c, p));
    if a == Step::AcquirePmapLock && s.procs[p].writepmap == m {
        assert(owns_pmap(u, p, m));
    } else {
        let q = choose |q: int| c.processors.contains(q) && #[trigger] owns_pmap(s, q, m);
        match a {
            Step::Boot(_) | Step::MainCheck | Step::ChooseInitiator | Step::SkipInitiator
            | Step::HandleInterrupt | Step::BeginShootdown(_) | Step::AcquirePmapLock => { assert(owns_pmap(u, q, m)); },
            Step::SelectCpu(_) | Step::ExitSend | Step::CheckCpuPmap => { assert(owns_pmap(u, q, m)); },
            Step::AcquireActionLock | Step::SetActionNeeded | Step::UnlockAction | Step::InterruptCpu => { assert(owns_pmap(u, q, m)); },
            Step::WaitQuiescence(_) | Step::ExitQuiescence | Step::UpdateEntry(_) | Step::MaybeRefreshOwnTlb | Step::UnlockPmap => { assert(owns_pmap(u, q, m)); },
            _ => { assert(owns_pmap(u, q, m)); },
        }
    }
}
pub proof fn preserve(s: LState, c: Constants, p: int, a: Step)
    requires inductive(s, c), enabled_step(s, c, p, a)
    ensures inductive(step(s, c, p, a), c)
{
    reveal(pmap_ownership);
    safety::preserve_inductive(s, c, p, a);
    preserve_booted(s, c, p, a);
    let u = step(s, c, p, a);
    assert forall |m: int| c.pmaps.contains(m) && u.plock[m]
        implies exists |q: int| c.processors.contains(q) && #[trigger] owns_pmap(u, q, m) by {
        preserve_pmap_owner(s, c, p, a, m);
    }
}
pub proof fn safety_at(b: Behavior<LState>, c: Constants, k: int)
    requires fair_spec(b, c), k >= 0
    ensures inductive(b[k], c), valid_constants(c), next(b[k], b[k+1], c)
    decreases k
{
    reveal(fair_spec);
    if k == 0 { initial(b[k], c); }
    else {
        safety_at(b, c, k-1);
        reveal(next);
        let a = choose |a: Action| #[trigger] enabled(b[k-1], c, a) && b[k] == apply(b[k-1], c, a);
        match a { Action::Stutter => {}, Action::Step { p, step: t } => { preserve(b[k-1], c, p, t); } }
    }
}
pub proof fn todo_finite(s: LState, c: Constants, p: int)
    requires inductive(s, c), c.processors.contains(p)
    ensures s.procs[p].todo.finite()
{
    assert forall |q: int| #![trigger booted(s, c).contains(q)] s.procs[p].todo.contains(q) implies booted(s, c).contains(q) by {
        assert(safety::pair_inv(s, c, p, q));
    }
    vstd::iset_lib::lemma_iset_subset_finite(booted(s, c), s.procs[p].todo);
}
pub proof fn step_changes(s: LState, c: Constants, p: int, a: Step)
    requires safety::inductive(s, c), enabled_step(s, c, p, a)
    ensures step(s, c, p, a) != s
{
    reveal(enabled_step); reveal(step);
    assert(safety::local_inv(s, c, p));
    match a {
        Step::WaitQuiescence(q) => {
            assert(s.procs[p].todo.contains(q));
            assert(!step(s, c, p, a).procs[p].todo.contains(q));
        },
        _ => { assert(step(s, c, p, a).procs[p].pc != s.procs[p].pc); },
    }
}
pub proof fn enabled_group(s: LState, c: Constants, p: int, t: Step, g: Group)
    requires safety::inductive(s, c), enabled_step(s, c, p, t), handles(g, Action::Step { p, step: t })
    ensures group_enabled(s, c, g)
{
    reveal(group_enabled);
    step_changes(s, c, p, t);
    assert(enabled(s, c, Action::Step { p, step: t }));
}
pub proof fn record_take(s: LState, u: LState, c: Constants, a: Action, g: Group)
    requires s != u, enabled(s, c, a), handles(g, a), u == apply(s, c, a)
    ensures group_taken(s, u, c, g)
{ reveal(group_taken); }
pub proof fn take_witness(s: LState, u: LState, c: Constants, g: Group) -> (a: Action)
    requires group_taken(s, u, c, g)
    ensures s != u, handles(g, a), enabled(s, c, a), u == apply(s, c, a)
{
    reveal(group_taken);
    choose |a: Action| handles(g, a) && #[trigger] enabled(s, c, a) && u == apply(s, c, a)
}
// Only a processor's own actions change these local control fields.
pub open spec fn same_control(t: LProcessor, u: LProcessor) -> bool {
    t.pc == u.pc && t.todo == u.todo && t.currentcpu == u.currentcpu
    && t.userpmap == u.userpmap && t.writepmap == u.writepmap && t.active == u.active
}
pub proof fn other_control(s: LState, c: Constants, a: Action, q: int)
    requires safety::inductive(s, c), enabled(s, c, a), c.processors.contains(q),
        !handles(Group::Processor(q), a)
    ensures same_control(s.procs[q], apply(s, c, a).procs[q])
{
    reveal(step); reveal(enabled_step);
}
pub proof fn quiet_step(s: LState, u: LState, c: Constants, p: int)
    requires safety::inductive(s, c), next(s, u, c), c.processors.contains(p),
        !group_taken(s, u, c, Group::Processor(p))
    ensures same_control(s.procs[p], u.procs[p])
{
    reveal(next);
    let a = choose |a: Action| #[trigger] enabled(s, c, a) && u == apply(s, c, a);
    if handles(Group::Processor(p), a) {
        match a { Action::Step { p: q, step: t } => { step_changes(s, c, q, t); }, _ => {} }
        record_take(s, u, c, a, Group::Processor(p));
    } else { other_control(s, c, a, p); }
}
pub proof fn quiet_interval(b: Behavior<LState>, c: Constants, p: int, start: int, end: int)
    requires fair_spec(b, c), c.processors.contains(p), 0 <= start <= end,
        forall |k: int| start <= k < end ==> !#[trigger] group_taken(b[k], b[k+1], c, Group::Processor(p))
    ensures same_control(b[start].procs[p], b[end].procs[p])
    decreases end-start
{
    if end > start {
        quiet_interval(b, c, p, start, end-1);
        safety_at(b, c, end-1);
        quiet_step(b[end-1], b[end], c, p);
    }
}
pub proof fn weak_fairness(b: Behavior<LState>, c: Constants, p: int)
    requires fair_spec(b, c), c.processors.contains(p)
    ensures weak_fair(b, c, Group::Processor(p))
{ reveal(fair_spec); }
pub proof fn strong_fairness(b: Behavior<LState>, c: Constants, p: int)
    requires fair_spec(b, c), c.processors.contains(p)
    ensures strong_fair(b, c, Group::Boot(p)), strong_fair(b, c, Group::Pmap(p)), strong_fair(b, c, Group::Responder(p))
{ reveal(fair_spec); }
pub proof fn weak_event(b: Behavior<LState>, c: Constants, p: int, start: int)
    requires fair_spec(b, c), c.processors.contains(p), start >= 0,
        forall |k: int| k >= start ==> #[trigger] group_enabled(b[k], c, Group::Processor(p))
    ensures exists |k: int| k >= start && #[trigger] group_taken(b[k], b[k+1], c, Group::Processor(p))
{
    weak_fairness(b, c, p);
    assert(fair_after(b, c, Group::Processor(p), start));
    let k = choose |k: int| k >= start && #[trigger] fair_event(b, c, Group::Processor(p), k);
    assert(group_taken(b[k], b[k+1], c, Group::Processor(p)));
}
} // verus!
