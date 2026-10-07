//! Weak fairness for exactly the action groups in FlashWithMutexDefs.Fairness.
use vstd::prelude::*;
use super::flash::*;
use super::temporal::Behavior;
verus! {
pub enum Group { Uni(int), Inv(int), Replace(int), Nakc, Wb, ShWb }
pub open spec fn handles(g: Group, a: Action) -> bool {
    match g {
        Group::Uni(n) => match a {
            Action::ReceiveNak { dst } | Action::ReceivePut { dst } | Action::ReceivePutX { dst } => dst == n,
            Action::LocalNak { src, .. } | Action::LocalRelay { src, .. } | Action::LocalGrant { src, .. }
                | Action::RemoteNak { src, .. } | Action::RemoteGrant { src, .. } => src == n,
            _ => false,
        },
        Group::Inv(n) => match a {
            Action::Invalidate { dst } => dst == n,
            Action::InvalidateAck { src } => src == n,
            _ => false,
        },
        Group::Replace(n) => a == Action::ReceiveReplace { src: n },
        Group::Nakc => a == Action::ClearNak,
        Group::Wb => a == Action::ReceiveWriteback,
        Group::ShWb => a == Action::ReceiveForwardAck || a == Action::ReceiveSharedWriteback,
    }
}
pub open spec fn group_enabled(s: LState, c: Constants, g: Group) -> bool {
    exists |a: Action| handles(g, a) && #[trigger] enabled(s, c, a) && apply(s, c, a) != s
}
pub open spec fn group_taken(s: LState, u: LState, c: Constants, g: Group) -> bool {
    s != u && exists |a: Action| handles(g, a) && #[trigger] enabled(s, c, a) && u == apply(s, c, a)
}
pub open spec fn fair_after(b: Behavior<LState>, c: Constants, g: Group, start: int) -> bool {
    exists |k: int| k >= start && #[trigger] fair_event(b, c, g, k)
}
pub open spec fn fair_event(b: Behavior<LState>, c: Constants, g: Group, k: int) -> bool {
    !group_enabled(b[k], c, g) || group_taken(b[k], b[k+1], c, g)
}
pub open spec fn weak_fair(b: Behavior<LState>, c: Constants, g: Group) -> bool {
    forall |start: int| start >= 0 ==> #[trigger] fair_after(b, c, g, start)
}
pub open spec fn safety_spec(b: Behavior<LState>, c: Constants) -> bool {
    valid_constants(c)
    && (forall |k: int| k >= 0 ==> b.dom().contains(k))
    && c.nodes.contains(b[0].home) && c.data.contains(b[0].current)
    && b[0] == initial(c, b[0].home, b[0].current)
    && forall |k: int| k >= 0 ==> #[trigger] next(b[k], b[k+1], c)
}
pub open spec fn fair_spec(b: Behavior<LState>, c: Constants) -> bool {
    safety_spec(b, c)
    && weak_fair(b, c, Group::Nakc) && weak_fair(b, c, Group::Wb) && weak_fair(b, c, Group::ShWb)
    && forall |n: int| c.nodes.contains(n) ==> weak_fair(b, c, Group::Uni(n))
        && weak_fair(b, c, Group::Inv(n)) && weak_fair(b, c, Group::Replace(n))
}
pub open spec fn pending(s: LState, g: Group) -> bool {
    match g {
        Group::Replace(n) => s.replace[n], Group::Nakc => s.nakc,
        Group::Wb => s.wb.pending, Group::ShWb => s.shwb.cmd != Shared::None,
        Group::Uni(n) => s.uni[n].cmd != Uni::None, Group::Inv(n) => s.inv[n] != Inv::None,
    }
}
pub open spec fn simple_group(g: Group, c: Constants) -> bool {
    match g { Group::Replace(n) => c.nodes.contains(n), Group::Nakc | Group::Wb | Group::ShWb => true, _ => false }
}
pub proof fn pending_enabled(s: LState, c: Constants, g: Group)
    requires simple_group(g, c), pending(s, g)
    ensures group_enabled(s, c, g)
{
    reveal(enabled);
    reveal(apply);
    let a = match g {
        Group::Replace(n) => Action::ReceiveReplace { src: n },
        Group::Nakc => Action::ClearNak,
        Group::Wb => Action::ReceiveWriteback,
        _ => if s.shwb.cmd == Shared::FAck { Action::ReceiveForwardAck } else { Action::ReceiveSharedWriteback },
    };
    assert(handles(g, a) && enabled(s, c, a) && apply(s, c, a) != s);
}
pub proof fn handler_clears(s: LState, u: LState, c: Constants, g: Group)
    requires simple_group(g, c), group_taken(s, u, c, g)
    ensures !pending(u, g)
{
    let a = choose |a: Action| handles(g, a) && #[trigger] enabled(s, c, a) && u == apply(s, c, a);
    reveal(apply);
}
pub proof fn progress_at(b: Behavior<LState>, c: Constants, g: Group, start: int)
    requires simple_group(g, c), weak_fair(b, c, g), start >= 0,
        forall |k: int| k >= 0 ==> b.dom().contains(k)
    ensures exists |k: int| k >= start && !pending(b[k], g)
{
    if !(exists |k: int| k >= start && !pending(b[k], g)) {
        assert(fair_after(b, c, g, start));
        let k = choose |k: int| k >= start && #[trigger] fair_event(b, c, g, k);
        assert(k >= start);
        assert(pending(b[k], g));
        pending_enabled(b[k], c, g);
        handler_clears(b[k], b[k+1], c, g);
        assert(exists |j: int| j >= start && !pending(b[j], g)) by { assert(!pending(b[k+1], g)); }
    }
}
pub open spec fn progress(b: Behavior<LState>, g: Group) -> bool {
    forall |start: int| start >= 0 && pending(b[start], g) ==> #[trigger] clear_after(b, g, start)
}
pub open spec fn clear_after(b: Behavior<LState>, g: Group, start: int) -> bool {
    exists |k: int| k >= start && !pending(b[k], g)
}
// FlashWithMutex_{Rp,Wb,ShWb,Nakc}ProgressCorrect. These are infinite-behavior
// leads-to proofs under the source weak fairness, not bounded progress tests.
pub proof fn benchmark_progress(b: Behavior<LState>, c: Constants)
    requires fair_spec(b, c)
    ensures progress(b, Group::Nakc), progress(b, Group::Wb), progress(b, Group::ShWb),
        forall |n: int| c.nodes.contains(n) ==> progress(b, Group::Replace(n))
{
    assert forall |g: Group, start: int| simple_group(g, c) && start >= 0
        implies #[trigger] clear_after(b, g, start) by {
        progress_at(b, c, g, start);
    }
}
} // verus!
