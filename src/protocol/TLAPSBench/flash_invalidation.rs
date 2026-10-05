//! An invalidation goes from Inv to Ack to None under the source weak fairness.
use vstd::prelude::*;
use super::flash::*;
use super::flash_control as control;
use super::flash_liveness::*;
use super::temporal::Behavior;
verus! {
pub open spec fn rank(s: LState,n: int) -> nat {
    match s.inv[n] { Inv::None => 0,Inv::Ack => 1,Inv::Inv => 2 }
}
pub proof fn pending_enabled(s: LState,c: Constants,n: int)
    requires control::inductive(s,c),c.nodes.contains(n),pending(s,Group::Inv(n))
    ensures group_enabled(s,c,Group::Inv(n))
{
    control::expose_node(s,c,n);
    control::expose_work(s,c,control::Work::Invalidating);
    reveal(enabled); reveal(apply);
    let a=if s.inv[n] == Inv::Inv { Action::Invalidate { dst: n } }
        else { Action::InvalidateAck { src: n } };
    assert(handles(Group::Inv(n),a) && enabled(s,c,a) && apply(s,c,a) != s);
}
pub proof fn step_rank(s: LState,c: Constants,a: Action,n: int)
    requires control::inductive(s,c),c.nodes.contains(n),pending(s,Group::Inv(n)),enabled(s,c,a)
    ensures rank(apply(s,c,a),n) <= rank(s,n),
        handles(Group::Inv(n),a) ==> rank(apply(s,c,a),n) < rank(s,n)
{
    control::expose_node(s,c,n);
    control::expose_work(s,c,control::Work::Invalidating);
    reveal(enabled); reveal(apply);
    match a {
        Action::Store { .. } | Action::RemoteRequest { .. } | Action::LocalForward { .. }
        | Action::LocalGet | Action::LocalGetX | Action::RemoteWriteback { .. }
        | Action::LocalWriteback | Action::RemoteReplace { .. } | Action::LocalReplace
        | Action::ReceiveNak { .. } | Action::ClearNak | Action::LocalNak { .. }
        | Action::LocalRelay { .. } | Action::LocalGrant { .. } | Action::RemoteNak { .. }
        | Action::RemoteGrant { .. } | Action::ReceivePut { .. } | Action::ReceivePutX { .. }
        | Action::ReceiveWriteback | Action::ReceiveForwardAck | Action::ReceiveSharedWriteback
        | Action::ReceiveReplace { .. } | Action::Stutter => {},
        Action::Invalidate { dst } => {},
        Action::InvalidateAck { src } => {},
    }
}
pub proof fn rank_until(s: Behavior<LState>,c: Constants,n: int,start: int,end: int)
    requires safety_spec(s,c),c.nodes.contains(n),0 <= start <= end,
        forall |j: int| start <= j <= end ==> pending(s[j],Group::Inv(n))
    ensures rank(s[end],n) <= rank(s[start],n)
    decreases end-start
{
    if end > start {
        rank_until(s,c,n,start,end-1);
        control::safety_at(s,c,end-1);
        let i=end-1;
        assert(next(s[i],s[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(s[end-1],c,a) && s[end] == apply(s[end-1],c,a);
        step_rank(s[end-1],c,a,n);
    }
}
pub proof fn progress_at(b: Behavior<LState>,c: Constants,n: int,start: int)
    requires fair_spec(b,c),c.nodes.contains(n),start >= 0
    ensures clear_after(b,Group::Inv(n),start)
    decreases rank(b[start],n)
{
    if !clear_after(b,Group::Inv(n),start) {
        assert(weak_fair(b,c,Group::Inv(n)));
        assert(fair_after(b,c,Group::Inv(n),start));
        let k=choose |k: int| k >= start && #[trigger] fair_event(b,c,Group::Inv(n),k);
        control::safety_at(b,c,k);
        pending_enabled(b[k],c,n);
        rank_until(b,c,n,start,k);
        let a=choose |a: Action| handles(Group::Inv(n),a) && #[trigger] enabled(b[k],c,a) && b[k+1] == apply(b[k],c,a);
        step_rank(b[k],c,a,n);
        progress_at(b,c,n,k+1);
        let j=choose |j: int| j >= k+1 && !pending(b[j],Group::Inv(n));
        assert(j >= start && !pending(b[j],Group::Inv(n)));
    }
}
pub proof fn inv_progress_correct(b: Behavior<LState>,c: Constants)
    requires fair_spec(b,c)
    ensures forall |n: int| c.nodes.contains(n) ==> #[trigger] progress(b,Group::Inv(n))
{
    assert forall |n: int,start: int| c.nodes.contains(n) && start >= 0 implies
        #[trigger] clear_after(b,Group::Inv(n),start) by { progress_at(b,c,n,start); }
}
} // verus!
