//! Request routing and a finite rank for the source's unicast action group.
use vstd::prelude::*;
use super::flash::*;
use super::flash_shared as shared;
use super::flash_liveness::*;
use super::temporal::Behavior;
verus! {
pub open spec fn routed(s: LState,c: Constants,p: int) -> bool {
    (s.uni[p].cmd == Uni::Get || s.uni[p].cmd == Uni::GetX) ==>
        c.nodes.contains(s.uni[p].node) && s.uni[p].node != p
}
pub open spec fn directory(s: LState,c: Constants) -> bool {
    (s.dir.dirty && !s.dir.local ==> s.dir.head_valid)
    && (s.dir.head_valid ==> c.nodes.contains(s.dir.head))
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    shared::inductive(s,c) && directory(s,c)
    && forall |p: int| c.nodes.contains(p) ==> #[trigger] routed(s,c,p)
}
pub proof fn initial_inductive(c: Constants,home: int,data: int)
    requires c.nodes.contains(home),c.data.contains(data)
    ensures inductive(initial(c,home,data),c)
{ shared::initial_inductive(c,home,data); }
pub proof fn preserve_node(s: LState,c: Constants,a: Action,p: int)
    requires inductive(s,c),enabled(s,c,a),c.nodes.contains(p)
    ensures routed(apply(s,c,a),c,p),directory(apply(s,c,a),c)
{
    reveal(enabled); reveal(apply);
    assert(routed(s,c,p));
    shared::expose(s,c,p); shared::expose(s,c,s.home);
    match a {
        Action::Store { src,.. } | Action::RemoteRequest { src,.. } | Action::RemoteReplace { src }
        | Action::LocalNak { src,.. } | Action::LocalRelay { src,.. } | Action::LocalGrant { src,.. }
        | Action::InvalidateAck { src } | Action::ReceiveReplace { src } => { shared::expose(s,c,src); },
        Action::RemoteWriteback { dst } | Action::ReceiveNak { dst } | Action::ReceivePut { dst }
        | Action::ReceivePutX { dst } | Action::Invalidate { dst } => { shared::expose(s,c,dst); },
        Action::RemoteNak { src,dst } | Action::RemoteGrant { src,dst,.. } => { shared::expose(s,c,src); shared::expose(s,c,dst); },
        _ => {},
    }
}
pub proof fn preserve_inductive(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    shared::preserve_inductive(s,c,a); preserve_node(s,c,a,s.home);
    let u=apply(s,c,a);
    assert forall |p: int| c.nodes.contains(p) implies #[trigger] routed(u,c,p) by { preserve_node(s,c,a,p); }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires safety_spec(b,c),k >= 0
    ensures inductive(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c,b[0].home,b[0].current); }
    else {
        safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve_inductive(b[i],c,a);
    }
}
pub open spec fn rank(s: LState,n: int) -> nat {
    match s.uni[n].cmd {
        Uni::None => 0,Uni::Put | Uni::PutX | Uni::Nak => 1,
        _ => if s.uni[n].node == s.home { 3 } else { 2 },
    }
}
pub proof fn pending_enabled(s: LState,c: Constants,n: int)
    requires inductive(s,c),c.nodes.contains(n),pending(s,Group::Uni(n)),!s.replace[n]
    ensures group_enabled(s,c,Group::Uni(n))
{
    shared::expose(s,c,n); shared::expose(s,c,s.home); assert(routed(s,c,n));
    reveal(enabled); reveal(apply);
    let x=s.uni[n].cmd == Uni::GetX;
    let dst=s.uni[n].node;
    let a=match s.uni[n].cmd {
        Uni::Put => Action::ReceivePut { dst: n },
        Uni::PutX => Action::ReceivePutX { dst: n },
        Uni::Nak => Action::ReceiveNak { dst: n },
        _ => if dst != s.home {
            if s.procs[dst].cache == Cache::E { Action::RemoteGrant { src: n,dst,exclusive: x } }
            else { Action::RemoteNak { src: n,dst } }
        } else if s.dir.pending || s.dir.dirty && s.dir.local && s.procs[s.home].cache != Cache::E
            || s.dir.dirty && !s.dir.local && s.dir.head == n { Action::LocalNak { src: n,exclusive: x } }
        else if s.dir.dirty && !s.dir.local { Action::LocalRelay { src: n,exclusive: x } }
        else { Action::LocalGrant { src: n,exclusive: x } },
    };
    assert(handles(Group::Uni(n),a) && enabled(s,c,a) && apply(s,c,a) != s);
}
pub proof fn step_rank(s: LState,c: Constants,a: Action,n: int)
    requires inductive(s,c),c.nodes.contains(n),pending(s,Group::Uni(n)),enabled(s,c,a)
    ensures rank(apply(s,c,a),n) <= rank(s,n),
        !s.replace[n] ==> !apply(s,c,a).replace[n],
        handles(Group::Uni(n),a) ==> rank(apply(s,c,a),n) < rank(s,n)
{
    shared::expose(s,c,n); shared::expose(s,c,s.home);
    reveal(enabled); reveal(apply);
    match a {
        Action::LocalRelay { src,exclusive } => {},
        _ => {},
    }
}
pub proof fn rank_until(b: Behavior<LState>,c: Constants,n: int,start: int,end: int)
    requires safety_spec(b,c),c.nodes.contains(n),0 <= start <= end,
        forall |j: int| #![trigger b[j]] start <= j <= end ==> pending(b[j],Group::Uni(n))
    ensures rank(b[end],n) <= rank(b[start],n),!b[start].replace[n] ==> !b[end].replace[n]
    decreases end-start
{
    if end > start {
        rank_until(b,c,n,start,end-1); safety_at(b,c,end-1);
        let i=end-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        step_rank(b[i],c,a,n);
    }
}
pub proof fn progress_at(b: Behavior<LState>,c: Constants,n: int,start: int)
    requires fair_spec(b,c),c.nodes.contains(n),start >= 0
    ensures clear_after(b,Group::Uni(n),start)
    decreases rank(b[start],n)
{
    if !clear_after(b,Group::Uni(n),start) {
        super::flash_liveness::progress_at(b,c,Group::Replace(n),start);
        let j=choose |j: int| #![trigger b[j]] j >= start && !pending(b[j],Group::Replace(n));
        assert(weak_fair(b,c,Group::Uni(n)));
        assert(fair_after(b,c,Group::Uni(n),j));
        let k=choose |k: int| k >= j && #[trigger] fair_event(b,c,Group::Uni(n),k);
        safety_at(b,c,k);
        rank_until(b,c,n,j,k);
        pending_enabled(b[k],c,n);
        rank_until(b,c,n,start,k);
        let a=choose |a: Action| handles(Group::Uni(n),a) && #[trigger] enabled(b[k],c,a) && b[k+1] == apply(b[k],c,a);
        step_rank(b[k],c,a,n);
        progress_at(b,c,n,k+1);
        let q=choose |q: int| #![trigger b[q]] q >= k+1 && !pending(b[q],Group::Uni(n));
        assert(q >= start && !pending(b[q],Group::Uni(n)));
    }
}
pub open spec fn request_clear_after(b: Behavior<LState>,n: int,start: int) -> bool {
    exists |k: int| #![trigger b[k]] k >= start && b[k].procs[n].cmd == Req::None
}
pub proof fn request_progress_correct(b: Behavior<LState>,c: Constants)
    requires fair_spec(b,c)
    ensures forall |n: int| c.nodes.contains(n) ==> #[trigger] progress(b,Group::Uni(n)),
        forall |n: int,start: int| c.nodes.contains(n) && start >= 0 && b[start].procs[n].cmd != Req::None ==>
            #[trigger] request_clear_after(b,n,start)
{
    assert forall |n: int,start: int| c.nodes.contains(n) && start >= 0 implies
        #[trigger] clear_after(b,Group::Uni(n),start) by { progress_at(b,c,n,start); }
    assert forall |n: int,start: int| c.nodes.contains(n) && start >= 0 implies
        #[trigger] request_clear_after(b,n,start) by {
        progress_at(b,c,n,start);
        let k=choose |k: int| #![trigger b[k]] k >= start && !pending(b[k],Group::Uni(n));
        safety_at(b,c,k); shared::expose(b[k],c,n);
        assert(b[k].procs[n].cmd == Req::None);
    }
}
} // verus!
