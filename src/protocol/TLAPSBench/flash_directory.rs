//! Pending directory operations terminate: forwarded requests produce replies,
//! replies clear the lock, and finite invalidation sets shrink to empty.
use vstd::prelude::*;
use super::flash::*;
use super::flash_control::{self as control,Work,work};
use super::flash_shared as shared;
use super::flash_requests as requests;
use super::flash_liveness::*;
use super::temporal::Behavior;
verus! {
pub open spec fn directory(s: LState,c: Constants) -> bool {
    !s.dir.sharers.contains(s.home)
    && (!s.dir.sharers_valid ==> s.dir.sharers.is_empty())
    && (s.collecting ==> !s.dir.invalidating.is_empty())
    && (s.dir.pending ==> exists |w: Work| #[trigger] work(s,c,w))
}
pub open spec fn outstanding(s: LState,p: int) -> bool {
    s.collecting && s.dir.invalidating.contains(p) ==> s.inv[p] != Inv::None
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    requests::inductive(s,c) && directory(s,c)
    && forall |p: int| c.nodes.contains(p) ==> #[trigger] outstanding(s,p)
}
pub proof fn initial_inductive(c: Constants,home: int,data: int)
    requires c.nodes.contains(home),c.data.contains(data)
    ensures inductive(initial(c,home,data),c)
{ requests::initial_inductive(c,home,data); }
pub proof fn preserve_node(s: LState,c: Constants,a: Action,p: int)
    requires inductive(s,c),enabled(s,c,a),c.nodes.contains(p)
    ensures outstanding(apply(s,c,a),p)
{
    shared::expose(s,c,p); shared::expose(s,c,s.home);
    control::expose_work(s,c,Work::Invalidating);
    assert(outstanding(s,p));
    assert(work(s,c,Work::Invalidating) && work(s,c,Work::Shared) ==> false);
    reveal(enabled); reveal(apply);
}
pub proof fn preserve_work(s: LState,c: Constants,a: Action,w: Work)
    requires inductive(s,c),enabled(s,c,a),work(s,c,w),apply(s,c,a).dir.pending
    ensures exists |v: Work| #[trigger] work(apply(s,c,a),c,v)
{
    reveal(enabled); reveal(apply);
    control::expose_work(s,c,w); shared::expose(s,c,s.home);
    match w {
        Work::Forward(p) => { shared::expose(s,c,p); assert(requests::routed(s,c,p)); },
        _ => {},
    }
    let u=apply(s,c,a);
    match a {
        Action::RemoteNak { src,dst } => { assert(work(u,c,Work::Nak)); },
        Action::RemoteGrant { src,dst,exclusive } => {
            if src == s.home { assert(work(u,c,Work::HomeReply)); }
            else { assert(work(u,c,Work::Shared)); }
        },
        _ => { assert(work(u,c,w)); },
    }
}
pub proof fn preserve_directory(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures directory(apply(s,c,a),c)
{
    reveal(enabled); reveal(apply);
    shared::expose(s,c,s.home);
    control::expose_work(s,c,Work::Nak); control::expose_work(s,c,Work::Shared);
    control::expose_work(s,c,Work::HomeReply); control::expose_work(s,c,Work::Invalidating);
    let u=apply(s,c,a);
    if s.dir.pending {
        let w=choose |w: Work| #[trigger] work(s,c,w);
        if u.dir.pending { preserve_work(s,c,a,w); }
    }
    match a {
        Action::Store { src,.. } | Action::RemoteRequest { src,.. } | Action::RemoteReplace { src }
        | Action::LocalNak { src,.. } | Action::LocalRelay { src,.. } | Action::LocalGrant { src,.. }
        | Action::InvalidateAck { src } | Action::ReceiveReplace { src } => { shared::expose(s,c,src); },
        Action::RemoteWriteback { dst } | Action::ReceiveNak { dst } | Action::ReceivePut { dst }
        | Action::ReceivePutX { dst } | Action::Invalidate { dst } => { shared::expose(s,c,dst); },
        Action::RemoteNak { src,dst } | Action::RemoteGrant { src,dst,.. } => { shared::expose(s,c,src); shared::expose(s,c,dst); },
        _ => {},
    }
    match a {
        Action::LocalForward { exclusive } => { assert(work(u,c,Work::Forward(s.home))); },
        Action::LocalRelay { src,exclusive } => { assert(work(u,c,Work::Forward(src))); },
        Action::LocalGetX => {
            if s.dir.head_valid { assert(inv_nodes(s,c,set![s.home]).contains(s.dir.head)); }
            assert(u.dir.pending ==> work(u,c,Work::Invalidating));
        },
        Action::LocalGrant { src,exclusive } => {
            if exclusive && !s.dir.dirty && !no_other_sharers(s,src) {
                if s.dir.head != src { assert(inv_nodes(s,c,set![s.home,src]).contains(s.dir.head)); }
                else {
                    let p=choose |p: int| s.dir.sharers.contains(p) && p != src;
                    assert(inv_nodes(s,c,set![s.home,src]).contains(p));
                }
                assert(work(u,c,Work::Invalidating));
            }
        },
        Action::RemoteNak { src,dst } => { assert(work(u,c,Work::Nak)); },
        Action::RemoteGrant { src,dst,exclusive } => {
            if src == s.home { assert(work(u,c,Work::HomeReply)); }
            else { assert(work(u,c,Work::Shared)); }
        },
        _ => {},
    }
    assert(!u.dir.sharers.contains(u.home));
    assert(!u.dir.sharers_valid ==> u.dir.sharers.is_empty());
    assert(u.collecting ==> !u.dir.invalidating.is_empty());
    assert(u.dir.pending ==> exists |w: Work| #[trigger] work(u,c,w));
}
pub proof fn preserve_inductive(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    requests::preserve_inductive(s,c,a); preserve_directory(s,c,a);
    let u=apply(s,c,a);
    assert forall |p: int| c.nodes.contains(p) implies #[trigger] outstanding(u,p) by { preserve_node(s,c,a,p); }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires safety_spec(b,c),k >= 0
    ensures inductive(b[k],c),b[k].home == b[0].home
    decreases k
{
    if k == 0 { initial_inductive(c,b[0].home,b[0].current); }
    else {
        safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve_inductive(b[i],c,a);
        reveal(apply);
    }
}
pub open spec fn clear_after(b: Behavior<LState>,start: int) -> bool {
    exists |k: int| k >= start && !b[k].dir.pending
}
pub proof fn collecting_step(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a),s.collecting,apply(s,c,a).dir.pending
    ensures apply(s,c,a).collecting,apply(s,c,a).dir.invalidating.subset_of(s.dir.invalidating)
{
    reveal(enabled); reveal(apply);
    control::expose_work(s,c,Work::Invalidating);
    assert(work(s,c,Work::Invalidating) && work(s,c,Work::Nak) ==> false);
    assert(work(s,c,Work::Invalidating) && work(s,c,Work::Shared) ==> false);
}
pub proof fn collecting_until(b: Behavior<LState>,c: Constants,start: int,end: int)
    requires safety_spec(b,c),0 <= start <= end,b[start].collecting,
        forall |j: int| start <= j <= end ==> b[j].dir.pending
    ensures b[end].collecting,b[end].dir.invalidating.subset_of(b[start].dir.invalidating)
    decreases end-start
{
    if end > start {
        collecting_until(b,c,start,end-1); safety_at(b,c,end-1);
        let i=end-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        collecting_step(b[i],c,a);
    }
}
pub proof fn collecting_progress(b: Behavior<LState>,c: Constants,start: int)
    requires fair_spec(b,c),start >= 0,b[start].collecting
    ensures clear_after(b,start)
    decreases b[start].dir.invalidating.len()
{
    if !clear_after(b,start) {
        safety_at(b,c,start);
        let p=choose |p: int| b[start].dir.invalidating.contains(p);
        super::flash_invalidation::progress_at(b,c,p,start);
        let k=choose |k: int| k >= start && !pending(b[k],Group::Inv(p));
        collecting_until(b,c,start,k); safety_at(b,c,k);
        assert(outstanding(b[k],p));
        b[k].dir.invalidating.lemma_subset_not_in_lt(b[start].dir.invalidating,p);
        collecting_progress(b,c,k);
    }
}
pub open spec fn terminal(w: Work) -> bool {
    match w { Work::Nak | Work::Shared | Work::HomeReply => true,_ => false }
}
pub open spec fn has_terminal(s: LState,c: Constants) -> bool {
    exists |w: Work| terminal(w) && #[trigger] work(s,c,w)
}
pub proof fn terminal_step(s: LState,c: Constants,a: Action,w: Work)
    requires inductive(s,c),enabled(s,c,a),terminal(w),work(s,c,w),apply(s,c,a).dir.pending
    ensures work(apply(s,c,a),c,w)
{
    reveal(enabled); reveal(apply);
    control::expose_work(s,c,w); shared::expose(s,c,s.home);
    assert(work(s,c,Work::Invalidating) ==> w == Work::Invalidating);
    assert(work(s,c,Work::Nak) ==> w == Work::Nak);
    assert(work(s,c,Work::Shared) ==> w == Work::Shared);
    assert(work(s,c,Work::HomeReply) ==> w == Work::HomeReply);
    match a {
        Action::RemoteNak { src,dst } | Action::RemoteGrant { src,dst,.. } => {
            shared::expose(s,c,src);
            assert(work(s,c,Work::Forward(src)) ==> w == Work::Forward(src));
        },
        _ => {},
    }
}
pub proof fn terminal_until(b: Behavior<LState>,c: Constants,w: Work,start: int,end: int)
    requires safety_spec(b,c),terminal(w),0 <= start <= end,work(b[start],c,w),
        forall |j: int| start <= j <= end ==> b[j].dir.pending
    ensures work(b[end],c,w)
    decreases end-start
{
    if end > start {
        terminal_until(b,c,w,start,end-1); safety_at(b,c,end-1);
        let i=end-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        terminal_step(b[i],c,a,w);
    }
}
pub proof fn terminal_progress(b: Behavior<LState>,c: Constants,w: Work,start: int)
    requires fair_spec(b,c),terminal(w),start >= 0,work(b[start],c,w)
    ensures clear_after(b,start)
{
    if !clear_after(b,start) {
        let g=match w { Work::Nak => Group::Nakc,Work::Shared => Group::ShWb,_ => Group::Uni(b[start].home) };
        if w == Work::HomeReply {
            safety_at(b,c,start); requests::progress_at(b,c,b[start].home,start);
        } else { super::flash_liveness::progress_at(b,c,g,start); }
        let k=choose |k: int| k >= start && !pending(b[k],g);
        terminal_until(b,c,w,start,k);
        // Home is a fixed field of every protocol step.
        safety_at(b,c,k);
        assert(false);
    }
}
pub proof fn forward_step(s: LState,c: Constants,a: Action,p: int)
    requires inductive(s,c),enabled(s,c,a),work(s,c,Work::Forward(p)),
        apply(s,c,a).dir.pending,!has_terminal(apply(s,c,a),c)
    ensures work(apply(s,c,a),c,Work::Forward(p))
{
    reveal(enabled); reveal(apply);
    shared::expose(s,c,p); shared::expose(s,c,s.home);
    control::expose_work(s,c,Work::Forward(p));
    let u=apply(s,c,a);
    assert(!work(u,c,Work::Nak)); assert(!work(u,c,Work::Shared)); assert(!work(u,c,Work::HomeReply));
}
pub proof fn forward_until(b: Behavior<LState>,c: Constants,p: int,start: int,end: int)
    requires safety_spec(b,c),0 <= start <= end,work(b[start],c,Work::Forward(p)),
        forall |j: int| start <= j <= end ==> b[j].dir.pending && !has_terminal(b[j],c)
    ensures work(b[end],c,Work::Forward(p))
    decreases end-start
{
    if end > start {
        forward_until(b,c,p,start,end-1); safety_at(b,c,end-1);
        let i=end-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        forward_step(b[i],c,a,p);
    }
}
pub proof fn progress_at(b: Behavior<LState>,c: Constants,start: int)
    requires fair_spec(b,c),start >= 0
    ensures clear_after(b,start)
{
    if !clear_after(b,start) {
        safety_at(b,c,start);
        let w=choose |w: Work| #[trigger] work(b[start],c,w);
        match w {
            Work::Invalidating => { collecting_progress(b,c,start); },
            Work::Forward(p) => {
                requests::progress_at(b,c,p,start);
                let k=choose |k: int| k >= start && !pending(b[k],Group::Uni(p));
                if !(exists |j: int| start <= j <= k && has_terminal(b[j],c)) {
                    forward_until(b,c,p,start,k);
                    assert(false);
                }
                let j=choose |j: int| start <= j <= k && has_terminal(b[j],c);
                let t=choose |t: Work| terminal(t) && #[trigger] work(b[j],c,t);
                terminal_progress(b,c,t,j);
            },
            _ => { terminal_progress(b,c,w,start); },
        }
    }
}
pub proof fn dir_progress_correct(b: Behavior<LState>,c: Constants)
    requires fair_spec(b,c)
    ensures forall |start: int| start >= 0 && b[start].dir.pending ==> #[trigger] clear_after(b,start)
{
    assert forall |start: int| start >= 0 implies #[trigger] clear_after(b,start) by { progress_at(b,c,start); }
}
} // verus!
