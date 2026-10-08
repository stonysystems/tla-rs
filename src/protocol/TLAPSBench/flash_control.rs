//! Directory work is serialized across forwarding and invalidation phases.
use vstd::prelude::*;
use super::flash::*;
use super::flash_coherence as coherence;
use super::temporal::Behavior;
verus! {
pub enum Work { Forward(int),Nak,Shared,HomeReply,Invalidating }
pub open spec fn forwarding(s: LState,p: int) -> bool {
    (s.uni[p].cmd == Uni::Get || s.uni[p].cmd == Uni::GetX) && s.uni[p].node != s.home
}
pub open spec fn work(s: LState,c: Constants,w: Work) -> bool {
    match w {
        Work::Forward(p) => c.nodes.contains(p) && forwarding(s,p),
        Work::Nak => s.nakc,
        Work::Shared => s.shwb.cmd != Shared::None,
        Work::HomeReply => s.uni[s.home].cmd == Uni::Put || s.uni[s.home].cmd == Uni::PutX,
        Work::Invalidating => s.collecting,
    }
}
pub open spec fn serialized(s: LState,c: Constants) -> bool {
    (forall |w: Work| #[trigger] work(s,c,w) ==> s.dir.pending)
    && forall |w: Work,v: Work| #[trigger] work(s,c,w) && #[trigger] work(s,c,v) ==> w == v
}
pub open spec fn home_location(s: LState) -> bool {
    (s.dir.local && s.dir.dirty ==> s.procs[s.home].cache == Cache::E)
    && (s.procs[s.home].cache == Cache::E ==> s.dir.local)
}
pub open spec fn forward_metadata(s: LState,p: int) -> bool {
    forwarding(s,p) ==> !s.dir.local && s.pending_src == p && s.forward_cmd == s.uni[p].cmd
}
pub open spec fn invalidation_metadata(s: LState,p: int) -> bool {
    s.inv[p] != Inv::None ==> p != s.home && s.collecting && s.dir.invalidating.contains(p)
}
pub open spec fn grant_metadata(s: LState,p: int) -> bool {
    s.collecting && s.uni[p].cmd == Uni::PutX ==> s.uni[p].node == s.home && s.pending_src == p
}
pub open spec fn control(s: LState,c: Constants) -> bool {
    home_location(s) && serialized(s,c) && (s.collecting ==> !s.dir.sharers_valid)
    && (forall |p: int| c.nodes.contains(p) ==> #[trigger] forward_metadata(s,p))
    && (forall |p: int| c.nodes.contains(p) ==> #[trigger] invalidation_metadata(s,p))
    && (forall |p: int| c.nodes.contains(p) ==> #[trigger] grant_metadata(s,p))
}
pub open spec fn inductive(s: LState,c: Constants) -> bool { coherence::inductive(s,c) && control(s,c) }
pub proof fn initial_inductive(c: Constants,home: int,data: int)
    requires c.nodes.contains(home),c.data.contains(data)
    ensures inductive(initial(c,home,data),c)
{ coherence::initial_inductive(c,home,data); }
pub proof fn expose_work(s: LState,c: Constants,w: Work)
    requires control(s,c)
    ensures work(s,c,w) ==> s.dir.pending,
        forall |v: Work| work(s,c,w) && #[trigger] work(s,c,v) ==> w == v
{}
pub proof fn expose_node(s: LState,c: Constants,p: int)
    requires inductive(s,c)
    ensures c.nodes.contains(p) ==> forward_metadata(s,p) && invalidation_metadata(s,p) && grant_metadata(s,p),
        work(s,c,Work::Forward(p)) ==> s.dir.pending,
        forall |v: Work| work(s,c,Work::Forward(p)) && #[trigger] work(s,c,v) ==> Work::Forward(p) == v,
        coherence::owns(s,c,coherence::Owner::Cache(p)) ==> s.dir.dirty,
        coherence::owns(s,c,coherence::Owner::Grant(p)) ==> s.dir.dirty,
        forall |o: coherence::Owner| coherence::owns(s,c,coherence::Owner::Cache(p)) && #[trigger] coherence::owns(s,c,o) ==> coherence::Owner::Cache(p) == o
{
    assert(control(s,c));
    expose_work(s,c,Work::Forward(p)); coherence::expose_node(s,c,p);
}
pub proof fn preserve_serialized(s: LState,c: Constants,a: Action,w: Work,v: Work)
    requires inductive(s,c),enabled(s,c,a)
    ensures work(apply(s,c,a),c,w) ==> apply(s,c,a).dir.pending,
        work(apply(s,c,a),c,w) && work(apply(s,c,a),c,v) ==> w == v
{
    reveal(enabled); reveal(apply);
    expose_work(s,c,Work::Nak); expose_work(s,c,Work::Shared); expose_work(s,c,Work::HomeReply); expose_work(s,c,Work::Invalidating);
    expose_node(s,c,s.home);
    coherence::expose_owner(s,c,coherence::Owner::Cache(s.home));
    coherence::expose_owner(s,c,coherence::Owner::Writeback); coherence::expose_owner(s,c,coherence::Owner::SharedWriteback); coherence::expose_owner(s,c,coherence::Owner::HomePut);
    expose_work(s,c,w); expose_work(s,c,v); assert(work(s,c,w) && work(s,c,v) ==> w == v);
    assert(work(s,c,w) && work(s,c,Work::Nak) ==> w == Work::Nak);
    assert(work(s,c,w) && work(s,c,Work::Shared) ==> w == Work::Shared);
    assert(work(s,c,w) && work(s,c,Work::HomeReply) ==> w == Work::HomeReply);
    assert(work(s,c,w) && work(s,c,Work::Invalidating) ==> w == Work::Invalidating);
    assert(work(s,c,v) && work(s,c,Work::Nak) ==> v == Work::Nak);
    assert(work(s,c,v) && work(s,c,Work::Shared) ==> v == Work::Shared);
    assert(work(s,c,v) && work(s,c,Work::HomeReply) ==> v == Work::HomeReply);
    assert(work(s,c,v) && work(s,c,Work::Invalidating) ==> v == Work::Invalidating);
    let u=apply(s,c,a);
    match a {
        Action::Store { src,data } => { expose_node(s,c,src); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::RemoteRequest { src,exclusive } => { expose_node(s,c,src); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::LocalForward { exclusive } => { assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::LocalGet => { assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::LocalGetX => { assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::RemoteWriteback { dst } => { expose_node(s,c,dst); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::LocalWriteback => { assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::RemoteReplace { src } => { expose_node(s,c,src); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::LocalReplace => { assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::ReceiveNak { dst } => { expose_node(s,c,dst); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::ClearNak => { assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::LocalNak { src,exclusive } => { expose_node(s,c,src); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::LocalRelay { src,exclusive } => { expose_node(s,c,src); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::LocalGrant { src,exclusive } => { expose_node(s,c,src); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::RemoteNak { src,dst } => { assert(work(s,c,Work::Forward(src))); assert(work(s,c,w) ==> w == Work::Forward(src)); assert(work(s,c,v) ==> v == Work::Forward(src)); expose_node(s,c,src); expose_node(s,c,dst); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::RemoteGrant { src,dst,exclusive } => { assert(work(s,c,Work::Forward(src))); assert(work(s,c,w) ==> w == Work::Forward(src)); assert(work(s,c,v) ==> v == Work::Forward(src)); expose_node(s,c,src); expose_node(s,c,dst); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::ReceivePut { dst } => { expose_node(s,c,dst); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::ReceivePutX { dst } => { expose_node(s,c,dst); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::Invalidate { dst } => { expose_node(s,c,dst); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::InvalidateAck { src } => { expose_node(s,c,src); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::ReceiveWriteback => { assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::ReceiveForwardAck => { assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::ReceiveSharedWriteback => { assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::ReceiveReplace { src } => { expose_node(s,c,src); assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
        Action::Stutter => { assert(work(u,c,w) ==> u.dir.pending); assert(work(u,c,w) && work(u,c,v) ==> w == v); },
    }

}
pub proof fn preserve_metadata(s: LState,c: Constants,a: Action,p: int)
    requires inductive(s,c),enabled(s,c,a),c.nodes.contains(p)
    ensures forward_metadata(apply(s,c,a),p),invalidation_metadata(apply(s,c,a),p),grant_metadata(apply(s,c,a),p)
{
    reveal(enabled); reveal(apply);
    expose_work(s,c,Work::Nak); expose_work(s,c,Work::Shared); expose_work(s,c,Work::HomeReply); expose_work(s,c,Work::Invalidating);
    expose_node(s,c,s.home);
    coherence::expose_owner(s,c,coherence::Owner::Cache(s.home));
    coherence::expose_owner(s,c,coherence::Owner::Writeback); coherence::expose_owner(s,c,coherence::Owner::SharedWriteback); coherence::expose_owner(s,c,coherence::Owner::HomePut);
    expose_node(s,c,p); expose_work(s,c,Work::Forward(p));
    assert(work(s,c,Work::Forward(p)) && work(s,c,Work::Nak) ==> Work::Forward(p) == Work::Nak);
    assert(work(s,c,Work::Forward(p)) && work(s,c,Work::Shared) ==> Work::Forward(p) == Work::Shared);
    assert(work(s,c,Work::Forward(p)) && work(s,c,Work::HomeReply) ==> Work::Forward(p) == Work::HomeReply);
    assert(work(s,c,Work::Forward(p)) && work(s,c,Work::Invalidating) ==> Work::Forward(p) == Work::Invalidating);
    assert(work(s,c,Work::Invalidating) && work(s,c,Work::Nak) ==> Work::Invalidating == Work::Nak);
    assert(work(s,c,Work::Invalidating) && work(s,c,Work::Shared) ==> Work::Invalidating == Work::Shared);
    assert(work(s,c,Work::Invalidating) && work(s,c,Work::HomeReply) ==> Work::Invalidating == Work::HomeReply);
    assert(work(s,c,Work::Invalidating) && work(s,c,Work::Invalidating) ==> Work::Invalidating == Work::Invalidating);
    let u=apply(s,c,a);
    match a {
        Action::Store { src,data } => { expose_node(s,c,src); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::RemoteRequest { src,exclusive } => { expose_node(s,c,src); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::LocalForward { exclusive } => { assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::LocalGet => { assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::LocalGetX => { assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::RemoteWriteback { dst } => { expose_node(s,c,dst); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::LocalWriteback => { assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::RemoteReplace { src } => { expose_node(s,c,src); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::LocalReplace => { assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::ReceiveNak { dst } => { expose_node(s,c,dst); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::ClearNak => { assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::LocalNak { src,exclusive } => { expose_node(s,c,src); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::LocalRelay { src,exclusive } => { expose_node(s,c,src); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::LocalGrant { src,exclusive } => { expose_node(s,c,src); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::RemoteNak { src,dst } => { expose_node(s,c,src); expose_node(s,c,dst); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::RemoteGrant { src,dst,exclusive } => { assert(work(s,c,Work::Forward(src))); assert(work(s,c,Work::Forward(src)) && work(s,c,Work::Invalidating) ==> Work::Forward(src) == Work::Invalidating); expose_node(s,c,src); expose_node(s,c,dst); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::ReceivePut { dst } => { expose_node(s,c,dst); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::ReceivePutX { dst } => { expose_node(s,c,dst); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::Invalidate { dst } => { expose_node(s,c,dst); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::InvalidateAck { src } => { expose_node(s,c,src); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::ReceiveWriteback => { assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::ReceiveForwardAck => { assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::ReceiveSharedWriteback => { assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::ReceiveReplace { src } => { expose_node(s,c,src); assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
        Action::Stutter => { assert(forward_metadata(u,p)); assert(invalidation_metadata(u,p)); assert(grant_metadata(u,p)); },
    }

}
pub proof fn preserve_home(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures home_location(apply(s,c,a)),apply(s,c,a).collecting ==> !apply(s,c,a).dir.sharers_valid
{
    reveal(enabled); reveal(apply);
    expose_work(s,c,Work::Nak); expose_work(s,c,Work::Shared); expose_work(s,c,Work::HomeReply); expose_work(s,c,Work::Invalidating);
    expose_node(s,c,s.home);
    coherence::expose_owner(s,c,coherence::Owner::Cache(s.home));
    coherence::expose_owner(s,c,coherence::Owner::Writeback); coherence::expose_owner(s,c,coherence::Owner::SharedWriteback); coherence::expose_owner(s,c,coherence::Owner::HomePut);
    
    assert(work(s,c,Work::Invalidating) && work(s,c,Work::Nak) ==> Work::Invalidating == Work::Nak);
    assert(work(s,c,Work::Invalidating) && work(s,c,Work::Shared) ==> Work::Invalidating == Work::Shared);
    assert(work(s,c,Work::Invalidating) && work(s,c,Work::HomeReply) ==> Work::Invalidating == Work::HomeReply);
    assert(work(s,c,Work::Invalidating) && work(s,c,Work::Invalidating) ==> Work::Invalidating == Work::Invalidating);
    let u=apply(s,c,a);
    match a {
        Action::Store { src,data } => { expose_node(s,c,src); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::RemoteRequest { src,exclusive } => { expose_node(s,c,src); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::LocalForward { exclusive } => { assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::LocalGet => { assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::LocalGetX => { assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::RemoteWriteback { dst } => { expose_node(s,c,dst); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::LocalWriteback => { assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::RemoteReplace { src } => { expose_node(s,c,src); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::LocalReplace => { assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::ReceiveNak { dst } => { expose_node(s,c,dst); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::ClearNak => { assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::LocalNak { src,exclusive } => { expose_node(s,c,src); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::LocalRelay { src,exclusive } => { expose_node(s,c,src); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::LocalGrant { src,exclusive } => { expose_node(s,c,src); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::RemoteNak { src,dst } => { expose_node(s,c,src); expose_node(s,c,dst); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::RemoteGrant { src,dst,exclusive } => { expose_node(s,c,src); expose_node(s,c,dst); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::ReceivePut { dst } => { expose_node(s,c,dst); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::ReceivePutX { dst } => { expose_node(s,c,dst); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::Invalidate { dst } => { expose_node(s,c,dst); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::InvalidateAck { src } => { expose_node(s,c,src); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::ReceiveWriteback => { assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::ReceiveForwardAck => { assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::ReceiveSharedWriteback => { assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::ReceiveReplace { src } => { expose_node(s,c,src); assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
        Action::Stutter => { assert(home_location(u)); assert(u.collecting ==> !u.dir.sharers_valid); },
    }

}
pub proof fn preserve_inductive(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    coherence::preserve_inductive(s,c,a); preserve_home(s,c,a);
    let u=apply(s,c,a);
    assert forall |w: Work| #[trigger] work(u,c,w) implies u.dir.pending by { preserve_serialized(s,c,a,w,w); }
    assert forall |w: Work,v: Work| #[trigger] work(u,c,w) && #[trigger] work(u,c,v) implies w == v by { preserve_serialized(s,c,a,w,v); }
    assert(serialized(u,c));
    assert forall |p: int| c.nodes.contains(p) implies #[trigger] forward_metadata(u,p) by { preserve_metadata(s,c,a,p); }
    assert forall |p: int| c.nodes.contains(p) implies #[trigger] invalidation_metadata(u,p) by { preserve_metadata(s,c,a,p); }
    assert forall |p: int| c.nodes.contains(p) implies #[trigger] grant_metadata(u,p) by { preserve_metadata(s,c,a,p); }
    assert(control(u,c));
}
pub proof fn goals_from_inductive(s: LState,c: Constants)
    requires inductive(s,c)
    ensures lemma_2_3(s,c,false),lemma_2_3(s,c,true),lemma_4(s,c)
{
    assert forall |src: int,dst: int| #![trigger c.nodes.contains(src), c.nodes.contains(dst)] c.nodes.contains(src) && c.nodes.contains(dst) && src != dst && dst != s.home
        && s.uni[src].cmd == Uni::Get && s.uni[src].node == dst implies
        s.dir.pending && !s.dir.local && s.pending_src == src && s.forward_cmd == Uni::Get by {
        expose_node(s,c,src); assert(work(s,c,Work::Forward(src)));
    }
    assert forall |src: int,dst: int| #![trigger c.nodes.contains(src), c.nodes.contains(dst)] c.nodes.contains(src) && c.nodes.contains(dst) && src != dst && dst != s.home
        && s.uni[src].cmd == Uni::GetX && s.uni[src].node == dst implies
        s.dir.pending && !s.dir.local && s.pending_src == src && s.forward_cmd == Uni::GetX by {
        expose_node(s,c,src); assert(work(s,c,Work::Forward(src)));
    }
    expose_work(s,c,Work::Invalidating); expose_work(s,c,Work::Nak); expose_work(s,c,Work::Shared);
    assert forall |p: int| #![trigger s.inv[p]] c.nodes.contains(p) && p != s.home && s.inv[p] == Inv::Ack implies
        s.dir.pending && s.collecting && !s.nakc && s.shwb.cmd == Shared::None
        && (forall |q: int| #![trigger c.nodes.contains(q)] c.nodes.contains(q) ==>
            ((s.uni[q].cmd == Uni::Get || s.uni[q].cmd == Uni::GetX) ==> s.uni[q].node == s.home)
            && (s.uni[q].cmd == Uni::PutX ==> s.uni[q].node == s.home && s.pending_src == q)) by {
        expose_node(s,c,p);
        assert(work(s,c,Work::Invalidating));
        assert forall |q: int| #![trigger c.nodes.contains(q)] c.nodes.contains(q) implies
            ((s.uni[q].cmd == Uni::Get || s.uni[q].cmd == Uni::GetX) ==> s.uni[q].node == s.home)
            && (s.uni[q].cmd == Uni::PutX ==> s.uni[q].node == s.home && s.pending_src == q) by {
            expose_node(s,c,q);
            assert(work(s,c,Work::Forward(q)) ==> Work::Invalidating == Work::Forward(q));
        }
    }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires super::flash_liveness::safety_spec(b,c),k >= 0
    ensures inductive(b[k],c),lemma_2_3(b[k],c,false),lemma_2_3(b[k],c,true),lemma_4(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c,b[0].home,b[0].current); }
    else {
        safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve_inductive(b[i],c,a);
    }
    goals_from_inductive(b[k],c);
}
pub proof fn benchmark_control(b: Behavior<LState>,c: Constants)
    requires super::flash_liveness::safety_spec(b,c)
    ensures forall |k: int| k >= 0 ==> #[trigger] lemma_2_3(b[k],c,false),
        forall |k: int| k >= 0 ==> #[trigger] lemma_2_3(b[k],c,true),
        forall |k: int| k >= 0 ==> #[trigger] lemma_4(b[k],c)
{
    assert forall |k: int| k >= 0 implies #[trigger] lemma_2_3(b[k],c,false) by { safety_at(b,c,k); }
    assert forall |k: int| k >= 0 implies #[trigger] lemma_2_3(b[k],c,true) by { safety_at(b,c,k); }
    assert forall |k: int| k >= 0 implies #[trigger] lemma_4(b[k],c) by { safety_at(b,c,k); }
}
} // verus!
