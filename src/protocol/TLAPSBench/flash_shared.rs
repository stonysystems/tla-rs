//! Shared copies and unconsumed read replies are registered in the directory
//! or covered by an outstanding invalidation. Their data is tracked together.
use vstd::prelude::*;
use super::flash::*;
use super::flash_control as control;
use super::flash_coherence as coherence;
use super::temporal::Behavior;
verus! {
pub open spec fn has_shared(s: LState,p: int) -> bool {
    s.procs[p].cache == Cache::S || s.uni[p].cmd == Uni::Put && !s.procs[p].marked
}
pub open spec fn registered(s: LState,p: int) -> bool {
    if p == s.home { s.dir.local || s.uni[s.home].cmd == Uni::Put }
    else { s.dir.head_valid && s.dir.head == p || s.dir.sharers_valid && s.dir.sharers.contains(p)
        || s.shwb.cmd == Shared::ShWb && s.shwb.node == p }
}
pub open spec fn requests(s: LState,p: int) -> bool {
    (s.procs[p].cmd == Req::None <==> s.uni[p].cmd == Uni::None)
    && ((s.uni[p].cmd == Uni::Get || s.uni[p].cmd == Uni::Put) ==> s.procs[p].cmd == Req::Get)
    && ((s.uni[p].cmd == Uni::GetX || s.uni[p].cmd == Uni::PutX) ==> s.procs[p].cmd == Req::GetX)
    && (s.procs[p].marked ==> s.procs[p].cmd == Req::Get && s.procs[p].cache == Cache::I)
    && (s.procs[p].cmd != Req::None ==> s.procs[p].cache != Cache::E)
    && (p != s.home && s.procs[p].cmd != Req::None ==> s.procs[p].cache == Cache::I)
    && (s.procs[p].cmd == Req::Get ==> s.procs[p].cache == Cache::I)
    && (s.uni[p].cmd == Uni::Put ==> !s.replace[p])
    && (control::forwarding(s,p) && s.uni[p].cmd == Uni::Get ==> !s.replace[p])
}
pub open spec fn location(s: LState,p: int) -> bool {
    (p != s.home && (s.procs[p].cache == Cache::E || s.uni[p].cmd == Uni::PutX) ==>
        !s.dir.local && s.dir.head_valid && (s.dir.head == p || s.shwb.cmd == Shared::FAck && s.shwb.node == p))
    && (s.shwb.cmd == Shared::FAck && (s.procs[p].cache == Cache::E || s.uni[p].cmd == Uni::PutX) ==> s.shwb.node == p)
}
pub open spec fn shared_info(s: LState,p: int) -> bool {
    (has_shared(s,p) && !s.collecting ==> registered(s,p))
    && (has_shared(s,p) && s.collecting ==> p != s.home && p != s.pending_src && s.inv[p] == Inv::Inv)
    && (has_shared(s,p) && !s.collecting && s.dir.dirty ==> s.shwb.cmd == Shared::ShWb || s.uni[s.home].cmd == Uni::Put)
    && (s.replace[p] && s.procs[p].cache == Cache::S && !s.collecting ==> s.dir.head_valid && s.dir.head == p)
}
pub open spec fn data_info(s: LState,p: int) -> bool {
    let data=if s.collecting { s.previous } else { s.current };
    (s.procs[p].cache == Cache::S ==> s.procs[p].data == data)
    && (s.uni[p].cmd == Uni::Put && !s.procs[p].marked ==> s.uni[p].data == data)
}
pub open spec fn directory(s: LState,c: Constants) -> bool {
    !s.replace[s.home]
    && (s.dir.head_valid ==> s.dir.head != s.home)
    && (s.dir.sharers_valid ==> s.dir.head_valid && !s.dir.dirty)
    && (s.shwb.cmd == Shared::ShWb ==> s.dir.head_valid)
    && (s.shwb.cmd != Shared::None ==> c.nodes.contains(s.shwb.node) && s.shwb.node != s.home)
}
pub open spec fn shared_inductive(s: LState,c: Constants) -> bool {
    directory(s,c)
    && (forall |p: int| c.nodes.contains(p) ==> #[trigger] requests(s,p))
    && (forall |p: int| c.nodes.contains(p) ==> #[trigger] location(s,p))
    && (forall |p: int| c.nodes.contains(p) ==> #[trigger] shared_info(s,p))
    && (forall |p: int| c.nodes.contains(p) ==> #[trigger] data_info(s,p))
}
pub open spec fn inductive(s: LState,c: Constants) -> bool { control::inductive(s,c) && shared_inductive(s,c) }
pub proof fn initial_inductive(c: Constants,home: int,data: int)
    requires c.nodes.contains(home),c.data.contains(data)
    ensures inductive(initial(c,home,data),c)
{ control::initial_inductive(c,home,data); }
pub proof fn expose(s: LState,c: Constants,p: int)
    requires inductive(s,c)
    ensures c.nodes.contains(p) ==> requests(s,p) && location(s,p) && shared_info(s,p) && data_info(s,p),
        c.nodes.contains(p) ==> control::forward_metadata(s,p) && control::invalidation_metadata(s,p) && control::grant_metadata(s,p),
        coherence::owns(s,c,coherence::Owner::Cache(p)) ==> s.dir.dirty && s.procs[p].data == s.current,
        coherence::owns(s,c,coherence::Owner::Grant(p)) ==> s.dir.dirty && s.uni[p].data == s.current,
        c.nodes.contains(p) && (s.procs[p].cache == Cache::E || s.uni[p].cmd == Uni::PutX) ==>
            !s.wb.pending && s.shwb.cmd != Shared::ShWb && s.uni[s.home].cmd != Uni::Put,
        control::forwarding(s,p) && c.nodes.contains(p) ==>
            !s.collecting && !s.nakc && s.shwb.cmd == Shared::None && s.uni[s.home].cmd != Uni::Put && s.uni[s.home].cmd != Uni::PutX
{
    assert(shared_inductive(s,c)); control::expose_node(s,c,p); coherence::expose_node(s,c,p);
    assert forall |o: coherence::Owner| #[trigger] coherence::owns(s,c,o) implies
        (coherence::owns(s,c,coherence::Owner::Cache(p)) ==> o == coherence::Owner::Cache(p))
        && (coherence::owns(s,c,coherence::Owner::Grant(p)) ==> o == coherence::Owner::Grant(p)) by {}
    assert(coherence::owns(s,c,coherence::Owner::Writeback) ==> !coherence::owns(s,c,coherence::Owner::Cache(p)) && !coherence::owns(s,c,coherence::Owner::Grant(p)));
    assert(coherence::owns(s,c,coherence::Owner::SharedWriteback) ==> !coherence::owns(s,c,coherence::Owner::Cache(p)) && !coherence::owns(s,c,coherence::Owner::Grant(p)));
    assert(coherence::owns(s,c,coherence::Owner::HomePut) ==> !coherence::owns(s,c,coherence::Owner::Cache(p)) && !coherence::owns(s,c,coherence::Owner::Grant(p)));
    assert(control::work(s,c,control::Work::Forward(p)) && control::work(s,c,control::Work::Invalidating) ==> control::Work::Forward(p) == control::Work::Invalidating);
    assert(control::work(s,c,control::Work::Forward(p)) && control::work(s,c,control::Work::Nak) ==> control::Work::Forward(p) == control::Work::Nak);
    assert(control::work(s,c,control::Work::Forward(p)) && control::work(s,c,control::Work::Shared) ==> control::Work::Forward(p) == control::Work::Shared);
    assert(control::work(s,c,control::Work::Forward(p)) && control::work(s,c,control::Work::HomeReply) ==> control::Work::Forward(p) == control::Work::HomeReply);
}
pub proof fn expose_pair(s: LState,c: Constants,p: int,q: int)
    requires inductive(s,c),c.nodes.contains(p),c.nodes.contains(q)
    ensures s.procs[p].cache == Cache::E ==> s.uni[q].cmd != Uni::PutX && (p != q ==> s.procs[q].cache != Cache::E),
        s.uni[p].cmd == Uni::PutX ==> s.procs[q].cache != Cache::E && (p != q ==> s.uni[q].cmd != Uni::PutX)
{
    assert(coherence::owns(s,c,coherence::Owner::Cache(p)) && coherence::owns(s,c,coherence::Owner::Cache(q)) ==> p == q);
    assert(coherence::owns(s,c,coherence::Owner::Cache(p)) && coherence::owns(s,c,coherence::Owner::Grant(q)) ==> false);
    assert(coherence::owns(s,c,coherence::Owner::Grant(p)) && coherence::owns(s,c,coherence::Owner::Cache(q)) ==> false);
    assert(coherence::owns(s,c,coherence::Owner::Grant(p)) && coherence::owns(s,c,coherence::Owner::Grant(q)) ==> p == q);
}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,p: int)
    requires inductive(s,c),enabled(s,c,a),c.nodes.contains(p)
    ensures requests(apply(s,c,a),p),location(apply(s,c,a),p),shared_info(apply(s,c,a),p),data_info(apply(s,c,a),p)
{
    reveal(enabled); reveal(apply);
    assert(shared_inductive(s,c)); assert(control::control(s,c));
    control::expose_work(s,c,control::Work::Nak);
    control::expose_work(s,c,control::Work::Shared);
    control::expose_work(s,c,control::Work::HomeReply);
    control::expose_work(s,c,control::Work::Invalidating);
    assert(coherence::owns(s,c,coherence::Owner::Writeback) && coherence::owns(s,c,coherence::Owner::SharedWriteback) ==> false);
    expose(s,c,s.home);
    coherence::expose_owner(s,c,coherence::Owner::Writeback); coherence::expose_owner(s,c,coherence::Owner::SharedWriteback); coherence::expose_owner(s,c,coherence::Owner::HomePut);
    let u=apply(s,c,a);
    expose(s,c,p); expose_pair(s,c,s.home,p);
    assert(control::work(s,c,control::Work::Nak) && control::work(s,c,control::Work::Nak) ==> control::Work::Nak == control::Work::Nak);
    assert(control::work(s,c,control::Work::Nak) && control::work(s,c,control::Work::Shared) ==> control::Work::Nak == control::Work::Shared);
    assert(control::work(s,c,control::Work::Nak) && control::work(s,c,control::Work::HomeReply) ==> control::Work::Nak == control::Work::HomeReply);
    assert(control::work(s,c,control::Work::Nak) && control::work(s,c,control::Work::Invalidating) ==> control::Work::Nak == control::Work::Invalidating);
    assert(control::work(s,c,control::Work::Nak) && control::work(s,c,control::Work::Forward(p)) ==> control::Work::Nak == control::Work::Forward(p));
    assert(control::work(s,c,control::Work::Shared) && control::work(s,c,control::Work::Nak) ==> control::Work::Shared == control::Work::Nak);
    assert(control::work(s,c,control::Work::Shared) && control::work(s,c,control::Work::Shared) ==> control::Work::Shared == control::Work::Shared);
    assert(control::work(s,c,control::Work::Shared) && control::work(s,c,control::Work::HomeReply) ==> control::Work::Shared == control::Work::HomeReply);
    assert(control::work(s,c,control::Work::Shared) && control::work(s,c,control::Work::Invalidating) ==> control::Work::Shared == control::Work::Invalidating);
    assert(control::work(s,c,control::Work::Shared) && control::work(s,c,control::Work::Forward(p)) ==> control::Work::Shared == control::Work::Forward(p));
    assert(control::work(s,c,control::Work::HomeReply) && control::work(s,c,control::Work::Nak) ==> control::Work::HomeReply == control::Work::Nak);
    assert(control::work(s,c,control::Work::HomeReply) && control::work(s,c,control::Work::Shared) ==> control::Work::HomeReply == control::Work::Shared);
    assert(control::work(s,c,control::Work::HomeReply) && control::work(s,c,control::Work::HomeReply) ==> control::Work::HomeReply == control::Work::HomeReply);
    assert(control::work(s,c,control::Work::HomeReply) && control::work(s,c,control::Work::Invalidating) ==> control::Work::HomeReply == control::Work::Invalidating);
    assert(control::work(s,c,control::Work::HomeReply) && control::work(s,c,control::Work::Forward(p)) ==> control::Work::HomeReply == control::Work::Forward(p));
    assert(control::work(s,c,control::Work::Invalidating) && control::work(s,c,control::Work::Nak) ==> control::Work::Invalidating == control::Work::Nak);
    assert(control::work(s,c,control::Work::Invalidating) && control::work(s,c,control::Work::Shared) ==> control::Work::Invalidating == control::Work::Shared);
    assert(control::work(s,c,control::Work::Invalidating) && control::work(s,c,control::Work::HomeReply) ==> control::Work::Invalidating == control::Work::HomeReply);
    assert(control::work(s,c,control::Work::Invalidating) && control::work(s,c,control::Work::Invalidating) ==> control::Work::Invalidating == control::Work::Invalidating);
    assert(control::work(s,c,control::Work::Invalidating) && control::work(s,c,control::Work::Forward(p)) ==> control::Work::Invalidating == control::Work::Forward(p));
    match a {
        Action::Store { src,data } => { expose(s,c,src); expose_pair(s,c,src,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::RemoteRequest { src,exclusive } => { expose(s,c,src); expose_pair(s,c,src,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::LocalForward { exclusive } => { assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::LocalGet => { assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::LocalGetX => { assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::RemoteWriteback { dst } => { expose(s,c,dst); expose_pair(s,c,dst,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::LocalWriteback => { assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::RemoteReplace { src } => { expose(s,c,src); expose_pair(s,c,src,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::LocalReplace => { assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::ReceiveNak { dst } => { expose(s,c,dst); expose_pair(s,c,dst,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::ClearNak => { assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::LocalNak { src,exclusive } => { expose(s,c,src); expose_pair(s,c,src,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::LocalRelay { src,exclusive } => { expose(s,c,src); expose_pair(s,c,src,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::LocalGrant { src,exclusive } => { expose(s,c,src); expose_pair(s,c,src,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::RemoteNak { src,dst } => { expose(s,c,src); expose_pair(s,c,src,p); expose(s,c,dst); expose_pair(s,c,dst,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::RemoteGrant { src,dst,exclusive } => { expose(s,c,src); expose_pair(s,c,src,p); expose(s,c,dst); expose_pair(s,c,dst,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::ReceivePut { dst } => { expose(s,c,dst); expose_pair(s,c,dst,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::ReceivePutX { dst } => { expose(s,c,dst); expose_pair(s,c,dst,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::Invalidate { dst } => { expose(s,c,dst); expose_pair(s,c,dst,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::InvalidateAck { src } => { expose(s,c,src); expose_pair(s,c,src,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::ReceiveWriteback => { assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::ReceiveForwardAck => { assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::ReceiveSharedWriteback => { assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::ReceiveReplace { src } => { expose(s,c,src); expose_pair(s,c,src,p); assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
        Action::Stutter => { assert(requests(u,p)); assert(location(u,p)); assert(shared_info(u,p)); assert(data_info(u,p)); },
    }

}
pub proof fn preserve_directory(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures directory(apply(s,c,a),c)
{
    reveal(enabled); reveal(apply);
    assert(shared_inductive(s,c)); assert(control::control(s,c));
    control::expose_work(s,c,control::Work::Nak);
    control::expose_work(s,c,control::Work::Shared);
    control::expose_work(s,c,control::Work::HomeReply);
    control::expose_work(s,c,control::Work::Invalidating);
    assert(coherence::owns(s,c,coherence::Owner::Writeback) && coherence::owns(s,c,coherence::Owner::SharedWriteback) ==> false);
    expose(s,c,s.home);
    coherence::expose_owner(s,c,coherence::Owner::Writeback); coherence::expose_owner(s,c,coherence::Owner::SharedWriteback); coherence::expose_owner(s,c,coherence::Owner::HomePut);
    let u=apply(s,c,a);
    assert(control::work(s,c,control::Work::Nak) && control::work(s,c,control::Work::Nak) ==> control::Work::Nak == control::Work::Nak);
    assert(control::work(s,c,control::Work::Nak) && control::work(s,c,control::Work::Shared) ==> control::Work::Nak == control::Work::Shared);
    assert(control::work(s,c,control::Work::Nak) && control::work(s,c,control::Work::HomeReply) ==> control::Work::Nak == control::Work::HomeReply);
    assert(control::work(s,c,control::Work::Nak) && control::work(s,c,control::Work::Invalidating) ==> control::Work::Nak == control::Work::Invalidating);
    assert(control::work(s,c,control::Work::Shared) && control::work(s,c,control::Work::Nak) ==> control::Work::Shared == control::Work::Nak);
    assert(control::work(s,c,control::Work::Shared) && control::work(s,c,control::Work::Shared) ==> control::Work::Shared == control::Work::Shared);
    assert(control::work(s,c,control::Work::Shared) && control::work(s,c,control::Work::HomeReply) ==> control::Work::Shared == control::Work::HomeReply);
    assert(control::work(s,c,control::Work::Shared) && control::work(s,c,control::Work::Invalidating) ==> control::Work::Shared == control::Work::Invalidating);
    assert(control::work(s,c,control::Work::HomeReply) && control::work(s,c,control::Work::Nak) ==> control::Work::HomeReply == control::Work::Nak);
    assert(control::work(s,c,control::Work::HomeReply) && control::work(s,c,control::Work::Shared) ==> control::Work::HomeReply == control::Work::Shared);
    assert(control::work(s,c,control::Work::HomeReply) && control::work(s,c,control::Work::HomeReply) ==> control::Work::HomeReply == control::Work::HomeReply);
    assert(control::work(s,c,control::Work::HomeReply) && control::work(s,c,control::Work::Invalidating) ==> control::Work::HomeReply == control::Work::Invalidating);
    assert(control::work(s,c,control::Work::Invalidating) && control::work(s,c,control::Work::Nak) ==> control::Work::Invalidating == control::Work::Nak);
    assert(control::work(s,c,control::Work::Invalidating) && control::work(s,c,control::Work::Shared) ==> control::Work::Invalidating == control::Work::Shared);
    assert(control::work(s,c,control::Work::Invalidating) && control::work(s,c,control::Work::HomeReply) ==> control::Work::Invalidating == control::Work::HomeReply);
    assert(control::work(s,c,control::Work::Invalidating) && control::work(s,c,control::Work::Invalidating) ==> control::Work::Invalidating == control::Work::Invalidating);
    match a {
        Action::Store { src,data } => { expose(s,c,src); assert(directory(u,c)); },
        Action::RemoteRequest { src,exclusive } => { expose(s,c,src); assert(directory(u,c)); },
        Action::LocalForward { exclusive } => { assert(directory(u,c)); },
        Action::LocalGet => { assert(directory(u,c)); },
        Action::LocalGetX => { assert(directory(u,c)); },
        Action::RemoteWriteback { dst } => { expose(s,c,dst); assert(directory(u,c)); },
        Action::LocalWriteback => { assert(directory(u,c)); },
        Action::RemoteReplace { src } => { expose(s,c,src); assert(directory(u,c)); },
        Action::LocalReplace => { assert(directory(u,c)); },
        Action::ReceiveNak { dst } => { expose(s,c,dst); assert(directory(u,c)); },
        Action::ClearNak => { assert(directory(u,c)); },
        Action::LocalNak { src,exclusive } => { expose(s,c,src); assert(directory(u,c)); },
        Action::LocalRelay { src,exclusive } => { expose(s,c,src); assert(directory(u,c)); },
        Action::LocalGrant { src,exclusive } => { expose(s,c,src); assert(directory(u,c)); },
        Action::RemoteNak { src,dst } => { expose(s,c,src); expose(s,c,dst); assert(directory(u,c)); },
        Action::RemoteGrant { src,dst,exclusive } => { expose(s,c,src); expose(s,c,dst); assert(directory(u,c)); },
        Action::ReceivePut { dst } => { expose(s,c,dst); assert(directory(u,c)); },
        Action::ReceivePutX { dst } => { expose(s,c,dst); assert(directory(u,c)); },
        Action::Invalidate { dst } => { expose(s,c,dst); assert(directory(u,c)); },
        Action::InvalidateAck { src } => { expose(s,c,src); assert(directory(u,c)); },
        Action::ReceiveWriteback => { assert(directory(u,c)); },
        Action::ReceiveForwardAck => { assert(directory(u,c)); },
        Action::ReceiveSharedWriteback => { assert(directory(u,c)); },
        Action::ReceiveReplace { src } => { expose(s,c,src); assert(directory(u,c)); },
        Action::Stutter => { assert(directory(u,c)); },
    }

}
pub proof fn preserve_inductive(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    control::preserve_inductive(s,c,a); preserve_directory(s,c,a); let u=apply(s,c,a);
    assert forall |p: int| c.nodes.contains(p) implies #[trigger] requests(u,p) by { preserve_node(s,c,a,p); }
    assert forall |p: int| c.nodes.contains(p) implies #[trigger] location(u,p) by { preserve_node(s,c,a,p); }
    assert forall |p: int| c.nodes.contains(p) implies #[trigger] shared_info(u,p) by { preserve_node(s,c,a,p); }
    assert forall |p: int| c.nodes.contains(p) implies #[trigger] data_info(u,p) by { preserve_node(s,c,a,p); }
    assert(shared_inductive(u,c));
}
pub proof fn cache_data_from_inductive(s: LState,c: Constants)
    requires inductive(s,c)
    ensures cache_data(s,c)
{
    assert forall |p: int| c.nodes.contains(p) implies
        (s.procs[p].cache == Cache::E ==> s.procs[p].data == s.current)
        && (s.procs[p].cache == Cache::S ==> s.procs[p].data == if s.collecting { s.previous } else { s.current }) by { expose(s,c,p); }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires super::flash_liveness::safety_spec(b,c),k >= 0
    ensures inductive(b[k],c),cache_data(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c,b[0].home,b[0].current); }
    else {
        safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve_inductive(b[i],c,a);
    }
    cache_data_from_inductive(b[k],c);
}
pub proof fn cache_data_correct(b: Behavior<LState>,c: Constants)
    requires super::flash_liveness::safety_spec(b,c)
    ensures forall |k: int| k >= 0 ==> #[trigger] cache_data(b[k],c)
{
    assert forall |k: int| k >= 0 implies #[trigger] cache_data(b[k],c) by { safety_at(b,c,k); }
}
} // verus!
