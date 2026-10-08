//! Ownership moves between an exclusive cache and messages in flight.
//! Tracking every location, rather than caches alone, closes the exclusion
//! induction and relates writeback data to the latest store.
use vstd::prelude::*;
use super::flash::*;
use super::flash_proof::{typed,initial_typed,preserve_typed};
use super::temporal::Behavior;
verus! {
pub enum Owner { Cache(int),Grant(int),Writeback,SharedWriteback,HomePut }
pub open spec fn owns(s: LState,c: Constants,o: Owner) -> bool {
    match o {
        Owner::Cache(p) => c.nodes.contains(p) && s.procs[p].cache == Cache::E,
        Owner::Grant(p) => c.nodes.contains(p) && s.uni[p].cmd == Uni::PutX,
        Owner::Writeback => s.wb.pending,
        Owner::SharedWriteback => s.shwb.cmd == Shared::ShWb,
        Owner::HomePut => s.uni[s.home].cmd == Uni::Put,
    }
}
pub open spec fn owner_data(s: LState,o: Owner) -> int {
    match o {
        Owner::Cache(p) => s.procs[p].data,Owner::Grant(p) => s.uni[p].data,
        Owner::Writeback => s.wb.data,Owner::SharedWriteback => s.shwb.data,
        Owner::HomePut => s.uni[s.home].data,
    }
}
pub open spec fn ownership(s: LState,c: Constants) -> bool {
    (forall |o: Owner| #[trigger] owns(s,c,o) ==> s.dir.dirty)
    && forall |o: Owner,p: Owner| #[trigger] owns(s,c,o) && #[trigger] owns(s,c,p) ==> o == p
}
pub open spec fn ownership_data(s: LState,c: Constants) -> bool {
    forall |o: Owner| #[trigger] owns(s,c,o) ==> owner_data(s,o) == s.current
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    typed(s,c) && ownership(s,c) && ownership_data(s,c) && mem_data(s)
}
pub proof fn initial_inductive(c: Constants,home: int,data: int)
    requires c.nodes.contains(home),c.data.contains(data)
    ensures inductive(initial(c,home,data),c)
{
    initial_typed(c,home,data);
}
pub proof fn expose_owner(s: LState,c: Constants,o: Owner)
    requires ownership(s,c)
    ensures owns(s,c,o) ==> s.dir.dirty,
        ownership_data(s,c) && owns(s,c,o) ==> owner_data(s,o) == s.current,
        forall |p: Owner| owns(s,c,o) && #[trigger] owns(s,c,p) ==> o == p
{}
pub proof fn expose_node(s: LState,c: Constants,i: int)
    requires ownership(s,c)
    ensures owns(s,c,Owner::Cache(i)) ==> s.dir.dirty,
        owns(s,c,Owner::Grant(i)) ==> s.dir.dirty,
        ownership_data(s,c) && owns(s,c,Owner::Cache(i)) ==> s.procs[i].data == s.current,
        ownership_data(s,c) && owns(s,c,Owner::Grant(i)) ==> s.uni[i].data == s.current,
        forall |p: Owner| owns(s,c,Owner::Cache(i)) && #[trigger] owns(s,c,p) ==> Owner::Cache(i) == p,
        forall |p: Owner| owns(s,c,Owner::Grant(i)) && #[trigger] owns(s,c,p) ==> Owner::Grant(i) == p
{ expose_owner(s,c,Owner::Cache(i)); expose_owner(s,c,Owner::Grant(i)); }
pub proof fn preserve_ownership(s: LState,c: Constants,a: Action,o: Owner,p: Owner)
    requires typed(s,c),ownership(s,c),enabled(s,c,a)
    ensures owns(apply(s,c,a),c,o) ==> apply(s,c,a).dir.dirty,
        owns(apply(s,c,a),c,o) && owns(apply(s,c,a),c,p) ==> o == p
{
    reveal(enabled); reveal(apply);
    expose_owner(s,c,o); expose_owner(s,c,p);
    expose_owner(s,c,Owner::Writeback); expose_owner(s,c,Owner::SharedWriteback); expose_owner(s,c,Owner::HomePut);
    expose_node(s,c,s.home);
    assert(owns(s,c,o) && owns(s,c,p) ==> o == p);
    assert(owns(s,c,Owner::Cache(s.home)) && owns(s,c,o) ==> Owner::Cache(s.home) == o);
    assert(owns(s,c,Owner::Cache(s.home)) && owns(s,c,p) ==> Owner::Cache(s.home) == p);
    assert(owns(s,c,Owner::HomePut) && owns(s,c,o) ==> Owner::HomePut == o);
    assert(owns(s,c,Owner::SharedWriteback) && owns(s,c,o) ==> Owner::SharedWriteback == o);
    let u=apply(s,c,a);
    match a {
        Action::Store { src,data } => { expose_node(s,c,src); assert(owns(u,c,o) == owns(s,c,o)); assert(owns(u,c,p) == owns(s,c,p)); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::RemoteRequest { src,exclusive } => { expose_node(s,c,src); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::LocalForward { exclusive } => { assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::LocalGet => { assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::LocalGetX => { assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::RemoteWriteback { dst } => { assert(owns(s,c,Owner::Cache(dst))); assert(owns(s,c,o) ==> o == Owner::Cache(dst)); assert(owns(s,c,p) ==> p == Owner::Cache(dst)); expose_node(s,c,dst); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::LocalWriteback => { assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::RemoteReplace { src } => { expose_node(s,c,src); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::LocalReplace => { assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::ReceiveNak { dst } => { expose_node(s,c,dst); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::ClearNak => { assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::LocalNak { src,exclusive } => { expose_node(s,c,src); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::LocalRelay { src,exclusive } => { expose_node(s,c,src); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::LocalGrant { src,exclusive } => { expose_node(s,c,src); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::RemoteNak { src,dst } => { expose_node(s,c,src); expose_node(s,c,dst); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::RemoteGrant { src,dst,exclusive } => { assert(owns(s,c,Owner::Cache(dst))); assert(owns(s,c,o) ==> o == Owner::Cache(dst)); assert(owns(s,c,p) ==> p == Owner::Cache(dst)); expose_node(s,c,src); expose_node(s,c,dst); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::ReceivePut { dst } => { expose_node(s,c,dst); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::ReceivePutX { dst } => { assert(owns(s,c,Owner::Grant(dst))); assert(owns(s,c,o) ==> o == Owner::Grant(dst)); assert(owns(s,c,p) ==> p == Owner::Grant(dst)); expose_node(s,c,dst); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::Invalidate { dst } => { expose_node(s,c,dst); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::InvalidateAck { src } => { expose_node(s,c,src); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::ReceiveWriteback => { assert(owns(s,c,Owner::Writeback)); assert(owns(s,c,o) ==> o == Owner::Writeback); assert(owns(s,c,p) ==> p == Owner::Writeback); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::ReceiveForwardAck => { assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::ReceiveSharedWriteback => { assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::ReceiveReplace { src } => { expose_node(s,c,src); assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
        Action::Stutter => { assert(owns(u,c,o) ==> u.dir.dirty); assert(owns(u,c,o) && owns(u,c,p) ==> o == p); },
    }
}
#[verifier::spinoff_prover]
pub proof fn preserve_owner_data(s: LState,c: Constants,a: Action,o: Owner)
    requires inductive(s,c),enabled(s,c,a)
    ensures owns(apply(s,c,a),c,o) ==> owner_data(apply(s,c,a),o) == apply(s,c,a).current
{
    reveal(enabled); reveal(apply);
    expose_owner(s,c,o);
    expose_owner(s,c,Owner::Writeback); expose_owner(s,c,Owner::SharedWriteback); expose_owner(s,c,Owner::HomePut);
    expose_node(s,c,s.home);
    let u=apply(s,c,a);
    match a {
        Action::Store { src,data } => { expose_node(s,c,src); assert(owns(s,c,Owner::Cache(src))); assert(owns(s,c,o) ==> o == Owner::Cache(src)); assert(owns(u,c,o) == owns(s,c,o)); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::RemoteRequest { src,exclusive } => { expose_node(s,c,src); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::LocalForward { exclusive } => { assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::LocalGet => { assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::LocalGetX => { assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::RemoteWriteback { dst } => { expose_node(s,c,dst); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::LocalWriteback => { assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::RemoteReplace { src } => { expose_node(s,c,src); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::LocalReplace => { assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::ReceiveNak { dst } => { expose_node(s,c,dst); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::ClearNak => { assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::LocalNak { src,exclusive } => { expose_node(s,c,src); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::LocalRelay { src,exclusive } => { expose_node(s,c,src); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::LocalGrant { src,exclusive } => { expose_node(s,c,src); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::RemoteNak { src,dst } => { expose_node(s,c,src); expose_node(s,c,dst); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::RemoteGrant { src,dst,exclusive } => { expose_node(s,c,src); expose_node(s,c,dst); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::ReceivePut { dst } => { expose_node(s,c,dst); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::ReceivePutX { dst } => { expose_node(s,c,dst); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::Invalidate { dst } => { expose_node(s,c,dst); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::InvalidateAck { src } => { expose_node(s,c,src); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::ReceiveWriteback => { assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::ReceiveForwardAck => { assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::ReceiveSharedWriteback => { assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::ReceiveReplace { src } => { expose_node(s,c,src); assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
        Action::Stutter => { assert(owns(u,c,o) ==> owner_data(u,o) == u.current); },
    }
}
pub proof fn preserve_mem(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures mem_data(apply(s,c,a))
{
    reveal(enabled); reveal(apply);
    expose_owner(s,c,Owner::Writeback); expose_owner(s,c,Owner::SharedWriteback); expose_owner(s,c,Owner::HomePut);
    expose_node(s,c,s.home);
    match a {
        Action::Store { src,.. } | Action::RemoteRequest { src,.. } | Action::RemoteReplace { src }
        | Action::LocalNak { src,.. } | Action::LocalRelay { src,.. } | Action::LocalGrant { src,.. }
        | Action::InvalidateAck { src } | Action::ReceiveReplace { src } => { expose_node(s,c,src); },
        Action::RemoteWriteback { dst } | Action::ReceiveNak { dst } | Action::ReceivePut { dst }
        | Action::ReceivePutX { dst } | Action::Invalidate { dst } => { expose_node(s,c,dst); },
        Action::RemoteNak { src,dst } | Action::RemoteGrant { src,dst,.. } => { expose_node(s,c,src); expose_node(s,c,dst); },
        _ => {},
    }

}
pub proof fn preserve_inductive(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    preserve_typed(s,c,a); preserve_mem(s,c,a);
    let u=apply(s,c,a);
    assert forall |o: Owner| #[trigger] owns(u,c,o) implies u.dir.dirty by { preserve_ownership(s,c,a,o,o); }
    assert forall |o: Owner,p: Owner| #[trigger] owns(u,c,o) && #[trigger] owns(u,c,p) implies o == p by { preserve_ownership(s,c,a,o,p); }
    assert forall |o: Owner| #[trigger] owns(u,c,o) implies owner_data(u,o) == u.current by { preserve_owner_data(s,c,a,o); }
}
pub proof fn exclusion_from_inductive(s: LState,c: Constants)
    requires inductive(s,c)
    ensures lemma_1(s,c)
{
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) && s.procs[p].cache == Cache::E implies
        s.dir.dirty && !s.wb.pending && s.shwb.cmd != Shared::ShWb && s.uni[s.home].cmd != Uni::Put
        && (forall |q: int| #![trigger c.nodes.contains(q)] c.nodes.contains(q) ==> (q != p ==> s.procs[q].cache != Cache::E) && s.uni[q].cmd != Uni::PutX) by {
        assert(owns(s,c,Owner::Cache(p)));
        assert(owns(s,c,Owner::Writeback) ==> Owner::Cache(p) == Owner::Writeback);
        assert(owns(s,c,Owner::SharedWriteback) ==> Owner::Cache(p) == Owner::SharedWriteback);
        assert(owns(s,c,Owner::HomePut) ==> Owner::Cache(p) == Owner::HomePut);
        assert forall |q: int| #![trigger c.nodes.contains(q)] c.nodes.contains(q) implies (q != p ==> s.procs[q].cache != Cache::E) && s.uni[q].cmd != Uni::PutX by {
            assert(owns(s,c,Owner::Cache(q)) ==> Owner::Cache(p) == Owner::Cache(q));
            assert(owns(s,c,Owner::Grant(q)) ==> Owner::Cache(p) == Owner::Grant(q));
        }
    }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires super::flash_liveness::safety_spec(b,c),k >= 0
    ensures inductive(b[k],c),lemma_1(b[k],c),mem_data(b[k])
    decreases k
{
    if k == 0 { initial_inductive(c,b[0].home,b[0].current); }
    else {
        safety_at(b,c,k-1); let i=k-1;
        assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve_inductive(b[i],c,a);
    }
    exclusion_from_inductive(b[k],c);
}
pub proof fn benchmark_coherence(b: Behavior<LState>,c: Constants)
    requires super::flash_liveness::safety_spec(b,c)
    ensures forall |k: int| k >= 0 ==> #[trigger] lemma_1(b[k],c),
        forall |k: int| k >= 0 ==> #[trigger] mem_data(b[k])
{
    assert forall |k: int| k >= 0 implies #[trigger] lemma_1(b[k],c) by { safety_at(b,c,k); }
    assert forall |k: int| k >= 0 implies #[trigger] mem_data(b[k]) by { safety_at(b,c,k); }
}
} // verus!
