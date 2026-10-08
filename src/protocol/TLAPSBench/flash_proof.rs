use vstd::prelude::*;
use super::flash::*;
use super::temporal::Behavior;
verus! {
pub open spec fn proc_typed(p: Proc, c: Constants) -> bool {
    data_u(c, p.data) && (p.cache != Cache::I ==> c.data.contains(p.data))
}
pub open spec fn uni_typed(m: UniMsg, c: Constants) -> bool {
    node_u(c, m.node) && data_u(c, m.data)
    && (m.cmd == Uni::Put || m.cmd == Uni::PutX ==> c.data.contains(m.data))
}
pub open spec fn typed(s: LState, c: Constants) -> bool {
    type_ok(s, c)
    && (forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) ==> proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c))
    && (s.wb.pending ==> c.data.contains(s.wb.data))
    && (s.shwb.cmd == Shared::ShWb ==> c.data.contains(s.shwb.data) && c.nodes.contains(s.shwb.node))
}
pub proof fn initial_typed(c: Constants, home: int, data: int)
    requires c.nodes.contains(home), c.data.contains(data)
    ensures typed(initial(c, home, data), c)
{}
pub proof fn preserve_typed(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a)
    ensures typed(apply(s, c, a), c)
{
    // Each Action variant is proved by its own helper lemma below, so
    // `apply` unfolds for one variant per query.
    match a {
        Action::Store { .. } => preserve_typed_store(s,c,a),
        Action::RemoteRequest { .. } => preserve_typed_remote_request(s,c,a),
        Action::LocalForward { .. } => preserve_typed_local_forward(s,c,a),
        Action::LocalGet => preserve_typed_local_get(s,c,a),
        Action::LocalGetX => preserve_typed_local_get_x(s,c,a),
        Action::RemoteWriteback { .. } => preserve_typed_remote_writeback(s,c,a),
        Action::LocalWriteback => preserve_typed_local_writeback(s,c,a),
        Action::RemoteReplace { .. } => preserve_typed_remote_replace(s,c,a),
        Action::LocalReplace => preserve_typed_local_replace(s,c,a),
        Action::ReceiveNak { .. } => preserve_typed_receive_nak(s,c,a),
        Action::ClearNak => preserve_typed_clear_nak(s,c,a),
        Action::LocalNak { .. } => preserve_typed_local_nak(s,c,a),
        Action::LocalRelay { .. } => preserve_typed_local_relay(s,c,a),
        Action::LocalGrant { .. } => preserve_typed_local_grant(s,c,a),
        Action::RemoteNak { .. } => preserve_typed_remote_nak(s,c,a),
        Action::RemoteGrant { .. } => preserve_typed_remote_grant(s,c,a),
        Action::ReceivePut { .. } => preserve_typed_receive_put(s,c,a),
        Action::ReceivePutX { .. } => preserve_typed_receive_put_x(s,c,a),
        Action::Invalidate { .. } => preserve_typed_invalidate(s,c,a),
        Action::InvalidateAck { .. } => preserve_typed_invalidate_ack(s,c,a),
        Action::ReceiveWriteback => preserve_typed_receive_writeback(s,c,a),
        Action::ReceiveForwardAck => preserve_typed_receive_forward_ack(s,c,a),
        Action::ReceiveSharedWriteback => preserve_typed_receive_shared_writeback(s,c,a),
        Action::ReceiveReplace { .. } => preserve_typed_receive_replace(s,c,a),
        Action::Stutter => preserve_typed_stutter(s,c,a),
    }
}
#[verifier::spinoff_prover]
proof fn preserve_typed_store(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is Store
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_remote_request(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is RemoteRequest
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_local_forward(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is LocalForward
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_local_get(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is LocalGet
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_local_get_x(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is LocalGetX
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_remote_writeback(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is RemoteWriteback
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_local_writeback(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is LocalWriteback
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_remote_replace(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is RemoteReplace
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_local_replace(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is LocalReplace
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_receive_nak(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is ReceiveNak
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_clear_nak(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is ClearNak
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_local_nak(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is LocalNak
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_local_relay(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is LocalRelay
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_local_grant(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is LocalGrant
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_remote_nak(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is RemoteNak
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_remote_grant(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is RemoteGrant
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_receive_put(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is ReceivePut
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_receive_put_x(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is ReceivePutX
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_invalidate(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is Invalidate
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_invalidate_ack(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is InvalidateAck
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_receive_writeback(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is ReceiveWriteback
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_receive_forward_ack(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is ReceiveForwardAck
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_receive_shared_writeback(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is ReceiveSharedWriteback
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_receive_replace(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is ReceiveReplace
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
#[verifier::spinoff_prover]
proof fn preserve_typed_stutter(s: LState, c: Constants, a: Action)
    requires typed(s, c), enabled(s, c, a),
        a is Stutter
    ensures typed(apply(s, c, a), c)
{
    reveal(enabled);
    reveal(apply);
    let u = apply(s, c, a);
    assert forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) implies proc_typed(u.procs[p], c) && uni_typed(u.uni[p], c) by {
        assert(proc_typed(s.procs[p], c) && uni_typed(s.uni[p], c));
    }
    assert(u.procs.dom() =~= c.nodes);
    assert(u.uni.dom() =~= c.nodes);
    assert(u.inv.dom() =~= c.nodes);
    assert(u.replace.dom() =~= c.nodes);
    assert(u.dir.sharers.subset_of(c.nodes));
    assert(u.dir.invalidating.subset_of(c.nodes));
    assert(type_ok(u, c));
}
pub open spec fn behavior(b: Seq<LState>, c: Constants) -> bool {
    valid_constants(c) && b.len() > 0
    && c.nodes.contains(b[0].home) && c.data.contains(b[0].current)
    && b[0] == initial(c, b[0].home, b[0].current)
    && forall |i: int| 0 <= i < b.len()-1 ==> #[trigger] next(b[i], b[i+1], c)
}
pub proof fn type_correct(b: Seq<LState>, c: Constants, k: int)
    requires behavior(b, c), 0 <= k < b.len()
    ensures typed(b[k], c), type_ok(b[k], c)
    decreases k
{
    if k == 0 { initial_typed(c, b[0].home, b[0].current); }
    else {
        type_correct(b, c, k-1);
        let i = k-1;
        assert(next(b[i], b[i+1], c));
        reveal(next);
        let a = choose |a: Action| #[trigger] enabled(b[i], c, a) && b[i+1] == apply(b[i], c, a);
        preserve_typed(b[i], c, a);
    }
}
pub proof fn type_at(b: Behavior<LState>, c: Constants, k: int)
    requires super::flash_liveness::safety_spec(b, c), k >= 0
    ensures typed(b[k], c), type_ok(b[k], c)
    decreases k
{
    if k == 0 { initial_typed(c, b[0].home, b[0].current); }
    else {
        type_at(b, c, k-1);
        let i = k-1;
        assert(next(b[i], b[i+1], c));
        reveal(next);
        let a = choose |a: Action| #[trigger] enabled(b[i], c, a) && b[i+1] == apply(b[i], c, a);
        preserve_typed(b[i], c, a);
    }
}
pub proof fn type_correct_always(b: Behavior<LState>, c: Constants)
    requires super::flash_liveness::safety_spec(b, c)
    ensures forall |k: int| k >= 0 ==> #[trigger] type_ok(b[k], c)
{
    assert forall |k: int| k >= 0 implies #[trigger] type_ok(b[k], c) by { type_at(b, c, k); }
}
} // verus!
