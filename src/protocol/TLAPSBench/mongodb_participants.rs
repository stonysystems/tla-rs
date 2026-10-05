//! Router participants grow while requests are issued and freeze when commit starts.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_router_time as time;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures };
pub open spec fn selected(s: LState,c: Constants,t: int) -> bool { exists |r: int| #[trigger] time::selected(s,c,r,t) }
pub open spec fn owner(s: LState,c: Constants,t: int) -> int { choose |r: int| #[trigger] time::selected(s,c,r,t) }
pub open spec fn txn(s: LState,c: Constants,t: int) -> RTransaction { s.routers[owner(s,c,t)][t] }
pub open spec fn shards(s: LState,c: Constants,t: int) -> Seq<int> { participant_shards(txn(s,c,t).participants) }
pub open spec fn issued(q: Seq<Participant>,i: int,kind: Kind) -> bool {
    exists |p: int| 0 <= p < q.len() && (#[trigger] q[p]).shard == i && q[p].kinds.contains(kind)
}
pub open spec fn well_formed(q: Seq<Participant>,c: Constants) -> bool {
    participant_shards(q).no_duplicates()
    && forall |p: int| 0 <= p < q.len() ==> c.shards.contains((#[trigger] q[p]).shard) && !q[p].kinds.is_empty()
}
pub open spec fn router(s: LState,c: Constants,r: int,t: int) -> bool {
    let x=s.routers[r][t]; well_formed(x.participants,c) && (x.count == 0 <==> x.participants.len() == 0)
    && (x.committing ==> x.participants.len() > 0)
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |r: int,t: int| c.routers.contains(r) && c.txns.contains(t) ==> #[trigger] router(s,c,r,t)
}
pub proof fn owner_is(s: LState,c: Constants,r: int,t: int)
    requires time::safe(s,c),time::selected(s,c,r,t)
    ensures selected(s,c,t),owner(s,c,t) == r,txn(s,c,t) == s.routers[r][t]
{
    assert(selected(s,c,t)); assert(time::selected(s,c,owner(s,c,t),t)); assert(time::unique(s,c,t));
}
pub proof fn owner_fixed(s: LState,c: Constants,a: Action,t: int)
    requires support::shape(s,c),time::safe(s,c),enabled(s,c,a),selected(s,c,t)
    ensures selected(apply(s,c,a),c,t),owner(apply(s,c,a),c,t) == owner(s,c,t)
{
    let r=owner(s,c,t); assert(time::selected(s,c,r,t)); time::selected_retained(s,c,a,r,t);
    time::preserve(s,c,a); owner_is(apply(s,c,a),c,r,t);
}
pub proof fn update(q: Seq<Participant>,c: Constants,i: int,kind: Kind)
    requires well_formed(q,c),c.shards.contains(i)
    ensures well_formed(update_participants(q,i,kind),c),update_participants(q,i,kind).len() > 0,
        issued(update_participants(q,i,kind),i,kind),
        forall |j: int,k: Kind| #[trigger] issued(q,j,k) ==> issued(update_participants(q,i,kind),j,k)
{
    let u=update_participants(q,i,kind); let old=participant_shards(q); let new=participant_shards(u);
    if old.contains(i) {
        assert(new =~= old);
        let p=choose |p: int| 0 <= p < old.len() && old[p] == i;
        assert(q[p].shard == i); assert(u[p].kinds.contains(kind));
    } else {
        assert(new =~= old.push(i)); assert(new.no_duplicates());
        assert(u[q.len() as int].shard == i); assert(u[q.len() as int].kinds.contains(kind));
    }
    assert forall |p: int| 0 <= p < u.len() implies c.shards.contains((#[trigger] u[p]).shard) && !u[p].kinds.is_empty() by {
        if p < q.len() { assert(c.shards.contains(q[p].shard)); assert(!q[p].kinds.is_empty()); }
    }
    assert forall |j: int,k: Kind| #[trigger] issued(q,j,k) implies issued(u,j,k) by {
        let p=choose |p: int| 0 <= p < q.len() && (#[trigger] q[p]).shard == j && q[p].kinds.contains(k);
        assert(u[p].shard == j); assert(u[p].kinds.contains(k));
    }
}
pub proof fn initial_safe(c: Constants,catalog: IMap<int,int>)
    ensures safe(initial(c,catalog),c)
{
    let s=initial(c,catalog);
    assert forall |r: int,t: int| c.routers.contains(r) && c.txns.contains(t) implies #[trigger] router(s,c,r,t) by {
        assert(participant_shards(s.routers[r][t].participants) =~= Seq::<int>::empty());
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    reveal(enabled); reveal(apply); let u=apply(s,c,a);
    assert forall |r: int,t: int| c.routers.contains(r) && c.txns.contains(t) implies #[trigger] router(u,c,r,t) by {
        assert(router(s,c,r,t));
        if let Action::RouterOp { r: ar,i,t: at,k,op }=a { if r == ar && t == at { update(s.routers[r][t].participants,c,i,op); } }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures safe(b[time],c)
    decreases time
{
    if time == 0 { initial_safe(c,b[0].catalog); }
    else { at(b,c,time-1); support::at(b,c,time-1); let a=support::step(b,c,time-1); preserve(b[time-1],c,a); }
}
pub proof fn issued_retained(s: LState,c: Constants,a: Action,t: int,i: int,kind: Kind)
    requires support::shape(s,c),time::safe(s,c),safe(s,c),enabled(s,c,a),selected(s,c,t),issued(txn(s,c,t).participants,i,kind)
    ensures selected(apply(s,c,a),c,t),issued(txn(apply(s,c,a),c,t).participants,i,kind)
{
    owner_fixed(s,c,a,t); reveal(enabled); reveal(apply); let r=owner(s,c,t); assert(router(s,c,r,t));
    if let Action::RouterOp { r: ar,i: ai,t: at,k,op }=a { if ar == r && at == t { update(s.routers[r][t].participants,c,ai,op); } }
}
pub proof fn frozen(s: LState,c: Constants,a: Action,t: int)
    requires support::shape(s,c),time::safe(s,c),enabled(s,c,a),selected(s,c,t),txn(s,c,t).committing
    ensures selected(apply(s,c,a),c,t),txn(apply(s,c,a),c,t) == txn(s,c,t)
{
    owner_fixed(s,c,a,t); let r=owner(s,c,t); assert(time::selected(s,c,r,t)); reveal(enabled); reveal(apply);
    if let Action::RouterStart { r: ar,t: at,ts }=a { if at == t { assert(s.routers[r][t].read_ts == c.no_value); assert(false); } }
}
} // verus!
