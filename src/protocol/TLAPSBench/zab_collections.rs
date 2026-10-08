//! Finite receipt selection and history helpers used by Zab's proof.
use vstd::prelude::*;
use super::zab::*;
verus! {
pub proof fn maximum_correct(q: Set<int>)
    ensures q.is_empty() ==> maximum(q) == -1,
        !q.is_empty() ==> q.contains(maximum(q)) && (forall |x: int| q.contains(x) ==> x <= maximum(q))
    decreases q.len()
{
    reveal(maximum);
    if !q.is_empty() {
        let x=choose |x: int| q.contains(x); let rest=q.remove(x);
        maximum_correct(rest);
        let m=if rest.is_empty() || x >= maximum(rest) { x } else { maximum(rest) };
        assert(q.contains(m));
        assert forall |y: int| q.contains(y) implies y <= m by { if y != x { assert(rest.contains(y)); } }
        assert(exists |v: int| q.contains(v) && forall |w: int| q.contains(w) ==> w <= v);
    }
}
pub open spec fn dominates(a: Summary,b: Summary) -> bool {
    a.epoch > b.epoch || a.epoch == b.epoch && !newer(b.zxid,a.zxid)
}
pub proof fn greatest(q: Set<Summary>) -> (a: Summary)
    requires !q.is_empty()
    ensures q.contains(a),forall |b: Summary| q.contains(b) ==> #[trigger] dominates(a,b)
    decreases q.len()
{
    let x=choose |x: Summary| q.contains(x); let r=q.remove(x);
    if r.is_empty() { x }
    else {
        let y=greatest(r); let a=if dominates(x,y) { x } else { y };
        assert forall |b: Summary| q.contains(b) implies #[trigger] dominates(a,b) by {
            if b != x { assert(r.contains(b)); assert(dominates(y,b)); }
        }
        a
    }
}
pub proof fn selected_origin(q: Set<AE>) -> (a: AE)
    requires !q.is_empty()
    ensures q.contains(a),select_history(q) == a.history
{
    let summaries=q.map(|a: AE| Summary { sid: a.sid,epoch: a.epoch,zxid: last(a.history) });
    let x=choose |x: AE| q.contains(x);
    assert(summaries.contains(Summary { sid: x.sid,epoch: x.epoch,zxid: last(x.history) }));
    let best=greatest(summaries);
    assert forall |b: Summary| #![trigger summaries.contains(b)] summaries.contains(b) && b != best implies best.epoch > b.epoch || best.epoch == b.epoch && !newer(b.zxid,best.zxid) by { assert(dominates(best,b)); }
    assert(exists |a: Summary| summaries.contains(a) && forall |b: Summary| #![trigger summaries.contains(b)] summaries.contains(b) && b != a ==> a.epoch > b.epoch || a.epoch == b.epoch && !newer(b.zxid,a.zxid));
    let selected=choose |a: Summary| summaries.contains(a) && forall |b: Summary| #![trigger summaries.contains(b)] summaries.contains(b) && b != a ==> a.epoch > b.epoch || a.epoch == b.epoch && !newer(b.zxid,a.zxid);
    assert(summaries.contains(selected));
    let origin=choose |a: AE| #![trigger q.contains(a)] q.contains(a) && Summary { sid: a.sid,epoch: a.epoch,zxid: last(a.history) } == selected;
    assert(q.contains(origin) && origin.sid == selected.sid);
    choose |a: AE| #![trigger q.contains(a)] q.contains(a) && a.sid == selected.sid
}
pub proof fn selected_maximal(q: Set<AE>) -> (a: AE)
    requires !q.is_empty(),forall |r: AE,t: AE| #![trigger q.contains(r), q.contains(t)] q.contains(r) && q.contains(t) && r.sid == t.sid ==> r == t
    ensures q.contains(a),select_history(q) == a.history,
        forall |r: AE| #![trigger q.contains(r)] q.contains(r) ==> a.epoch > r.epoch || a.epoch == r.epoch && !newer(last(r.history),last(a.history))
{
    let summaries=q.map(|r: AE| Summary { sid: r.sid,epoch: r.epoch,zxid: last(r.history) });
    let member=choose |r: AE| q.contains(r);
    assert(summaries.contains(Summary { sid: member.sid,epoch: member.epoch,zxid: last(member.history) }));
    let best=greatest(summaries);
    assert forall |b: Summary| #![trigger summaries.contains(b)] summaries.contains(b) && b != best implies best.epoch > b.epoch || best.epoch == b.epoch && !newer(b.zxid,best.zxid) by { assert(dominates(best,b)); }
    let selected=choose |a: Summary| summaries.contains(a) && forall |b: Summary| #![trigger summaries.contains(b)] summaries.contains(b) && b != a ==> a.epoch > b.epoch || a.epoch == b.epoch && !newer(b.zxid,a.zxid);
    let origin=choose |r: AE| #![trigger q.contains(r)] q.contains(r) && Summary { sid: r.sid,epoch: r.epoch,zxid: last(r.history) } == selected;
    assert(q.contains(origin) && origin.sid == selected.sid);
    let a=choose |a: AE| #![trigger q.contains(a)] q.contains(a) && a.sid == selected.sid;
    assert(a == origin);
    assert forall |r: AE| #![trigger q.contains(r)] q.contains(r) implies a.epoch > r.epoch || a.epoch == r.epoch && !newer(last(r.history),last(a.history)) by {
        let summary=Summary { sid: r.sid,epoch: r.epoch,zxid: last(r.history) }; assert(summaries.contains(summary));
    }
    a
}
pub proof fn ce_update(q: Set<CE>,i: int,e: int)
    ensures ce_ids(update_ce(q,i,e)) =~= ce_ids(q).insert(i)
{
    if ce_ids(q).contains(i) {
        let old=choose |r: CE| #![trigger q.contains(r)] q.contains(r) && r.sid == i;
        assert(q.contains(old) && old.sid == i);
    }
    assert forall |j: int| #![trigger ce_ids(q).insert(i).contains(j)] ce_ids(update_ce(q,i,e)).contains(j) <==> ce_ids(q).insert(i).contains(j) by {
        if ce_ids(q).contains(j) && j != i {
            let r=choose |r: CE| #![trigger q.contains(r)] q.contains(r) && r.sid == j;
            assert(update_ce(q,i,e).contains(r));
        }
        if j == i { assert(update_ce(q,i,e).contains(CE { sid: i,connected: true,epoch: e })); }
    }
}
pub proof fn ae_update(q: Set<AE>,i: int,e: int,h: Seq<Txn>)
    ensures ae_ids(update_ae(q,i,e,h)) =~= ae_ids(q).insert(i)
{
    if ae_ids(q).contains(i) {
        let old=choose |r: AE| #![trigger q.contains(r)] q.contains(r) && r.sid == i;
        assert(q.contains(old) && old.sid == i);
    }
    assert forall |j: int| #![trigger ae_ids(q).insert(i).contains(j)] ae_ids(update_ae(q,i,e,h)).contains(j) <==> ae_ids(q).insert(i).contains(j) by {
        if ae_ids(q).contains(j) && j != i {
            let r=choose |r: AE| #![trigger q.contains(r)] q.contains(r) && r.sid == j;
            assert(update_ae(q,i,e,h).contains(r));
        }
        if j == i { assert(update_ae(q,i,e,h).contains(AE { sid: i,connected: true,epoch: e,history: h })); }
    }
}
pub proof fn al_update(q: Set<AL>,i: int)
    ensures al_ids(update_al(q,i)) =~= al_ids(q).insert(i)
{
    if al_ids(q).contains(i) {
        let old=choose |r: AL| #![trigger q.contains(r)] q.contains(r) && r.sid == i;
        assert(q.contains(old) && old.sid == i);
    }
    assert forall |j: int| al_ids(update_al(q,i)).contains(j) <==> al_ids(q).insert(i).contains(j) by {
        if al_ids(q).contains(j) && j != i {
            let r=choose |r: AL| #![trigger q.contains(r)] q.contains(r) && r.sid == j;
            assert(update_al(q,i).contains(r));
        }
        if j == i { assert(update_al(q,i).contains(AL { sid: i,connected: true })); }
    }
}
pub proof fn disconnect_ids(ce: Set<CE>,ae: Set<AE>,al: Set<AL>,i: int)
    ensures ce_ids(disconnect_ce(ce,i)) =~= ce_ids(ce),ae_ids(disconnect_ae(ae,i)) =~= ae_ids(ae),al_ids(disconnect_al(al,i)) =~= al_ids(al)
{
    if ce_ids(ce).contains(i) {
        let old=choose |r: CE| #![trigger ce.contains(r)] ce.contains(r) && r.sid == i; assert(ce.contains(old) && old.sid == i);
        assert(disconnect_ce(ce,i).contains(CE { connected: false,..old }));
    }
    if ae_ids(ae).contains(i) {
        let old=choose |r: AE| #![trigger ae.contains(r)] ae.contains(r) && r.sid == i; assert(ae.contains(old) && old.sid == i);
        assert(disconnect_ae(ae,i).contains(AE { connected: false,..old }));
    }
    if al_ids(al).contains(i) {
        let old=choose |r: AL| #![trigger al.contains(r)] al.contains(r) && r.sid == i; assert(al.contains(old) && old.sid == i);
        assert(disconnect_al(al,i).contains(AL { connected: false,..old }));
    }
    assert forall |j: int| #![trigger ce_ids(ce).contains(j)] ce_ids(disconnect_ce(ce,i)).contains(j) <==> ce_ids(ce).contains(j) by {
        if ce_ids(ce).contains(j) && j != i {
            let r=choose |r: CE| #![trigger ce.contains(r)] ce.contains(r) && r.sid == j;
            assert(disconnect_ce(ce,i).contains(r));
        }
    }
    assert forall |j: int| #![trigger ae_ids(ae).contains(j)] ae_ids(disconnect_ae(ae,i)).contains(j) <==> ae_ids(ae).contains(j) by {
        if ae_ids(ae).contains(j) && j != i {
            let r=choose |r: AE| #![trigger ae.contains(r)] ae.contains(r) && r.sid == j;
            assert(disconnect_ae(ae,i).contains(r));
        }
    }
    assert forall |j: int| #![trigger al_ids(al).contains(j)] al_ids(disconnect_al(al,i)).contains(j) <==> al_ids(al).contains(j) by {
        if al_ids(al).contains(j) && j != i {
            let r=choose |r: AL| #![trigger al.contains(r)] al.contains(r) && r.sid == j;
            assert(disconnect_al(al,i).contains(r));
        }
    }
}
pub proof fn quorum_add(q: Set<int>,c: Constants,i: int)
    requires q.subset_of(c.servers),c.servers.contains(i)
    ensures quorum(q,c) ==> quorum(q.insert(i),c)
{
    vstd::set_lib::lemma_len_subset(q,q.insert(i));
}
pub proof fn record_ids(n: LServer)
    ensures forall |r: CE| #![trigger n.ce.contains(r)] n.ce.contains(r) ==> ce_ids(n.ce).contains(r.sid),
        forall |r: AE| #![trigger n.ae.contains(r)] n.ae.contains(r) ==> ae_ids(n.ae).contains(r.sid),
        forall |r: AL| #![trigger n.al.contains(r)] n.al.contains(r) ==> al_ids(n.al).contains(r.sid)
{
    assert forall |r: CE| #![trigger n.ce.contains(r)] n.ce.contains(r) implies ce_ids(n.ce).contains(r.sid) by {}
    assert forall |r: AE| #![trigger n.ae.contains(r)] n.ae.contains(r) implies ae_ids(n.ae).contains(r.sid) by {}
    assert forall |r: AL| #![trigger n.al.contains(r)] n.al.contains(r) implies al_ids(n.al).contains(r.sid) by {}
}
pub proof fn quorum_superset(q: Set<int>,r: Set<int>,c: Constants)
    requires quorum(q,c),q.subset_of(r),r.subset_of(c.servers)
    ensures quorum(r,c)
{
    vstd::set_lib::lemma_len_subset(q,r);
}
pub proof fn fresh_ids(n: LServer,i: int)
    ensures ce_ids(lead(n,i).ce) =~= set![i],ae_ids(lead(n,i).ae) =~= set![i],al_ids(lead(n,i).al) =~= set![i]
{
    let u=lead(n,i);
    assert(u.ce.contains(CE { sid: i,connected: true,epoch: n.accepted }));
    assert(u.ae.contains(AE { sid: i,connected: true,epoch: n.current,history: n.history }));
    assert(u.al.contains(AL { sid: i,connected: true }));
    assert(ce_ids(u.ce).contains(i)); assert(ae_ids(u.ae).contains(i)); assert(al_ids(u.al).contains(i));
}
pub proof fn intersect_quorums(q: Set<int>,r: Set<int>,c: Constants) -> (j: int)
    requires quorum(q,c),quorum(r,c)
    ensures q.contains(j),r.contains(j),c.servers.contains(j)
{
    if q.disjoint(r) {
        vstd::set_lib::lemma_set_disjoint_lens(q,r);
        assert(q.union(r).subset_of(c.servers)); vstd::set_lib::lemma_len_subset(q.union(r),c.servers); assert(false);
    }
    choose |j: int| q.contains(j) && r.contains(j)
}
} // verus!
