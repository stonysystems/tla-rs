//! Receipt updates preserve configured identities and one receipt per server.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,AL,Zxid};
use super::zab_collections as collections;
verus! {
broadcast use { vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn al(q: Set<AL>,c: Constants) -> bool {
    z::al_ids(q).subset_of(c.servers) && forall |r: AL,t: AL| #![trigger q.contains(r), q.contains(t)] q.contains(r) && q.contains(t) && r.sid == t.sid ==> r == t
}
pub open spec fn ids(q: Set<Electing>) -> Set<int> { q.map(|r: Electing| r.sid) }
pub open spec fn electing(q: Set<Electing>,c: Constants) -> bool {
    ids(q).subset_of(c.servers) && forall |r: Electing,t: Electing| #![trigger q.contains(r), q.contains(t)] q.contains(r) && q.contains(t) && r.sid == t.sid ==> r == t
}
pub proof fn al_update(q: Set<AL>,c: Constants,i: int)
    requires al(q,c),c.servers.contains(i)
    ensures al(z::update_al(q,i),c),z::al_ids(z::update_al(q,i)) == z::al_ids(q).insert(i),
        forall |r: AL| #![trigger q.contains(r)] q.contains(r) && r.sid != i ==> z::update_al(q,i).contains(r)
{
    collections::al_update(q,i);
    if z::al_ids(q).contains(i) { let old=choose |r: AL| #![trigger q.contains(r)] q.contains(r) && r.sid == i; assert(q.contains(old) && old.sid == i); }
    assert forall |r: AL,t: AL| #![trigger z::update_al(q,i).contains(r), z::update_al(q,i).contains(t)] z::update_al(q,i).contains(r) && z::update_al(q,i).contains(t) && r.sid == t.sid implies r == t by {}
}
pub proof fn al_disconnect(q: Set<AL>,c: Constants,i: int)
    requires al(q,c)
    ensures al(z::disconnect_al(q,i),c),z::al_ids(z::disconnect_al(q,i)) == z::al_ids(q),
        forall |r: AL| #![trigger q.contains(r)] q.contains(r) && r.sid != i ==> z::disconnect_al(q,i).contains(r)
{
    collections::disconnect_ids(Set::empty(),Set::empty(),q,i);
    if z::al_ids(q).contains(i) { let old=choose |r: AL| #![trigger q.contains(r)] q.contains(r) && r.sid == i; assert(q.contains(old) && old.sid == i); }
    assert forall |r: AL,t: AL| #![trigger z::disconnect_al(q,i).contains(r), z::disconnect_al(q,i).contains(t)] z::disconnect_al(q,i).contains(r) && z::disconnect_al(q,i).contains(t) && r.sid == t.sid implies r == t by {}
}
pub proof fn electing_replace(q: Set<Electing>,c: Constants,r: Electing,t: Electing)
    requires electing(q,c),q.contains(r),r.sid == t.sid
    ensures electing(q.remove(r).insert(t),c),ids(q.remove(r).insert(t)) == ids(q),
        forall |v: Electing| #![trigger q.contains(v)] q.contains(v) && v.sid != r.sid ==> q.remove(r).insert(t).contains(v)
{
    let u=q.remove(r).insert(t); assert(ids(q).contains(r.sid));
    assert(ids(u) =~= ids(q)) by {
        assert forall |i: int| ids(u).contains(i) <==> ids(q).contains(i) by {
            if ids(q).contains(i) { let v=choose |v: Electing| #![trigger q.contains(v)] q.contains(v) && v.sid == i; if i != r.sid { assert(u.contains(v)); } else { assert(u.contains(t)); } }
        }
    }
    assert forall |a: Electing,b: Electing| #![trigger u.contains(a), u.contains(b)] u.contains(a) && u.contains(b) && a.sid == b.sid implies a == b by {}
}
pub proof fn electing_update(q: Set<Electing>,c: Constants,i: int,zxid: Zxid,yes: bool)
    requires electing(q,c),c.servers.contains(i)
    ensures electing(update_e(q,i,zxid,yes),c),ids(update_e(q,i,zxid,yes)) == ids(q).insert(i),
        forall |r: Electing| #![trigger q.contains(r)] q.contains(r) && r.sid != i ==> update_e(q,i,zxid,yes).contains(r)
{
    let u=update_e(q,i,zxid,yes);
    if exists |r: Electing| #![trigger q.contains(r)] q.contains(r) && r.sid == i {
        let r=choose |r: Electing| #![trigger q.contains(r)] q.contains(r) && r.sid == i;
        electing_replace(q,c,r,Electing { sid: i,zxid,quorum: yes || r.quorum }); assert(ids(q).contains(i));
    } else {
        assert(!ids(q).contains(i));
        assert(ids(u) =~= ids(q).insert(i)) by {
            assert forall |j: int| #![trigger ids(u).contains(j)] ids(u).contains(j) <==> ids(q).insert(i).contains(j) by {
                if j == i { assert(u.contains(Electing { sid: i,zxid,quorum: yes })); }
                else if ids(q).contains(j) { let r=choose |r: Electing| #![trigger q.contains(r)] q.contains(r) && r.sid == j; assert(u.contains(r)); }
            }
        }
        assert forall |r: Electing,t: Electing| #![trigger u.contains(r), u.contains(t)] u.contains(r) && u.contains(t) && r.sid == t.sid implies r == t by {}
    }
}
pub proof fn electing_disconnect(q: Set<Electing>,c: Constants,i: int)
    requires electing(q,c)
    ensures electing(disconnect_e(q,i),c),ids(disconnect_e(q,i)) == ids(q),
        forall |r: Electing| #![trigger q.contains(r)] q.contains(r) && r.sid != i ==> disconnect_e(q,i).contains(r)
{
    if exists |r: Electing| #![trigger q.contains(r)] q.contains(r) && r.sid == i { let r=choose |r: Electing| #![trigger q.contains(r)] q.contains(r) && r.sid == i; electing_replace(q,c,r,Electing { zxid: unset(),..r }); }
}
pub proof fn singletons(c: Constants,i: int)
    requires c.servers.contains(i)
    ensures al(set![AL { sid: i,connected: true }],c),electing(set![Electing { sid: i,zxid: unset(),quorum: true }],c)
{
    let a=AL { sid: i,connected: true }; let e=Electing { sid: i,zxid: unset(),quorum: true }; let qa=set![a]; let qe=set![e];
    assert(qa.contains(a)); assert(qe.contains(e));
    qa.lemma_map_contains(|r: AL| r.sid,i); qe.lemma_map_contains(|r: Electing| r.sid,i);
    assert(z::al_ids(qa).contains(i)); assert(ids(qe).contains(i));
    assert(z::al_ids(qa) =~= set![i]); assert(ids(qe) =~= set![i]);
}
} // verus!
