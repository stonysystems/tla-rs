//! Disconnecting a learner clears the receipts that authorize synchronization traffic.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,AL};
use super::zookeeper_receipt_sets as sets;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn electing(q: Set<Electing>,j: int) -> bool { exists |r: Electing| q.contains(r) && r.sid == j && r.zxid != unset() }
pub open spec fn ackld(q: Set<AL>,j: int) -> bool { exists |r: AL| q.contains(r) && r.sid == j && r.connected }
pub proof fn disconnect_electing(q: Set<Electing>,c: Constants,x: int,j: int)
    requires sets::electing(q,c)
    ensures electing(disconnect_e(q,x),j) <==> electing(q,j) && j != x
{
    if electing(disconnect_e(q,x),j) {
        let r=choose |r: Electing| disconnect_e(q,x).contains(r) && r.sid == j && r.zxid != unset();
        assert(q.contains(r)); assert(electing(q,j));
        if j == x { let old=choose |r: Electing| q.contains(r) && r.sid == x; assert(old == r); assert(false); }
    }
    if electing(q,j) && j != x { let r=choose |r: Electing| q.contains(r) && r.sid == j && r.zxid != unset(); assert(disconnect_e(q,x).contains(r)); }
}
pub proof fn disconnect_ackld(q: Set<AL>,c: Constants,x: int,j: int)
    requires sets::al(q,c)
    ensures ackld(z::disconnect_al(q,x),j) <==> ackld(q,j) && j != x
{
    if ackld(z::disconnect_al(q,x),j) {
        let r=choose |r: AL| z::disconnect_al(q,x).contains(r) && r.sid == j && r.connected;
        assert(q.contains(r)); assert(ackld(q,j));
        if j == x { let old=choose |r: AL| q.contains(r) && r.sid == x; assert(old == r); assert(false); }
    }
    if ackld(q,j) && j != x { let r=choose |r: AL| q.contains(r) && r.sid == j && r.connected; assert(z::disconnect_al(q,x).contains(r)); }
}
pub proof fn update_electing(q: Set<Electing>,x: int,zxid: z::Zxid,yes: bool,j: int)
    ensures electing(update_e(q,x,zxid,yes),j) ==> electing(q,j) || j == x
{
    if electing(update_e(q,x,zxid,yes),j) {
        let r=choose |r: Electing| update_e(q,x,zxid,yes).contains(r) && r.sid == j && r.zxid != unset();
        if j != x { assert(q.contains(r)); assert(electing(q,j)); }
    }
}
pub proof fn update_ackld(q: Set<AL>,x: int,j: int)
    ensures ackld(z::update_al(q,x),j) ==> ackld(q,j) || j == x
{
    if ackld(z::update_al(q,x),j) { let r=choose |r: AL| z::update_al(q,x).contains(r) && r.sid == j && r.connected; if j != x { assert(q.contains(r)); assert(ackld(q,j)); } }
}
pub proof fn clear_electing(q: Set<Electing>,r: Electing,j: int)
    ensures electing(q.remove(r).insert(Electing { zxid: unset(),..r }),j) ==> electing(q,j)
{
    if electing(q.remove(r).insert(Electing { zxid: unset(),..r }),j) {
        let t=choose |t: Electing| q.remove(r).insert(Electing { zxid: unset(),..r }).contains(t) && t.sid == j && t.zxid != unset();
        assert(q.contains(t)); assert(electing(q,j));
    }
}
pub proof fn connected_member(q: Set<AL>,j: int)
    ensures z::al_connected(q).contains(j) <==> ackld(q,j)
{
    if ackld(q,j) {
        let r=choose |r: AL| q.contains(r) && r.sid == j && r.connected; assert(q.filter(|r: AL| r.connected).contains(r));
        q.filter(|r: AL| r.connected).lemma_map_contains(|r: AL| r.sid,j);
    }
}
pub proof fn clear_current(q: Set<Electing>,c: Constants,r: Electing)
    requires sets::electing(q,c),q.contains(r)
    ensures !electing(q.remove(r).insert(Electing { zxid: unset(),..r }),r.sid)
{
    if electing(q.remove(r).insert(Electing { zxid: unset(),..r }),r.sid) {
        let t=choose |t: Electing| q.remove(r).insert(Electing { zxid: unset(),..r }).contains(t) && t.sid == r.sid && t.zxid != unset();
        assert(q.contains(t)); assert(t == r); assert(false);
    }
}
} // verus!
