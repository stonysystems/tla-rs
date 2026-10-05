//! Election receipts retain each positive acknowledgment until leadership ends.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role};
use super::zk_election as fle;
use super::zookeeper_channels as channels;
use super::zookeeper_receipts as receipts;
use super::zookeeper_receipt_sets as sets;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn ids(q: Set<Electing>) -> Set<int> { q.filter(|e: Electing| e.quorum).map(|e: Electing| e.sid) }
pub open spec fn member(q: Set<Electing>,i: int) -> bool { exists |r: Electing| q.contains(r) && r.sid == i && r.quorum }
pub proof fn membership(q: Set<Electing>,i: int)
    ensures ids(q).contains(i) <==> member(q,i)
{
    if member(q,i) {
        let r=choose |r: Electing| q.contains(r) && r.sid == i && r.quorum;
        assert(q.filter(|e: Electing| e.quorum).contains(r));
        q.filter(|e: Electing| e.quorum).lemma_map_contains(|e: Electing| e.sid,i);
    }
}
pub proof fn update(q: Set<Electing>,c: Constants,j: int,zxid: z::Zxid,yes: bool,i: int)
    requires sets::electing(q,c)
    ensures member(update_e(q,j,zxid,yes),i) <==> member(q,i) || i == j && yes
{
    if member(update_e(q,j,zxid,yes),i) {
        let r=choose |r: Electing| update_e(q,j,zxid,yes).contains(r) && r.sid == i && r.quorum;
        if q.contains(r) { assert(member(q,i)); }
        else if !(i == j && yes) {
            let old=choose |r: Electing| q.contains(r) && r.sid == j; assert(q.contains(old) && old.quorum && old.sid == i); assert(member(q,i));
        }
    }
    if member(q,i) {
        let r=choose |r: Electing| q.contains(r) && r.sid == i && r.quorum;
        if i != j { assert(update_e(q,j,zxid,yes).contains(r)); }
        else { assert(update_e(q,j,zxid,yes).contains(Electing { sid: j,zxid,quorum: true })); }
    }
    if i == j && yes { assert(update_e(q,j,zxid,yes).contains(Electing { sid: j,zxid,quorum: true })); }
}
pub proof fn disconnect(q: Set<Electing>,c: Constants,j: int,i: int)
    requires sets::electing(q,c)
    ensures member(disconnect_e(q,j),i) <==> member(q,i)
{
    if member(disconnect_e(q,j),i) {
        let r=choose |r: Electing| disconnect_e(q,j).contains(r) && r.sid == i && r.quorum;
        if q.contains(r) { assert(member(q,i)); }
        else { let old=choose |r: Electing| q.contains(r) && r.sid == j; assert(q.contains(old) && old.sid == i && old.quorum); assert(member(q,i)); }
    }
    if member(q,i) {
        let r=choose |r: Electing| q.contains(r) && r.sid == i && r.quorum;
        if i != j { assert(disconnect_e(q,j).contains(r)); }
        else { assert(disconnect_e(q,j).contains(Electing { zxid: unset(),..r })); }
    }
}
pub proof fn clear(q: Set<Electing>,r: Electing,i: int)
    ensures member(q.remove(r).insert(Electing { zxid: unset(),..r }),i) <==> member(q,i) || r.sid == i && r.quorum
{
    let u=q.remove(r).insert(Electing { zxid: unset(),..r });
    if member(u,i) { let t=choose |t: Electing| u.contains(t) && t.sid == i && t.quorum; if t != (Electing { zxid: unset(),..r }) { assert(q.contains(t)); assert(member(q,i)); } }
    if member(q,i) { let t=choose |t: Electing| q.contains(t) && t.sid == i && t.quorum; if t != r { assert(u.contains(t)); } else { assert(u.contains(Electing { zxid: unset(),..r })); } }
    if r.sid == i && r.quorum { assert(u.contains(Electing { zxid: unset(),..r })); }
}
pub open spec fn origin(s: LState,u: LState,a: Action,i: int,j: int) -> bool {
    u.election.nodes[i].role == Role::Leading && member(u.nodes[i].electing,j) && j != i ==>
        s.election.nodes[i].role == Role::Leading && (member(s.nodes[i].electing,j)
            || a == Action::AckEpoch(i,j) && s.msgs[(j,i)][0] is AckEpoch && s.msgs[(j,i)][0]->AckEpoch_1 >= 0)
}
pub proof fn election_origin(s: LState,c: Constants,ea: fle::Action,i: int,j: int)
    requires channels::safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i)
    ensures origin(s,apply(s,c,Action::Election(ea)),Action::Election(ea),i,j)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x);
}
pub proof fn protocol_origin(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election)
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    reveal(enabled); reveal(apply); let x=receiver(a); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[y].electing,c,x,j); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);
            if a is AckEpoch {
                if let Message::AckEpoch(zxid,report)=s.msgs[(y,x)][0] {
                    let en=s.election.nodes[x]; let yes=!election_finished(s,c,x) && report > -1 && !(report > en.current || report == en.current && z::newer(zxid,en.processed.zxid));
                    update(s.nodes[x].electing,c,y,zxid,yes,j);
                }
            }
            if a is Sync {
                let r=choose |r: Electing| s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
                clear(s.nodes[x].electing,r,j); if r.sid == j && r.quorum { assert(member(s.nodes[x].electing,j)); }
            }
        },_ => {},
    }
}
pub proof fn step(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    if let Action::Election(ea)=a {
        election_origin(s,c,ea,i,j); reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(a); channels::facts(s,c,i,x);
    } else { protocol_origin(s,c,a,i,j); }
}
pub proof fn finished_retained(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),s.election.nodes[i].role == Role::Leading,
        apply(s,c,a).election.nodes[i].role == Role::Leading,election_finished(s,c,i)
    ensures election_finished(apply(s,c,a),c,i)
{
    let u=apply(s,c,a); receipts::preserve(s,c,a); assert(receipts::node(u,c,i));
    assert(ids(u.nodes[i].electing).subset_of(c.servers)) by {
        assert forall |j: int| ids(u.nodes[i].electing).contains(j) implies c.servers.contains(j) by {
            membership(u.nodes[i].electing,j); let r=choose |r: Electing| u.nodes[i].electing.contains(r) && r.sid == j && r.quorum;
            u.nodes[i].electing.lemma_map_contains(|r: Electing| r.sid,j);
        }
    }
    assert(ids(s.nodes[i].electing).subset_of(ids(u.nodes[i].electing))) by {
        assert forall |j: int| ids(s.nodes[i].electing).contains(j) implies ids(u.nodes[i].electing).contains(j) by {
            membership(s.nodes[i].electing,j); step(s,c,a,i,j); membership(u.nodes[i].electing,j);
        }
    }
    super::zab_collections::quorum_superset(ids(s.nodes[i].electing),ids(u.nodes[i].electing),c);
}
} // verus!
