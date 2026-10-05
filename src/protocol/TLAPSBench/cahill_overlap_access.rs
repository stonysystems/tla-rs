//! New reads and writes either set both edge flags or abort a participant.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_history as history;
use super::cahill_keys as keys_math;
use super::cahill_support as support;
use super::cahill_records as records;
use super::cahill_lifecycle as lifecycle;
use super::cahill_history_order as order;
use super::cahill_recent as recent;
use super::cahill_first_committer as first;
use super::cahill_writer_intervals as intervals;
use super::cahill_versions as versions;
use super::cahill_flags as flags;
use super::cahill_overlap as overlap;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub proof fn read_safe(s: LState,c: Constants,t: int,k: int)
    requires support::inductive(s,c),records::exact(s,c),lifecycle::valid(s.history),s.history.no_duplicates(),intervals::safe(s),first::safe(s,c),overlap::safe(s,c),
        c.txns.contains(t),active(s.history).contains(t),!version(s,t,k).is_empty()
    ensures overlap::safe(read(s,c,t,k),c)
{
    reveal(read); let u=read(s,c,t,k); flags::read_retained(s,c,t,k);
    let v=choose |v: int| version(s,t,k).contains(v); let e=Event { txn: t,op: Op::Read { key: k,version: v } }; let fail=Event { txn: t,op: Op::Abort(Reason::ReadConflict) };
    history::append(s.history,e); history::append(s.history,fail); lifecycle::append(s.history,e); lifecycle::append(s.history,fail);
    assert(s.history.is_prefix_of(u.history));
    let rejected=exists |w: int| newer_versions(s,t,k).contains(w) && committed(s.history).contains(w) && s.txns[w].outgoing;
    assert forall |r: int,w: int,key: int| c.txns.contains(r) && c.txns.contains(w) && #[trigger] overlap::edge(u,r,w,key)
        implies u.txns[r].outgoing && u.txns[w].incoming by {
        keys_math::append(s.history,e,r,true); keys_math::append(s.history,e,w,false);
        keys_math::append(s.history,fail,r,true); keys_math::append(s.history,fail,w,false);
        if rejected || keys(s.history,r,true).contains(key) { overlap::inherited(s,u,c,r,w,key); }
        else {
            assert(r == t && key == k); assert(keys(s.history,w,false).contains(k)); keys_math::member_all(s.history,w,false,k);
            overlap::old_overlap(s.history,u.history,t,w); assert(records::node(s,w));
            let others=c.txns.filter(|w: int| w != t && s.txns[w].xlocks.contains(k));
            if active(s.history).contains(w) {
                assert(s.txns[w].xlocks.contains(k)); assert(others.contains(w)); assert(!others.is_empty());
            } else {
                assert(committed(s.history).contains(w)); order::endpoint(s.history,w); lifecycle::start_position(s.history,t);
                assert(position(s.history,Event { txn: w,op: Op::Commit }) != start(s.history,t));
                recent::member(s,t,k,w); assert(writers_since(s,t,k).contains(w));
                if s.txns[t].xlocks.contains(k) { assert(first::protected(s,t,k)); assert(writers_since(s,t,k).is_empty()); assert(false); }
                versions::committed_newer(s,t,k,w); assert(!newer_versions(s,t,k).is_empty());
            }
        }
    }
}
pub proof fn acquire_safe(s: LState,c: Constants,t: int,k: int)
    requires records::exact(s,c),lifecycle::valid(s.history),overlap::safe(s,c),c.txns.contains(t),active(s.history).contains(t)
    ensures overlap::safe(acquire(s,c,t,k),c)
{
    reveal(acquire); let u=acquire(s,c,t,k); flags::acquire_retained(s,c,t,k);
    let e=Event { txn: t,op: Op::Write(k) }; let fail=Event { txn: t,op: Op::Abort(Reason::WriteConflict) };
    history::append(s.history,e); history::append(s.history,fail); lifecycle::append(s.history,e); lifecycle::append(s.history,fail);
    assert(s.history.is_prefix_of(u.history));
    let readers=concurrent_readers(s,c,t,k); let rejected=exists |r: int| readers.contains(r) && (committed(s.history).contains(r) || s.txns[r].incoming);
    assert forall |r: int,w: int,key: int| c.txns.contains(r) && c.txns.contains(w) && #[trigger] overlap::edge(u,r,w,key)
        implies u.txns[r].outgoing && u.txns[w].incoming by {
        keys_math::append(s.history,e,r,true); keys_math::append(s.history,e,w,false);
        keys_math::append(s.history,fail,r,true); keys_math::append(s.history,fail,w,false);
        if rejected || keys(s.history,w,false).contains(key) { overlap::inherited(s,u,c,r,w,key); }
        else {
            assert(w == t && key == k); assert(keys(s.history,r,true).contains(k)); keys_math::member_all(s.history,r,true,k);
            overlap::old_overlap(s.history,u.history,r,t); assert(records::node(s,r)); assert(s.txns[r].siread.contains(k));
            lifecycle::start_position(s.history,t);
            if committed(s.history).contains(r) {
                order::endpoint(s.history,r); assert(position(s.history,Event { txn: r,op: Op::Commit }) != start(s.history,t));
            }
            assert(readers.contains(r)); assert(!readers.is_empty());
        }
    }
}
} // verus!
