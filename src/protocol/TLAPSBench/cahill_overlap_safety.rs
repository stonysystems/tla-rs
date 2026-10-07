//! Induction over every source action establishes the read/write conflict invariant.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_keys as keys_math;
use super::cahill_support as support;
use super::cahill_records as records;
use super::cahill_lifecycle as lifecycle;
use super::cahill_unique as unique;
use super::cahill_history_order as order;
use super::cahill_first_committer as first;
use super::cahill_writer_intervals as intervals;
use super::cahill_flags as flags;
use super::cahill_overlap as overlap;
use super::cahill_overlap_access as access;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::inductive(s,c),records::exact(s,c),lifecycle::valid(s.history),s.history.no_duplicates(),intervals::safe(s),first::safe(s,c),overlap::safe(s,c),enabled(s,c,a)
    ensures overlap::safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); lifecycle::preserve(s,c,a); order::step_prefix(s,c,a); flags::preserve(s,c,a);
    reveal(enabled); reveal(apply); reveal(commit);
    match a {
        Action::Read(t,k) => { access::read_safe(s,c,t,k); return; },
        Action::Finish(t) => { assert(support::node(s,c,t)); access::acquire_safe(s,c,t,s.txns[t].waiting.unwrap()); return; },
        Action::Write { txn: t,key: k,victim: v } => {
            if writers_since(s,t,k).is_empty() && !locked(s,c,k) { access::acquire_safe(s,c,t,k); return; }
        },
        _ => {},
    }
    assert forall |t: int| c.txns.contains(t) implies #[trigger] overlap::same_keys(s,u,t) by {
        match a {
            Action::Begin(r) => { let e=Event { txn: r,op: Op::Begin }; keys_math::append(s.history,e,t,true); keys_math::append(s.history,e,t,false); },
            Action::Abort(r) => { let e=Event { txn: r,op: Op::Abort(Reason::Voluntary) }; keys_math::append(s.history,e,t,true); keys_math::append(s.history,e,t,false); },
            Action::Commit(r) => {
                let e=Event { txn: r,op: Op::Commit }; keys_math::append(s.history,e,t,true); keys_math::append(s.history,e,t,false);
                keys_math::batch(s.history.push(e),losers(s,c,r),t,true); keys_math::batch(s.history.push(e),losers(s,c,r),t,false);
                let e=Event { txn: r,op: Op::Abort(Reason::CommitConflict) }; keys_math::append(s.history,e,t,true); keys_math::append(s.history,e,t,false);
            },
            Action::Write { txn: r,key: k,victim: v } => {
                let e=Event { txn: r,op: Op::Abort(Reason::FirstCommitter) }; keys_math::append(s.history,e,t,true); keys_math::append(s.history,e,t,false);
                let e=Event { txn: v,op: Op::Abort(Reason::Deadlock) }; keys_math::append(s.history,e,t,true); keys_math::append(s.history,e,t,false);
            },
            _ => {},
        }
    }
    overlap::unchanged(s,u,c);
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures overlap::safe(b[time],c)
    decreases time
{
    if time == 0 {
        let h=b[0].history; assert(h.to_set() =~= Set::<Event>::empty());
        assert forall |t: int,w: int,k: int| c.txns.contains(t) && c.txns.contains(w) && #[trigger] overlap::edge(b[0],t,w,k)
            implies b[0].txns[t].outgoing && b[0].txns[w].incoming by { keys_math::absent(h,t,true); }
    } else {
        at(b,c,time-1); support::at(b,c,time-1); records::at(b,c,time-1); lifecycle::at(b,c,time-1);
        unique::at(b,c,time-1); first::at(b,c,time-1); intervals::at(b,c,time-1);
        let a=support::step(b,c,time-1); preserve(b[time-1],c,a);
    }
}
} // verus!
