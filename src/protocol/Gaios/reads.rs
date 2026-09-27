//! SMARTER read protocol, NSDI 2011 Section 3.3.2, fixed membership.
//! View replies are separate events and may be delayed. Timestamps are proof
//! event order, not synchronized clocks used by the protocol.
//! Paxos host contracts: recovery covers lower-view decisions; a leader knows
//! its own committed prefix. Concrete view-change/metadata refinement is open.
use vstd::prelude::*;
use super::super::ConsensusSafety::{paxos as p, register_history as h};
verus! {
pub struct Config { pub paxos: p::Config, pub read_quorums: Set<Set<int>> }
pub struct View { pub quorum: Set<int>, pub recovered: int, pub elected: int }
pub struct Stamp { pub view: int, pub at: int, pub known: int, pub cut: int, pub replies: Map<int, int> }
pub struct Protocol {
    pub history: h::History,
    pub write_views: Seq<int>,
    pub views: Map<int, View>,
    pub recognitions: Map<(int, int), int>, // node, view -> recognition time
    pub stamps: Map<int, Stamp>,
    pub slot_states: Map<int, Seq<p::State>>,
    pub slot_actions: Map<int, Seq<p::Action>>,
}
pub open spec fn config_ok(c: Config) -> bool {
    p::config_ok(c.paxos) && forall|q: Set<int>| c.read_quorums.contains(q) ==>
        q.subset_of(c.paxos.acceptors) && forall|r: Set<int>| c.paxos.quorums.contains(r)
            ==> exists|a: int| q.contains(a) && r.contains(a)
}
pub open spec fn host_ok(s: Protocol, c: Config) -> bool {
    &&& h::execution_ok(s.history) && s.write_views.len() == s.history.writes.len()
    &&& forall|v: int| s.views.dom().contains(v) ==> c.paxos.quorums.contains(s.views[v].quorum)
        && s.views[v].recovered >= 0
        && forall|a: int| s.views[v].quorum.contains(a) ==> s.recognitions.dom().contains((a, v))
            && s.recognitions[(a, v)] <= s.views[v].elected
    &&& forall|i: int| 0 <= i < s.history.writes.len() ==> {
        let v = s.write_views[i];
        s.views.dom().contains(v) && s.views[v].elected <= s.history.writes[i].commit
        && s.slot_states.dom().contains(i) && s.slot_actions.dom().contains(i)
        && #[trigger] p::behavior(s.slot_states[i], s.slot_actions[i], c.paxos)
        && p::quorum_chosen(s.slot_states[i].last(), c.paxos, v, s.history.writes[i].value)
    }
    // The prepared/reproposed horizon includes all possible earlier-view decisions.
    &&& forall|v: int, i: int| s.views.dom().contains(v) && 0 <= i < s.history.writes.len()
        && s.write_views[i] < v ==> i < s.views[v].recovered
}
pub open spec fn read_protocol(s: Protocol, c: Config) -> bool {
    &&& s.stamps.dom() == s.history.reads.dom()
    &&& forall|r: int| s.stamps.dom().contains(r) ==> {
        let st = s.stamps[r]; let rd = s.history.reads[r];
        &&& s.views.dom().contains(st.view)
        &&& rd.call <= st.at < rd.execute
        &&& st.cut == if st.known >= s.views[st.view].recovered { st.known } else { s.views[st.view].recovered }
        &&& rd.cut >= st.cut
        &&& c.read_quorums.contains(st.replies.dom())
        &&& forall|a: int| st.replies.dom().contains(a) ==> st.at < st.replies[a] < rd.execute
        // A reply reporting this view cannot follow recognition of a higher view.
        &&& forall|a: int, v: int| st.replies.dom().contains(a) && s.recognitions.dom().contains((a, v))
            && s.recognitions[(a, v)] <= st.replies[a] ==> v <= st.view
        // The leader stamps its own actual committed prefix at receipt time.
        &&& forall|i: int| 0 <= i < s.history.writes.len() && s.write_views[i] == st.view
            && s.history.writes[i].commit <= st.at ==> i < st.known
    }
}
pub proof fn read_is_fresh(s: Protocol, c: Config, r: int, i: int)
    requires config_ok(c), host_ok(s, c), read_protocol(s, c),
        s.history.reads.dom().contains(r), 0 <= i < s.history.writes.len(),
        s.history.writes[i].commit < s.history.reads[r].call,
    ensures i < s.history.reads[r].cut,
{
    assert(p::behavior(s.slot_states[i], s.slot_actions[i], c.paxos));
    let st = s.stamps[r]; let v = s.write_views[i];
    assert(s.views.dom().contains(v));
    if v > st.view {
        let q = s.views[v].quorum; let rq = st.replies.dom();
        assert(c.paxos.quorums.contains(q) && c.read_quorums.contains(rq));
        let a = choose|a: int| rq.contains(a) && q.contains(a);
        assert(s.recognitions.dom().contains((a, v)));
        assert(s.recognitions[(a, v)] <= s.views[v].elected <= s.history.writes[i].commit);
        assert(st.at < st.replies[a]);
        assert(v <= st.view);
    } else if v < st.view {
        assert(i < s.views[st.view].recovered);
    } else { assert(i < st.known); }
}
pub proof fn linearizable_reads_and_writes(s: Protocol, c: Config)
    requires config_ok(c), host_ok(s, c), read_protocol(s, c),
    ensures h::linearization(s.history, |a: h::Op, b: h::Op| h::before(s.history, a, b)),
        exists|order: spec_fn(h::Op, h::Op) -> bool| h::linearization(s.history, order),
{
    assert forall|r: int, i: int| s.history.reads.dom().contains(r) && 0 <= i < s.history.writes.len()
        && s.history.writes[i].commit < s.history.reads[r].call implies i < s.history.reads[r].cut by {
        read_is_fresh(s, c, r, i);
    }
    h::history_linearizable(s.history);
}
pub proof fn committed_slot_agreement(s: Protocol, c: Config, i: int, k: int, v: int)
    requires config_ok(c), host_ok(s, c), 0 <= i < s.history.writes.len(),
        0 <= k < s.slot_states[i].len(), p::learned(s.slot_states[i][k], c.paxos, v),
    ensures v == s.history.writes[i].value,
{
    assert(p::behavior(s.slot_states[i], s.slot_actions[i], c.paxos));
    let ss = s.slot_states[i]; let aa = s.slot_actions[i];
    assert(p::learned(ss.last(), c.paxos, s.history.writes[i].value));
    p::behavior_agreement(ss, aa, c.paxos, k, ss.len() as int - 1, v, s.history.writes[i].value);
}
} // verus!
