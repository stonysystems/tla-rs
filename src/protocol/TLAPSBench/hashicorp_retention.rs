//! Retain a decided prefix while later-term leaders below a bound contain it.
//! The completeness premise is explicit; it is a term-induction obligation.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_history::{self as history,step};
use super::hashicorp_replication as replication;
use super::hashicorp_prefixes as prefixes;
use super::hashicorp_commits as commits;
use super::temporal::Behavior;
verus! {
pub open spec fn compatible(a: Seq<Entry>,d: Seq<Entry>) -> bool { prefix(a,d) || prefix(d,a) }
pub proof fn reflexive(h: Seq<Entry>)
    ensures prefix(h,h)
{ assert(sub(h,1,h.len() as int) =~= h); }
pub proof fn transitive(a: Seq<Entry>,d: Seq<Entry>,e: Seq<Entry>)
    requires prefix(a,d),prefix(d,e)
    ensures prefix(a,e)
{ assert(sub(e,1,a.len() as int) =~= a); }
pub proof fn prefixes_compatible(a: Seq<Entry>,d: Seq<Entry>,h: Seq<Entry>)
    requires prefix(a,h),prefix(d,h)
    ensures compatible(a,d)
{
    if a.len() <= d.len() { assert(sub(d,1,a.len() as int) =~= a); }
    else { assert(sub(a,1,d.len() as int) =~= d); }
}
pub proof fn shorter(h: Seq<Entry>,a: Seq<Entry>,length: int)
    requires prefix(h,a),0 <= length <= h.len()
    ensures prefix(sub(h,1,length),a),prefix(sub(h,1,length),h)
{ assert(sub(h,1,length) =~= sub(a,1,length)); }
pub proof fn compatible_prefix(h: Seq<Entry>,a: Seq<Entry>,d: Seq<Entry>)
    requires prefix(h,a),compatible(a,d)
    ensures compatible(h,d)
{
    if prefix(a,d) { transitive(h,a,d); }
    else { prefixes_compatible(h,d,a); }
}
pub open spec fn decision(b: Behavior<LState>,c: Constants,time: int,i: int) -> bool { step(b,c,time) == Action::AdvanceCommit(i) }
pub open spec fn decided(b: Behavior<LState>,time: int,i: int) -> Seq<Entry> { sub(b[time].nodes[i].log,1,b[time+1].nodes[i].commit as int) }
pub open spec fn complete_below(b: Behavior<LState>,c: Constants,horizon: int,bound: nat) -> bool {
    forall |at: int,i: int,time: int,j: int| 0 <= at < horizon && 0 <= time <= horizon
        && decision(b,c,at,i) && c.servers.contains(j) && (#[trigger] b[time].nodes[j]).role == Role::Leader
        && (#[trigger] b[at].nodes[i]).term < b[time].nodes[j].term < bound
        ==> prefix(decided(b,at,i),b[time].nodes[j].log)
}
pub proof fn merge_retains(old: Seq<Entry>,m: Message,source: Seq<Entry>,h: Seq<Entry>)
    requires history::segment(m,source),prefix(h,old),compatible(h,source),m.body is AppendRequest,
        0 <= m.body->AppendRequest_prev <= old.len()
    ensures prefix(h,merge(old,m.body->AppendRequest_prev,m.body->AppendRequest_entries))
{
    let prev=m.body->AppendRequest_prev; let entries=m.body->AppendRequest_entries;
    types::first_mismatch(old,prev,entries,1); reveal(merge);
    let first=choose |j: int| 1 <= j <= entries.len()+1
        && (forall |q: int| 0 <= q < j-1 ==> prev+q < old.len() && old[prev+q].term == (#[trigger] entries[q]).term)
        && (j == entries.len()+1 || prev+j > old.len() || old[prev+j-1].term != (#[trigger] entries[j-1]).term);
    if entries.len() > 0 && first <= entries.len() {
        let cut=prev+first-1;
        if cut < h.len() {
            assert(cut < source.len()); assert(old[cut] == h[cut] && h[cut] == source[cut] && source[cut] == entries[first-1]); assert(false);
        }
        let out=merge(old,prev,entries); assert(sub(out,1,h.len() as int) =~= h);
    }
}
pub proof fn packet_compatible(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,m: Message,at: int,i: int) -> (sent: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),
        0 <= time <= horizon,0 <= at < horizon,decision(b,c,at,i),b[time].messages.count(m) > 0,m.body is AppendRequest,
        b[at].nodes[i].term <= m.term < bound
    ensures 0 <= sent < time,history::segment(m,b[sent].nodes[m.source].log),compatible(decided(b,at,i),b[sent].nodes[m.source].log)
{
    let sent=replication::request_bound(b,c,time,m); commits::decision_certificate(b,c,at,i);
    let h=decided(b,at,i); let source=b[sent].nodes[m.source].log;
    assert(prefix(h,b[at].nodes[i].log));
    if b[at].nodes[i].term < m.term { assert(prefix(h,source)); }
    else {
        assert(i == m.source);
        if at <= sent { history::continuous(b,c,i,at,sent); transitive(h,b[at].nodes[i].log,source); }
        else { history::continuous(b,c,i,sent,at); prefixes_compatible(h,source,b[at].nodes[i].log); }
    }
    sent
}
pub proof fn local_prefix(s: LState,c: Constants,a: Action,j: int,h: Seq<Entry>)
    requires enabled(s,c,a),c.servers.contains(j),prefix(h,s.nodes[j].log),
        match a { Action::Receive { m,how: Receive::AcceptAppend } => m.dest == j ==> prefix(h,merge(s.nodes[j].log,m.body->AppendRequest_prev,m.body->AppendRequest_entries)),_ => true }
    ensures prefix(h,apply(s,c,a).nodes[j].log)
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    if history::creates(a,j) { assert(sub(apply(s,c,a).nodes[j].log,1,h.len() as int) =~= h); }
}
pub proof fn preserve(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,j: int,at: int,i: int,length: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),
        0 <= time < horizon,0 <= at < horizon,decision(b,c,at,i),c.servers.contains(j),
        b[at].nodes[i].term <= b[time].nodes[j].term,b[time+1].nodes[j].term < bound,0 <= length <= decided(b,at,i).len(),
        prefix(sub(decided(b,at,i),1,length),b[time].nodes[j].log)
    ensures prefix(sub(decided(b,at,i),1,length),b[time+1].nodes[j].log)
{
    history::step_valid(b,c,time); types::safety_at(b,c,time); let a=step(b,c,time); let d=decided(b,at,i); let h=sub(d,1,length);
    if let Action::Receive { m,how } = a {
        if m.dest == j && how == Receive::AcceptAppend {
            reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
            assert(types::message(m,c)); let sent=packet_compatible(b,c,horizon,bound,time,m,at,i);
            assert(prefix(h,d)); compatible_prefix(h,d,b[sent].nodes[m.source].log);
            merge_retains(b[time].nodes[j].log,m,b[sent].nodes[m.source].log,h);
        }
    }
    local_prefix(b[time],c,a,j,h);
}
pub proof fn interval(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,lo: int,hi: int,j: int,at: int,i: int,length: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),
        0 <= lo <= hi <= horizon,0 <= at < horizon,decision(b,c,at,i),c.servers.contains(j),
        b[at].nodes[i].term <= b[lo].nodes[j].term,b[hi].nodes[j].term < bound,0 <= length <= decided(b,at,i).len(),
        prefix(sub(decided(b,at,i),1,length),b[lo].nodes[j].log)
    ensures prefix(sub(decided(b,at,i),1,length),b[hi].nodes[j].log)
    decreases hi-lo
{
    if lo < hi {
        let p=hi-1; history::term_role_interval(b,c,j,lo,p); history::term_role_interval(b,c,j,p,hi);
        interval(b,c,horizon,bound,lo,p,j,at,i,length); preserve(b,c,horizon,bound,p,j,at,i,length);
    }
}
} // verus!
