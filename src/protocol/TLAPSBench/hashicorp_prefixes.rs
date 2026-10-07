//! Log matching below a term bound, conditional on unique leaders below it.
//! This is a component of term induction, not a completed benchmark theorem.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_order as order;
use super::hashicorp_history::{self as history,step};
use super::temporal::Behavior;
verus! {
pub open spec fn unique_below(b: Behavior<LState>,c: Constants,horizon: int,bound: nat) -> bool {
    forall |left: int,right: int,i: int,j: int| 0 <= left <= horizon && 0 <= right <= horizon
        && c.servers.contains(i) && c.servers.contains(j)
        && (#[trigger] b[left].nodes[i]).role == Role::Leader && (#[trigger] b[right].nodes[j]).role == Role::Leader
        && b[left].nodes[i].term == b[right].nodes[j].term && b[left].nodes[i].term < bound ==> i == j
}
pub proof fn same_creation(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,left: int,right: int,i: int,j: int,k: int,e: Entry,f: Entry)
    requires configs::safety_spec(b,c),unique_below(b,c,horizon,bound),0 <= left < horizon,0 <= right < horizon,
        history::created(b,c,left,i,k,e),history::created(b,c,right,j,k,f),e.term == f.term,e.term < bound
    ensures left == right,i == j,e == f
{
    assert(i == j); history::step_valid(b,c,left); history::step_valid(b,c,right);
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    if left < right {
        assert(b[left+1].nodes[i].role == Role::Leader && b[left+1].nodes[i].term == e.term);
        history::continuous(b,c,i,left+1,right); assert(false);
    }
    if right < left {
        assert(b[right+1].nodes[i].role == Role::Leader && b[right+1].nodes[i].term == e.term);
        history::continuous(b,c,i,right+1,left); assert(false);
    }
}
pub proof fn merge_cut(old: Seq<Entry>,prev: int,entries: Seq<Entry>) -> (cut: int)
    requires 0 <= prev <= old.len()
    ensures merge(old,prev,entries) == old || (
        prev <= cut <= old.len() && cut < prev+entries.len()
        && merge(old,prev,entries) == sub(old,1,cut)+sub(entries,cut-prev+1,entries.len() as int)
        && (cut == prev || old[cut-1].term == entries[cut-prev-1].term))
{
    types::first_mismatch(old,prev,entries,1); reveal(merge);
    let first=choose |j: int| 1 <= j <= entries.len()+1
        && (forall |q: int| 0 <= q < j-1 ==> prev+q < old.len() && old[prev+q].term == (#[trigger] entries[q]).term)
        && (j == entries.len()+1 || prev+j > old.len() || old[prev+j-1].term != (#[trigger] entries[j-1]).term);
    if first > 1 && first <= entries.len() { assert(prev+first-2 < old.len() && old[prev+first-2].term == entries[first-2].term); }
    prev+first-1
}
pub proof fn prefix_origin(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,i: int,k: int) -> (origin: (int,int))
    requires configs::safety_spec(b,c),unique_below(b,c,horizon,bound),0 <= time <= horizon,c.servers.contains(i),
        0 <= k < b[time].nodes[i].log.len(),b[time].nodes[i].log[k].term < bound
    ensures 0 <= origin.0 < time,history::created(b,c,origin.0,origin.1,k,b[time].nodes[i].log[k]),
        sub(b[time].nodes[i].log,1,k+1) == b[origin.0+1].nodes[origin.1].log
    decreases time
{
    if time == 0 { assert(false); (0,i) }
    else {
        let p=time-1; history::step_valid(b,c,p); let a=step(b,c,p); let s=b[p]; let u=b[time];
        let old=s.nodes[i].log; let h=u.nodes[i].log;
        if h == old { prefix_origin(b,c,horizon,bound,p,i,k) }
        else {
            reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
            if history::creates(a,i) {
                if k == old.len() {
                    assert(history::created(b,c,p,i,k,h[k])); assert(sub(h,1,k+1) =~= h); (p,i)
                } else {
                    assert(0 <= k < old.len() && h[k] == old[k]); assert(sub(h,1,k+1) =~= sub(old,1,k+1));
                    prefix_origin(b,c,horizon,bound,p,i,k)
                }
            } else {
                assert(a is Receive); let m=a->Receive_m; let how=a->Receive_how;
                assert(m.dest == i && how == Receive::AcceptAppend && m.body is AppendRequest);
                let sent=history::request_origin(b,c,p,m); let source=b[sent].nodes[m.source].log;
                let prev=m.body->AppendRequest_prev; let entries=m.body->AppendRequest_entries;
                assert(0 <= prev <= old.len()); let cut=merge_cut(old,prev,entries);
                assert(h == sub(old,1,cut)+sub(entries,cut-prev+1,entries.len() as int));
                if k < cut {
                    assert(sub(h,1,k+1) =~= sub(old,1,k+1)); prefix_origin(b,c,horizon,bound,p,i,k)
                } else {
                    assert(prev <= k < source.len() && h[k] == source[k]);
                    if cut > 0 {
                        assert(0 <= cut-1 < old.len() && cut-1 < source.len());
                        if cut == prev { assert(old[cut-1].term == source[cut-1].term); }
                        else { assert(entries[cut-prev-1] == source[cut-1]); }
                        let g=order::safety_at(b,c,sent); assert(order::node(g.state.nodes[m.source]));
                        assert(source[cut-1].term <= source[k].term);
                        let left=prefix_origin(b,c,horizon,bound,p,i,cut-1);
                        let right=prefix_origin(b,c,horizon,bound,sent,m.source,cut-1);
                        same_creation(b,c,horizon,bound,left.0,right.0,left.1,right.1,cut-1,old[cut-1],source[cut-1]);
                        assert(sub(old,1,cut) == sub(source,1,cut));
                    }
                    assert(sub(h,1,k+1) =~= sub(source,1,k+1)) by {
                        assert forall |q: int| 0 <= q <= k implies (#[trigger] sub(h,1,k+1)[q]) == sub(source,1,k+1)[q] by {
                            if q < cut { assert(sub(old,1,cut)[q] == sub(source,1,cut)[q]); }
                        }
                    }
                    prefix_origin(b,c,horizon,bound,sent,m.source,k)
                }
            }
        }
    }
}
pub proof fn log_matching_below(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,left: int,right: int,i: int,j: int,k: int)
    requires configs::safety_spec(b,c),unique_below(b,c,horizon,bound),0 <= left <= horizon,0 <= right <= horizon,
        c.servers.contains(i),c.servers.contains(j),0 <= k < b[left].nodes[i].log.len(),k < b[right].nodes[j].log.len(),
        b[left].nodes[i].log[k].term == b[right].nodes[j].log[k].term,b[left].nodes[i].log[k].term < bound
    ensures sub(b[left].nodes[i].log,1,k+1) == sub(b[right].nodes[j].log,1,k+1)
{
    let a=prefix_origin(b,c,horizon,bound,left,i,k); let d=prefix_origin(b,c,horizon,bound,right,j,k);
    same_creation(b,c,horizon,bound,a.0,d.0,a.1,d.1,k,b[left].nodes[i].log[k],b[right].nodes[j].log[k]);
}
} // verus!
