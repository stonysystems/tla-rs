//! Recover the concrete one-member change behind every configuration entry.
//! The prefix correspondence is conditional on earlier-term leader uniqueness.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_history::{self as history,step};
use super::hashicorp_prefixes as prefixes;
use super::hashicorp_certificates as certificates;
use super::temporal::Behavior;
verus! {
pub open spec fn parent(h: Seq<Entry>,k: int,c: Constants) -> Set<int> {
    let before=sub(h,1,k); config_at(before,last_config(before),c)
}
pub open spec fn toggle(voters: Set<int>,member: int) -> Set<int> {
    if voters.contains(member) { voters.remove(member) } else { voters.insert(member) }
}
pub open spec fn adjacent(a: Set<int>,b: Set<int>) -> bool {
    a.subset_of(b) && b.len() <= a.len()+1 || b.subset_of(a) && a.len() <= b.len()+1
}
pub proof fn toggle_adjacent(a: Set<int>,i: int)
    ensures adjacent(a,toggle(a,i))
{
    if a.contains(i) { vstd::set::lemma_set_remove_len(a,i); }
    else { vstd::set::lemma_set_insert_len(a,i); }
}
pub struct Edge { pub at: int,pub server: int,pub member: int }
pub proof fn configuration_origin(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,i: int,k: int) -> (edge: Edge)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),0 <= time <= horizon,c.servers.contains(i),
        0 <= k < b[time].nodes[i].log.len(),b[time].nodes[i].log[k].kind == EntryKind::Config,b[time].nodes[i].log[k].term < bound
    ensures 0 <= edge.at < time,c.servers.contains(edge.server),c.servers.contains(edge.member),
        step(b,c,edge.at) == (Action::ProposeConfig { i: edge.server,member: edge.member }),
        b[edge.at].nodes[edge.server].log == sub(b[time].nodes[i].log,1,k),
        b[edge.at].nodes[edge.server].role == Role::Leader,b[edge.at].nodes[edge.server].term == b[time].nodes[i].log[k].term,
        b[edge.at].nodes[edge.server].latest_config == parent(b[time].nodes[i].log,k,c),
        b[time].nodes[i].log[k].config == toggle(parent(b[time].nodes[i].log,k,c),edge.member),
        b[edge.at].nodes[edge.server].committed_config_index == b[edge.at].nodes[edge.server].latest_config_index,
        b[edge.at].nodes[edge.server].commit > 0,
        b[edge.at].nodes[edge.server].log[b[edge.at].nodes[edge.server].commit-1].term == b[time].nodes[i].log[k].term
{
    let origin=prefixes::prefix_origin(b,c,horizon,bound,time,i,k); let at=origin.0; let writer=origin.1;
    history::step_valid(b,c,at); let a=step(b,c,at); let h=b[time].nodes[i].log;
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    assert(a is ProposeConfig); assert(a->ProposeConfig_i == writer);
    assert(sub(h,1,k) =~= b[at].nodes[writer].log) by {
        assert forall |q: int| 0 <= q < k implies (#[trigger] sub(h,1,k)[q]) == b[at].nodes[writer].log[q] by {
            assert(sub(h,1,k+1)[q] == b[at+1].nodes[writer].log[q]);
        }
    }
    types::safety_at(b,c,at); assert(types::node(b[at].nodes[writer],c));
    Edge { at,server: writer,member: a->ProposeConfig_member }
}
pub proof fn adjacent_entry(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,i: int,k: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),0 <= time <= horizon,c.servers.contains(i),
        0 <= k < b[time].nodes[i].log.len(),b[time].nodes[i].log[k].kind == EntryKind::Config,b[time].nodes[i].log[k].term < bound
    ensures adjacent(parent(b[time].nodes[i].log,k,c),b[time].nodes[i].log[k].config),
        parent(b[time].nodes[i].log,k,c) != b[time].nodes[i].log[k].config
{
    let edge=configuration_origin(b,c,horizon,bound,time,i,k); toggle_adjacent(parent(b[time].nodes[i].log,k,c),edge.member);
    let old=parent(b[time].nodes[i].log,k,c); let new=b[time].nodes[i].log[k].config;
    assert(old.contains(edge.member) != new.contains(edge.member));
}
pub proof fn adjacent_quorums(a: Set<int>,b: Set<int>,av: Set<int>,bv: Set<int>) -> (i: int)
    requires a.subset_of(av),b.subset_of(bv),quorum(a,av),quorum(b,bv),adjacent(av,bv)
    ensures a.contains(i),b.contains(i)
{
    if av.subset_of(bv) && bv.len() <= av.len()+1 { certificates::adjacent_majorities(a,b,av,bv) }
    else { certificates::adjacent_majorities(b,a,bv,av) }
}
} // verus!
