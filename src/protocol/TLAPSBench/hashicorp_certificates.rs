//! Each recorded election has released votes from its actual log configuration.
use vstd::prelude::*;
use super::hashicorp::*;
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_votes::{self as votes,ProofState,Ballot};
use super::temporal::Behavior;
verus! {
pub open spec fn configuration(e: Event,c: Constants) -> Set<int> { config_at(e.entries,last_config(e.entries),c) }
pub open spec fn voters(g: ProofState,c: Constants,e: Event) -> Set<int> {
    c.servers.filter(|i: int| g.votes.contains(Ballot { voter: i,candidate: e.server,term: e.term }))
}
pub open spec fn certificate(g: ProofState,c: Constants,e: Event) -> bool {
    c.servers.contains(e.server) && e.term > 0 && types::log(e.entries,c)
    && !configuration(e,c).is_empty() && configuration(e,c).subset_of(c.servers)
    && quorum(voters(g,c,e).intersect(configuration(e,c)),configuration(e,c))
}
pub open spec fn inductive(g: ProofState,c: Constants) -> bool {
    votes::inductive(g,c) && forall |e: Event| g.state.elections.contains(e) ==> #[trigger] certificate(g,c,e)
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(votes::initial_proof(c),c)
{ votes::initial_inductive(c); }
pub proof fn certificate_monotone(g: ProofState,u: ProofState,c: Constants,e: Event)
    requires certificate(g,c,e),g.votes.subset_of(u.votes)
    ensures certificate(u,c,e)
{
    let a=voters(g,c,e).intersect(configuration(e,c)); let b=voters(u,c,e).intersect(configuration(e,c));
    assert(a.subset_of(b)); vstd::set_lib::lemma_len_subset(a,b);
}
pub proof fn new_certificate(g: ProofState,c: Constants,a: Action,e: Event)
    requires votes::inductive(g,c),enabled(g.state,c,a),!g.state.elections.contains(e),votes::advance(g,c,a).state.elections.contains(e)
    ensures certificate(votes::advance(g,c,a),c,e)
{
    let s=g.state; let u=votes::advance(g,c,a); let v=u.state;
    broadcast use Set::lemma_map_contains;
    let elected=c.servers.filter(|i: int| s.nodes[i].role != Role::Leader && v.nodes[i].role == Role::Leader);
    assert(elected.map(|i: int| Event { server: i,term: v.nodes[i].term,entries: v.nodes[i].log }).contains(e));
    assert(elected.contains(e.server)); assert(e == (Event { server: e.server,term: v.nodes[e.server].term,entries: v.nodes[e.server].log }));
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    let i=e.server; assert(a == Action::BecomeLeader(i)); let n=s.nodes[i];
    assert(types::node(n,c)); assert(votes::node(n,i)); assert(votes::granted(g,i));
    let q=n.granted.intersect(n.latest_config); let selected=voters(u,c,e).intersect(configuration(e,c));
    assert(configuration(e,c) == n.latest_config);
    assert(q.subset_of(selected)) by {
        assert forall |j: int| q.contains(j) implies selected.contains(j) by {
            assert(g.votes.contains(Ballot { voter: j,candidate: i,term: n.term }));
        }
    }
    vstd::set_lib::lemma_len_subset(q,selected);
}
pub proof fn preserve(g: ProofState,c: Constants,a: Action)
    requires inductive(g,c),enabled(g.state,c,a)
    ensures inductive(votes::advance(g,c,a),c)
{
    votes::preserve(g,c,a); let u=votes::advance(g,c,a);
    assert forall |e: Event| u.state.elections.contains(e) implies #[trigger] certificate(u,c,e) by {
        if g.state.elections.contains(e) { assert(certificate(g,c,e)); certificate_monotone(g,u,c,e); }
        else { new_certificate(g,c,a,e); }
    }
}
pub proof fn intersecting_certificates(g: ProofState,c: Constants,a: Event,b: Event,j: int)
    requires votes::inductive(g,c),a.term == b.term,voters(g,c,a).contains(j),voters(g,c,b).contains(j)
    ensures a.server == b.server
{
    let x=Ballot { voter: j,candidate: a.server,term: a.term }; let y=Ballot { voter: j,candidate: b.server,term: b.term };
    assert(g.votes.contains(x)); assert(g.votes.contains(y)); assert(votes::compatible(x,y));
}
pub proof fn adjacent_majorities(a: Set<int>,b: Set<int>,av: Set<int>,bv: Set<int>) -> (j: int)
    requires a.subset_of(av),b.subset_of(bv),quorum(a,av),quorum(b,bv),av.subset_of(bv),bv.len() <= av.len()+1
    ensures a.contains(j),b.contains(j)
{
    if a.disjoint(b) {
        vstd::set_lib::lemma_set_disjoint_lens(a,b); assert(a.union(b).subset_of(bv)); vstd::set_lib::lemma_len_subset(a.union(b),bv);
        assert(false);
    }
    choose |j: int| a.contains(j) && b.contains(j)
}
pub proof fn adjacent_configurations(g: ProofState,c: Constants,a: Event,b: Event)
    requires votes::inductive(g,c),certificate(g,c,a),certificate(g,c,b),a.term == b.term,
        configuration(a,c).subset_of(configuration(b,c)),configuration(b,c).len() <= configuration(a,c).len()+1
    ensures a.server == b.server
{
    let av=configuration(a,c); let bv=configuration(b,c);
    let j=adjacent_majorities(voters(g,c,a).intersect(av),voters(g,c,b).intersect(bv),av,bv);
    intersecting_certificates(g,c,a,b,j);
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,time: int) -> (g: ProofState)
    requires configs::safety_spec(b,c),time >= 0
    ensures g.state == b[time],inductive(g,c)
    decreases time
{
    if time == 0 { initial_inductive(c); votes::initial_proof(c) }
    else {
        let g=safety_at(b,c,time-1); let p=time-1; assert(next(b[p],b[p+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[p],c,a) && b[time] == apply(b[p],c,a);
        preserve(g,c,a); votes::advance(g,c,a)
    }
}
} // verus!
