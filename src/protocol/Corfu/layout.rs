//! Competing projection proposals are resolved by the Paxos layout service.
//! Logical migration uses its chosen projection; physical copying remains the
//! atomic migration abstraction stated in chain.rs.
use vstd::prelude::*;
use super::chain as d;
use super::super::ConsensusSafety::paxos as p;
verus! {
pub open spec fn install(s:d::State,t:d::State,consensus:p::State,c:p::Config,
    layouts:Map<int,Seq<int>>,id:int,seed:Option<int>) -> bool {
    layouts.dom().contains(id) && p::learned(consensus,c,id) && d::migrate(s,t,layouts[id],seed)
}
pub proof fn agreed_projection_migration(ss:Seq<p::State>,aa:Seq<p::Action>,c:p::Config,
    layouts:Map<int,Seq<int>>,k:int,j:int,id:int,other:int,
    s:d::State,t:d::State,seed:Option<int>)
    requires p::config_ok(c),p::behavior(ss,aa,c),0 <= k <= j < ss.len(),
        d::inv(s),install(s,t,ss[k],c,layouts,id,seed),
        layouts.dom().contains(other),p::learned(ss[j],c,other),
    ensures d::inv(t),id==other,t.chain==layouts[other],
        d::abstract_cell(s) is Some ==> d::abstract_cell(t)==d::abstract_cell(s),
{
    p::behavior_agreement(ss,aa,c,k,j,id,other);
    d::single_assignment_refinement(s,t,d::Action::Migrate {chain:layouts[id],seed});
}
} // verus!
