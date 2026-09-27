//! Replicated Commit Algorithm 1: one transaction with a unique initial client.
//! A datacenter votes Commit only after every local cohort durably prepares.
//! Higher-ballot recovery is explicit classic Paxos: adopt the highest accepted
//! decision, or Abort if none exists. The paper does not specify this recovery
//! procedure in detail; it is a separately identified completion of its core.
use vstd::prelude::*;
use super::super::ConsensusSafety::paxos as p;
verus! {
pub struct Config { pub paxos: p::Config, pub cohorts: Set<int> }
pub struct State {
    pub core: p::State,
    pub prepared: Set<(int, int)>, // datacenter, cohort; durable history
    pub learned: Map<int, int>,
    pub applied: Set<(int, int, int)>, // datacenter, cohort, decision
}
pub open spec fn prepared_dc(s: State, c: Config, dc: int) -> bool {
    forall|shard: int| c.cohorts.contains(shard) ==> s.prepared.contains((dc, shard))
}
pub open spec fn inv(s: State, c: Config) -> bool {
    &&& p::inv(s.core, c.paxos)
    &&& forall|b: int| s.core.proposals.dom().contains(b) ==> s.core.proposals[b] == 0 || s.core.proposals[b] == 1
    &&& forall|dc: int, b: int| p::voted(s.core, dc, b, 1) ==> prepared_dc(s, c, dc)
    &&& forall|dc: int| s.learned.dom().contains(dc) ==> c.paxos.acceptors.contains(dc)
        && p::learned(s.core, c.paxos, s.learned[dc])
    &&& forall|dc: int, sh: int, d: int| s.applied.contains((dc, sh, d)) ==> c.cohorts.contains(sh)
        && s.learned.dom().contains(dc) && s.learned[dc] == d
        && (d == 1 ==> s.prepared.contains((dc, sh)))
}
pub open spec fn init(s: State, c: Config) -> bool {
    p::init(s.core, c.paxos) && s.prepared == Set::<(int,int)>::empty()
        && s.learned == Map::<int,int>::empty() && s.applied == Set::<(int,int,int)>::empty()
}
pub enum Action {
    Prepare { dc: int, cohort: int }, InitialCommit,
    Recover { ballot: int, quorum: Set<int>, maximum: int, decision: int },
    Accept { dc: int, ballot: int }, Learn { dc: int, decision: int },
    Apply { dc: int, cohort: int }, Stutter,
}
pub open spec fn core_step(s: State, t: State, c: Config, a: p::Action) -> bool {
    p::next(s.core, t.core, c.paxos, a) && t == State { core: t.core, ..s }
}
pub open spec fn next(s: State, t: State, c: Config, a: Action) -> bool {
    match a {
        Action::Prepare { dc, cohort } => c.paxos.acceptors.contains(dc) && c.cohorts.contains(cohort)
            && t == State { prepared: s.prepared.insert((dc, cohort)), ..s },
        Action::InitialCommit => core_step(s, t, c, p::Action::Suggest { value: 1 }),
        Action::Recover { ballot, quorum, maximum, decision } =>
            (maximum == -1 ==> decision == 0)
            && core_step(s, t, c, p::Action::Revoke { ballot, quorum, maximum, value: decision }),
        Action::Accept { dc, ballot } => (s.core.proposals[ballot] == 1 ==> prepared_dc(s, c, dc))
            && core_step(s, t, c, p::Action::Accept { acceptor: dc, ballot }),
        Action::Learn { dc, decision } => c.paxos.acceptors.contains(dc) && p::learned(s.core, c.paxos, decision)
            && t == State { learned: s.learned.insert(dc, decision), ..s },
        Action::Apply { dc, cohort } => s.learned.dom().contains(dc) && c.cohorts.contains(cohort)
            && (s.learned[dc] == 1 ==> s.prepared.contains((dc, cohort)))
            && t == State { applied: s.applied.insert((dc, cohort, s.learned[dc])), ..s },
        Action::Stutter => t == s,
    }
}
pub proof fn init_inv(s: State, c: Config)
    requires init(s, c), ensures inv(s, c),
{ p::init_inv(s.core, c.paxos); }
pub proof fn core_preserves_learned(s: State, t: State, c: Config, a: p::Action)
    requires p::config_ok(c.paxos), inv(s,c), core_step(s,t,c,a),
    ensures p::inv(t.core,c.paxos),
        forall|dc:int| s.learned.dom().contains(dc) ==> p::learned(t.core,c.paxos,s.learned[dc]),
{
    p::step_preserves(s.core,t.core,c.paxos,a);
    assert forall|dc:int| s.learned.dom().contains(dc) implies p::learned(t.core,c.paxos,s.learned[dc]) by {
        p::learned_preserved(s.core,t.core,c.paxos,s.learned[dc]);
    }
}
pub proof fn step_preserves(s: State, t: State, c: Config, a: Action)
    requires p::config_ok(c.paxos), inv(s,c), next(s,t,c,a),
    ensures inv(t,c), s.applied.subset_of(t.applied),
        forall|d:int| p::learned(s.core,c.paxos,d) ==> p::learned(t.core,c.paxos,d),
{
    match a {
        Action::InitialCommit => core_preserves_learned(s,t,c,p::Action::Suggest {value:1}),
        Action::Recover {ballot,quorum,maximum,decision} => {
            core_preserves_learned(s,t,c,p::Action::Revoke {ballot,quorum,maximum,value:decision});
            assert(quorum.subset_of(c.paxos.acceptors));
            if maximum >= 0 {
                let dc = choose|dc:int| quorum.contains(dc) && s.core.last_ballot[dc] == maximum
                    && s.core.last_value[dc] == decision;
                assert(c.paxos.acceptors.contains(dc));
                assert(p::voted(s.core,dc,maximum,decision));
                assert(s.core.proposals[maximum] == decision);
            }
        },
        Action::Accept {dc,ballot} => core_preserves_learned(s,t,c,p::Action::Accept {acceptor:dc,ballot}),
        Action::Learn {dc,decision} => {
            if s.learned.dom().contains(dc) { p::learned_agreement(s.core,c.paxos,s.learned[dc],decision); }
        },
        _ => {},
    }
    assert forall|dc:int,b:int| p::voted(t.core,dc,b,1) implies prepared_dc(t,c,dc) by {
        if p::voted(s.core,dc,b,1) { assert(prepared_dc(s,c,dc)); }
        else {
            match a {
                Action::Accept {dc: voter,ballot} => {
                    assert(dc == voter && b == ballot && s.core.proposals[ballot] == 1);
                    assert(prepared_dc(s,c,dc));
                },
                _ => { assert(false); },
            }
        }
    }
    assert forall|d:int| p::learned(s.core,c.paxos,d) implies p::learned(t.core,c.paxos,d) by {
        p::learned_preserved(s.core,t.core,c.paxos,d);
    }
}
pub proof fn commit_requires_prepared_quorum(s: State, c: Config)
    requires p::config_ok(c.paxos), inv(s,c), p::learned(s.core,c.paxos,1),
    ensures exists|q:Set<int>| c.paxos.quorums.contains(q)
        && forall|dc:int| q.contains(dc) ==> prepared_dc(s,c,dc),
{
    let b = choose|b:int| p::quorum_chosen(s.core,c.paxos,b,1);
    let q = choose|q:Set<int>| c.paxos.quorums.contains(q)
        && forall|dc:int| q.contains(dc) ==> p::voted(s.core,dc,b,1);
    assert forall|dc:int| q.contains(dc) implies prepared_dc(s,c,dc) by { assert(p::voted(s.core,dc,b,1)); }
}
pub open spec fn behavior(ss:Seq<State>, aa:Seq<Action>, c:Config) -> bool {
    ss.len() == aa.len()+1 && init(ss[0],c)
        && forall|i:int| 0 <= i < aa.len() ==> #[trigger] next(ss[i],ss[i+1],c,aa[i])
}
pub proof fn reachable_inv(ss:Seq<State>, aa:Seq<Action>, c:Config,k:int)
    requires p::config_ok(c.paxos),behavior(ss,aa,c),0 <= k < ss.len(), ensures inv(ss[k],c),
    decreases k,
{
    if k == 0 { init_inv(ss[0],c); }
    else {
        reachable_inv(ss,aa,c,k-1);
        assert(next(ss[k-1],ss[(k-1)+1],c,aa[k-1]));
        step_preserves(ss[k-1],ss[k],c,aa[k-1]);
    }
}
pub proof fn decision_persists(ss:Seq<State>,aa:Seq<Action>,c:Config,i:int,j:int,d:int)
    requires p::config_ok(c.paxos),behavior(ss,aa,c),0 <= i <= j < ss.len(),p::learned(ss[i].core,c.paxos,d),
    ensures p::learned(ss[j].core,c.paxos,d), decreases j-i,
{
    if i < j {
        decision_persists(ss,aa,c,i,j-1,d); reachable_inv(ss,aa,c,j-1);
        assert(next(ss[j-1],ss[(j-1)+1],c,aa[j-1]));
        step_preserves(ss[j-1],ss[j],c,aa[j-1]);
    }
}
pub proof fn atomic_commit_agreement(ss:Seq<State>,aa:Seq<Action>,c:Config,i:int,j:int,
    dc:int,sh:int,d:int,other:int,other_sh:int,e:int)
    requires p::config_ok(c.paxos),behavior(ss,aa,c),0 <= i <= j < ss.len(),
        ss[i].applied.contains((dc,sh,d)),ss[j].applied.contains((other,other_sh,e)),
    ensures d == e, d == 0 || d == 1,
        d == 1 ==> exists|q:Set<int>| c.paxos.quorums.contains(q)
            && forall|a:int| q.contains(a) ==> prepared_dc(ss[j],c,a),
{
    reachable_inv(ss,aa,c,i); reachable_inv(ss,aa,c,j);
    assert(p::learned(ss[i].core,c.paxos,d));
    assert(p::learned(ss[j].core,c.paxos,e));
    decision_persists(ss,aa,c,i,j,d);
    p::learned_agreement(ss[j].core,c.paxos,d,e);
    let b = choose|b:int| p::quorum_chosen(ss[j].core,c.paxos,b,d);
    let q = choose|q:Set<int>| c.paxos.quorums.contains(q)
        && forall|a:int| q.contains(a) ==> p::voted(ss[j].core,a,b,d);
    let a = choose|a:int| q.contains(a);
    assert(p::voted(ss[j].core,a,b,d)); assert(ss[j].core.proposals[b] == d);
    if d == 1 { commit_requires_prepared_quorum(ss[j],c); }
}
pub open spec fn abstract_decision(s:State,c:Config) -> Option<int> {
    if exists|d:int| p::learned(s.core,c.paxos,d) {
        Some(choose|d:int| p::learned(s.core,c.paxos,d))
    } else { None }
}
// A single-assignment atomic decision is the abstract specification. Prepare
// and voting steps may stutter; the first quorum decision publishes the value.
pub proof fn atomic_decision_refinement(s:State,t:State,c:Config,a:Action)
    requires p::config_ok(c.paxos),inv(s,c),next(s,t,c,a),
    ensures inv(t,c), abstract_decision(s,c) is Some ==> abstract_decision(t,c)==abstract_decision(s,c),
        forall|dc:int| t.learned.dom().contains(dc) ==> abstract_decision(t,c)==Some(t.learned[dc]),
{
    step_preserves(s,t,c,a);
    if abstract_decision(s,c) is Some {
        let d=abstract_decision(s,c)->Some_0;
        assert(p::learned(s.core,c.paxos,d)); assert(p::learned(t.core,c.paxos,d));
        assert(abstract_decision(t,c) is Some);
        p::learned_agreement(t.core,c.paxos,d,abstract_decision(t,c)->Some_0);
    }
    assert forall|dc:int| t.learned.dom().contains(dc) implies abstract_decision(t,c)==Some(t.learned[dc]) by {
        assert(p::learned(t.core,c.paxos,t.learned[dc]));
        assert(abstract_decision(t,c) is Some);
        p::learned_agreement(t.core,c.paxos,t.learned[dc],abstract_decision(t,c)->Some_0);
    }
}
} // verus!
