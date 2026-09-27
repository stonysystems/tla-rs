//! Constructive examples: the protocol premises admit nonempty executions.
use vstd::prelude::*;
use super::{ConsensusSafety, Om, Gaios, Corfu, ReplicatedCommit, SpecPaxos};
verus! {
pub open spec fn one_config() -> ConsensusSafety::paxos::Config {
    ConsensusSafety::paxos::Config {acceptors:set![0int],quorums:set![set![0int]]}
}
pub open spec fn initial_paxos() -> ConsensusSafety::paxos::State {
    ConsensusSafety::paxos::State {promise:Map::empty().insert(0int,0int),
        last_ballot:Map::empty().insert(0int,-1int),last_value:Map::empty().insert(0int,0int),
        proposals:Map::empty(),votes:Set::empty()}
}
pub proof fn om_nonempty_decision(v:int)
    ensures exists|h:Om::consensus::History,c:Om::consensus::Config|
        Om::consensus::config_ok(c) && Om::consensus::defined_execution(h,c) && Om::consensus::decision(h,0,0,v),
{
    let c=Om::consensus::Config {processes:set![0int],witnesses:set![0int],quorums:set![set![0int]]};
    let p=(0int,0int,0int);let ck=(1int,0int,0int);
    let h=Om::consensus::History {
        inputs:Map::empty().insert(0int,v),values:Map::empty().insert(p,v).insert(ck,1int),
        starts:Map::empty().insert(p,0int).insert(ck,3int),
        processed:Map::empty().insert((0int,p),1int).insert((0int,ck),4int),
        quorums:Map::empty().insert(p,set![0int]).insert(ck,set![0int]),
        finishes:Map::empty().insert(p,2int).insert(ck,5int),
    };
    assert forall|q:Set<int>,r:Set<int>| c.quorums.contains(q) && c.quorums.contains(r)
        implies exists|w:int| q.contains(w) && r.contains(w) by {
        assert(q.contains(0) && r.contains(0));
    }
    assert(c.processes.contains(0)); assert(c.processes != Set::<int>::empty());
    assert forall|q:Set<int>| c.quorums.contains(q) implies q.subset_of(c.witnesses) && q != Set::<int>::empty() by {
        assert(q =~= set![0int]); assert(q.contains(0));
        assert(q.subset_of(c.witnesses));
    }
    assert(Om::consensus::config_ok(c));
    assert forall|q:int| Om::consensus::sees(h,p,q) implies q==0 by {
        let w=choose|w:int| h.quorums[p].contains(w)
            && h.processed.dom().contains((w,(0int,0int,q)))
            && h.processed[(w,(0int,0int,q))] <= h.processed[(w,p)];
        assert(w==0);
    }
    assert(Om::consensus::uniform(h,0,0));
    assert(Om::consensus::defined_execution(h,c));
    assert(!Om::consensus::saw_disagree(h,0,0)) by {
        assert forall|q:int| Om::consensus::sees(h,ck,q) implies h.values[(1int,0int,q)]!=0 by {
            let w=choose|w:int| h.quorums[ck].contains(w)
                && h.processed.dom().contains((w,(1int,0int,q)))
                && h.processed[(w,(1int,0int,q))] <= h.processed[(w,ck)];
            assert(w==0 && q==0);
        }
    }
    assert(Om::consensus::decision(h,0,0,v));
}
pub proof fn gaios_nonempty_read()
    ensures exists|s:Gaios::reads::Protocol,c:Gaios::reads::Config|
        Gaios::reads::config_ok(c) && Gaios::reads::host_ok(s,c) && Gaios::reads::read_protocol(s,c)
        && s.history.writes.len()==1 && s.history.reads.dom().contains(9) && s.history.reads[9].result==7,
{
    let pc=one_config(); let a=initial_paxos();
    let b=ConsensusSafety::paxos::State {proposals:a.proposals.insert(0int,7int),..a};
    let d=ConsensusSafety::paxos::State {last_ballot:b.last_ballot.insert(0int,0int),
        last_value:b.last_value.insert(0int,7int),votes:set![(0int,0int,7int)],..b};
    let ss=seq![a,b,d];let aa=seq![ConsensusSafety::paxos::Action::Suggest {value:7},
        ConsensusSafety::paxos::Action::Accept {acceptor:0,ballot:0}];
    assert(a.promise =~= Map::new(pc.acceptors,|n:int|0int));
    assert(a.last_ballot =~= Map::new(pc.acceptors,|n:int|-1int));
    assert(a.last_value =~= Map::new(pc.acceptors,|n:int|0int));
    assert(ConsensusSafety::paxos::init(a,pc));
    assert forall|k:int| 0 <= k < aa.len() implies #[trigger] ConsensusSafety::paxos::next(ss[k],ss[k+1],pc,aa[k]) by {
        if k==0 { assert(ConsensusSafety::paxos::suggest(a,b,7)); }
        else {
            assert(d.promise =~= b.promise.insert(0int,0int));
            assert(d.votes =~= b.votes.insert((0int,0int,7int)));
            assert(ConsensusSafety::paxos::accept(b,d,pc,0,0));
        }
    }
    assert(ConsensusSafety::paxos::behavior(ss,aa,pc));
    assert(pc.quorums.contains(set![0int]));
    assert forall|n:int| set![0int].contains(n) implies ConsensusSafety::paxos::voted(d,n,0,7) by {};
    assert(ConsensusSafety::paxos::quorum_chosen(d,pc,0,7));
    let c=Gaios::reads::Config {paxos:pc,read_quorums:set![set![0int]]};
    let hist=ConsensusSafety::register_history::History {initial:0,
        writes:seq![ConsensusSafety::register_history::Write {value:7,call:0,commit:3,reply:Some(4)}],
        reads:Map::empty().insert(9int,ConsensusSafety::register_history::Read {call:5,execute:8,reply:9,cut:1,result:7})};
    let s=Gaios::reads::Protocol {history:hist,write_views:seq![0int],
        views:Map::empty().insert(0int,Gaios::reads::View {quorum:set![0int],recovered:0,elected:-1}),
        recognitions:Map::empty().insert((0int,0int),-1int),
        stamps:Map::empty().insert(9int,Gaios::reads::Stamp {view:0,at:6,known:1,cut:1,replies:Map::empty().insert(0int,7int)}),
        slot_states:Map::empty().insert(0int,ss),slot_actions:Map::empty().insert(0int,aa)};
    assert(Gaios::reads::config_ok(c)); assert(Gaios::reads::host_ok(s,c)); assert(Gaios::reads::read_protocol(s,c));
}
pub proof fn speculative_fast_then_reconciliation()
    ensures exists|s:SpecPaxos::reconciliation::History,c:SpecPaxos::reconciliation::Config|
        SpecPaxos::reconciliation::config_ok(c) && SpecPaxos::reconciliation::well_formed(s,c)
        && SpecPaxos::reconciliation::fast(s,c,0,seq![1int,2int])
        && SpecPaxos::reconciliation::slow(s,c,1,seq![1int,2int])
        && s.logs.dom().contains((0int,4int)) && s.logs[(0int,4int)]==seq![2int,1int],
{
    let c=SpecPaxos::reconciliation::Config {nodes:set![0int,1int,2int,3int,4int],f:2};
    let q=set![0int,1int,4int]; let log=seq![1int,2int];
    let r=SpecPaxos::reconciliation::Recovery {nodes:q,previous:Map::new(q,|a:int|0int),maximum:0,winner:log};
    let keys=set![(0int,0int),(0int,1int),(0int,2int),(0int,3int),(0int,4int),(1int,0int),(1int,1int),(1int,4int)];
    let s=SpecPaxos::reconciliation::History {initial:Map::empty().insert(0int,Seq::empty()).insert(1int,log),
        logs:Map::new(keys,|k:(int,int)| if k==(0int,4int) {seq![2int,1int]} else {log}),
        recoveries:Map::empty().insert(1int,r)};
    assert(SpecPaxos::reconciliation::highest(r) =~= q);
    assert(SpecPaxos::reconciliation::merge_support(s,r,log) =~= set![0int,1int]);
    assert(SpecPaxos::reconciliation::majority(s,r,log));
    assert forall|p:Seq<int>| #[trigger] SpecPaxos::reconciliation::majority(s,r,p) implies p.len() <= r.winner.len() by {
        let support=SpecPaxos::reconciliation::merge_support(s,r,p);
        assert(support.len()>0);vstd::set::lemma_set_choose_len(support);
        let a=support.choose(); assert(support.contains(a));
        assert(q.contains(a)); assert(s.logs[(0int,a)].len()==2);
        assert(SpecPaxos::reconciliation::prefix(p,s.logs[(0int,a)]));
    }
    assert(SpecPaxos::reconciliation::config_ok(c));
    assert(SpecPaxos::reconciliation::quorum(c,q));
    assert(r.previous.dom()==q);
    assert forall|n:int| q.contains(n) implies 0 <= r.previous[n] < 1
        && SpecPaxos::reconciliation::installed(s,r.previous[n],n) && r.previous[n] <= r.maximum by {};
    assert(q.contains(0) && r.previous[0]==r.maximum);
    assert forall|u:int,n:int| SpecPaxos::reconciliation::installed(s,u,n) && u < 1 && q.contains(n)
        implies u <= r.previous[n] by { assert(u==0); }
    assert(SpecPaxos::reconciliation::prefix(r.winner,s.initial[1]));
    assert(SpecPaxos::reconciliation::recovery_ok(s,c,1,r));
    assert(SpecPaxos::reconciliation::well_formed(s,c));
    assert(SpecPaxos::reconciliation::support(s,c,0,log) =~= set![0int,1int,2int,3int]);
    assert(SpecPaxos::reconciliation::installs(s,c,1) =~= q);
    assert(SpecPaxos::reconciliation::fast(s,c,0,log));
    assert(SpecPaxos::reconciliation::slow(s,c,1,log));
}
pub proof fn corfu_read_survives_migration()
    ensures exists|ss:Seq<Corfu::chain::State>,aa:Seq<Corfu::chain::Action>|
        Corfu::chain::behavior(ss,aa,seq![0int,1int]) && ss.len()==9
        && ss[4].returned.contains(7) && ss[8].returned.contains(7) && ss[8].epoch==1,
{
    let chain=seq![0int,1int];
    let s0=Corfu::chain::State {epoch:0,chain,cells:Map::new(chain.to_set(),|n:int|None),
        failed:Set::empty(),sealed:Set::empty(),origins:Set::empty(),returned:Set::empty()};
    let s1=Corfu::chain::State {origins:set![7int],..s0};
    let s2=Corfu::chain::State {cells:s1.cells.insert(0int,Some(7int)),..s1};
    let s3=Corfu::chain::State {cells:s2.cells.insert(1int,Some(7int)),..s2};
    let s4=Corfu::chain::State {returned:set![7int],..s3};
    let s5=Corfu::chain::State {failed:set![0int],..s4};
    let s6=Corfu::chain::State {sealed:set![1int],..s5};
    let s7=Corfu::chain::State {epoch:1,chain:seq![2int],cells:Map::new(seq![2int].to_set(),|n:int|Some(7int)),
        failed:Set::empty(),sealed:Set::empty(),..s6};
    let s8=s7;
    let ss=seq![s0,s1,s2,s3,s4,s5,s6,s7,s8];
    let aa=seq![Corfu::chain::Action::Issue {value:7},Corfu::chain::Action::Write {epoch:0,index:0,value:7},
        Corfu::chain::Action::Write {epoch:0,index:1,value:7},Corfu::chain::Action::Observe {epoch:0,value:7},
        Corfu::chain::Action::Crash {node:0},Corfu::chain::Action::Seal {node:1},
        Corfu::chain::Action::Migrate {chain:seq![2int],seed:Some(7int)},Corfu::chain::Action::Observe {epoch:1,value:7}];
    assert(chain.contains(0) && chain.contains(1));
    let new_chain=seq![2int];assert(new_chain[0]==2);assert(new_chain.contains(2));
    assert(Corfu::chain::init(s0,chain));
    assert forall|k:int| 0 <= k < aa.len() implies #[trigger] Corfu::chain::next(ss[k],ss[k+1],aa[k]) by {
        if k==0 {} else if k==1 {} else if k==2 {} else if k==3 {}
        else if k==4 {assert(Corfu::chain::live(s4,1));}
        else if k==5 {} else if k==6 {
            assert forall|n:int| Corfu::chain::live(s6,n) implies s6.sealed.contains(n) by {
                let j=choose|j:int| 0 <= j < s6.chain.len() && s6.chain[j]==n;
                assert(n==1);
            }
            assert(Corfu::chain::live(s6,1) && s6.cells[1]==Some(7int));
        } else {assert(s8.returned =~= s7.returned.insert(7));}
    }
    assert(Corfu::chain::behavior(ss,aa,chain));
}
pub proof fn replicated_commit_recovers_chosen_commit()
    ensures exists|ss:Seq<ReplicatedCommit::commit::State>,aa:Seq<ReplicatedCommit::commit::Action>,c:ReplicatedCommit::commit::Config|
        ConsensusSafety::paxos::config_ok(c.paxos) && ReplicatedCommit::commit::behavior(ss,aa,c)
        && ss.last().applied.contains((0int,0int,1int))
        && ConsensusSafety::paxos::quorum_chosen(ss.last().core,c.paxos,1,1),
{
    let pc=one_config();let c=ReplicatedCommit::commit::Config {paxos:pc,cohorts:set![0int]};
    assert(pc.acceptors.contains(0) && pc.acceptors!=Set::<int>::empty());
    assert(pc.quorums.contains(set![0int]) && pc.quorums!=Set::<Set<int>>::empty());
    assert forall|q:Set<int>| pc.quorums.contains(q) implies q.subset_of(pc.acceptors) && q!=Set::<int>::empty() by {assert(q.contains(0));}
    assert forall|q:Set<int>,r:Set<int>| pc.quorums.contains(q) && pc.quorums.contains(r)
        implies exists|a:int| q.contains(a) && r.contains(a) by {assert(q.contains(0) && r.contains(0));}
    assert(ConsensusSafety::paxos::config_ok(pc));
    let p0=initial_paxos();
    assert(p0.promise =~= Map::new(pc.acceptors,|n:int|0int));
    assert(p0.last_ballot =~= Map::new(pc.acceptors,|n:int|-1int));
    assert(p0.last_value =~= Map::new(pc.acceptors,|n:int|0int));
    assert(ConsensusSafety::paxos::init(p0,pc));
    let s0=ReplicatedCommit::commit::State {core:p0,prepared:Set::empty(),learned:Map::empty(),applied:Set::empty()};
    let s1=ReplicatedCommit::commit::State {core:ConsensusSafety::paxos::State {proposals:p0.proposals.insert(0int,1int),..p0},..s0};
    let s2=ReplicatedCommit::commit::State {prepared:set![(0int,0int)],..s1};
    let s3=ReplicatedCommit::commit::State {core:ConsensusSafety::paxos::State {last_ballot:s2.core.last_ballot.insert(0int,0int),
        last_value:s2.core.last_value.insert(0int,1int),votes:set![(0int,0int,1int)],..s2.core},..s2};
    let s4=ReplicatedCommit::commit::State {learned:Map::empty().insert(0int,1int),..s3};
    let s5=ReplicatedCommit::commit::State {applied:set![(0int,0int,1int)],..s4};
    let s6=ReplicatedCommit::commit::State {core:ConsensusSafety::paxos::State {promise:s5.core.promise.insert(0int,1int),
        proposals:s5.core.proposals.insert(1int,1int),..s5.core},..s5};
    let s7=ReplicatedCommit::commit::State {core:ConsensusSafety::paxos::State {last_ballot:s6.core.last_ballot.insert(0int,1int),
        votes:s6.core.votes.insert((0int,1int,1int)),..s6.core},..s6};
    let ss=seq![s0,s1,s2,s3,s4,s5,s6,s7];
    let aa=seq![ReplicatedCommit::commit::Action::InitialCommit,ReplicatedCommit::commit::Action::Prepare {dc:0,cohort:0},
        ReplicatedCommit::commit::Action::Accept {dc:0,ballot:0},ReplicatedCommit::commit::Action::Learn {dc:0,decision:1},
        ReplicatedCommit::commit::Action::Apply {dc:0,cohort:0},
        ReplicatedCommit::commit::Action::Recover {ballot:1,quorum:set![0int],maximum:0,decision:1},
        ReplicatedCommit::commit::Action::Accept {dc:0,ballot:1}];
    assert(ConsensusSafety::paxos::quorum_chosen(s3.core,pc,0,1));
    assert forall|k:int| 0 <= k < aa.len() implies #[trigger] ReplicatedCommit::commit::next(ss[k],ss[k+1],c,aa[k]) by {
        if k==0 {assert(ReplicatedCommit::commit::next(s0,s1,c,aa[0]));}
        else if k==1 {assert(ReplicatedCommit::commit::next(s1,s2,c,aa[1]));}
        else if k==2 {
            assert(s3.core.promise =~= s2.core.promise.insert(0int,0int));
            assert(s3.core.votes =~= s2.core.votes.insert((0int,0int,1int)));
            assert(ReplicatedCommit::commit::next(s2,s3,c,aa[2]));
        } else if k==3 {assert(ReplicatedCommit::commit::next(s3,s4,c,aa[3]));}
        else if k==4 {assert(ReplicatedCommit::commit::next(s4,s5,c,aa[4]));}
        else if k==5 {
            assert(s5.core.last_ballot[0]==0 && s5.core.last_value[0]==1);
            assert(s6.core.promise =~= ConsensusSafety::paxos::prepared_promises(s5.core,set![0int],1));
            assert(set![0int].contains(0));
            assert(exists|dc:int| set![0int].contains(dc) && s5.core.last_ballot[dc]==0 && s5.core.last_value[dc]==1);
            assert(ReplicatedCommit::commit::next(s5,s6,c,aa[5]));
        } else {
            assert(s7.core.promise =~= s6.core.promise.insert(0int,1int));
            assert(s7.core.last_value =~= s6.core.last_value.insert(0int,1int));
            assert(ReplicatedCommit::commit::next(s6,s7,c,aa[6]));
        }
    }
    assert(ReplicatedCommit::commit::behavior(ss,aa,c));
    assert(ConsensusSafety::paxos::quorum_chosen(s7.core,pc,1,1));
}
} // verus!
