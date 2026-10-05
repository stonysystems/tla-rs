//! Fixed 47-transition counterexample certificate. Every edge is checked by Verus.
//! Reproduce with scripts/build_tlaps_bench_etcd_counterexample.py.
use vstd::prelude::*;
use vstd::multiset::Multiset;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::temporal::Behavior;
verus! {
pub open spec fn constants() -> Constants { Constants { servers: set![1int,2int,3int].to_iset(),voters: set![1int,2int,3int] } }
pub open spec fn node(t: nat,r: Role,v: Option<int>,h: Seq<nat>,k: nat,responded: Set<int>,granted: Set<int>,matched: Seq<nat>,dt: nat,dv: Option<int>,dh: Seq<nat>,dk: nat) -> LServer {
    LServer { term: t,role: r,voted_for: v,log: h,commit: k,responded,granted,
        matched: IMap::empty().insert(1,matched[0]).insert(2,matched[1]).insert(3,matched[2]),
        disk: Disk { term: dt,voted_for: dv,log: dh,commit: dk } }
}
#[verifier::opaque]
pub open spec fn state(k: int) -> LState { match k {
    _ if k == 0 => LState { nodes: IMap::empty().insert(1,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(2,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![] },
    _ if k == 1 => LState { nodes: IMap::empty().insert(1,node(1,Role::Candidate,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(2,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![] },
    _ if k == 2 => LState { nodes: IMap::empty().insert(1,node(1,Role::Candidate,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(2,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)),
        pending: Multiset::empty().insert(Message { source: 1,dest: 1,term: 1,body: Body::VoteResponse { granted: true } }),
        messages: Multiset::empty(),votes: set![] },
    _ if k == 3 => LState { nodes: IMap::empty().insert(1,node(1,Role::Candidate,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(2,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)),
        pending: Multiset::empty().insert(Message { source: 1,dest: 1,term: 1,body: Body::VoteResponse { granted: true } }).insert(Message { source: 1,dest: 3,term: 1,body: Body::VoteRequest { last_term: 0,last_index: 0 } }),
        messages: Multiset::empty(),votes: set![] },
    _ if k == 4 => LState { nodes: IMap::empty().insert(1,node(1,Role::Candidate,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![],0)).insert(2,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 1,dest: 1,term: 1,body: Body::VoteResponse { granted: true } }).insert(Message { source: 1,dest: 3,term: 1,body: Body::VoteRequest { last_term: 0,last_index: 0 } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 }] },
    _ if k == 5 => LState { nodes: IMap::empty().insert(1,node(1,Role::Candidate,Some(1),seq![],0,set![1int],set![1int],seq![0nat,0nat,0nat],1,Some(1),seq![],0)).insert(2,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 1,dest: 3,term: 1,body: Body::VoteRequest { last_term: 0,last_index: 0 } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 }] },
    _ if k == 6 => LState { nodes: IMap::empty().insert(1,node(1,Role::Candidate,Some(1),seq![],0,set![1int],set![1int],seq![0nat,0nat,0nat],1,Some(1),seq![],0)).insert(2,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(1,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 1,dest: 3,term: 1,body: Body::VoteRequest { last_term: 0,last_index: 0 } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 }] },
    _ if k == 7 => LState { nodes: IMap::empty().insert(1,node(1,Role::Candidate,Some(1),seq![],0,set![1int],set![1int],seq![0nat,0nat,0nat],1,Some(1),seq![],0)).insert(2,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(1,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)),
        pending: Multiset::empty().insert(Message { source: 3,dest: 1,term: 1,body: Body::VoteResponse { granted: true } }),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 }] },
    _ if k == 8 => LState { nodes: IMap::empty().insert(1,node(1,Role::Candidate,Some(1),seq![],0,set![1int],set![1int],seq![0nat,0nat,0nat],1,Some(1),seq![],0)).insert(2,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(1,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 3,dest: 1,term: 1,body: Body::VoteResponse { granted: true } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 3,term: 1,candidate: 1 }] },
    _ if k == 9 => LState { nodes: IMap::empty().insert(1,node(1,Role::Candidate,Some(1),seq![],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![],0)).insert(2,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(1,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 3,term: 1,candidate: 1 }] },
    _ if k == 10 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![],0)).insert(2,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(1,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 3,term: 1,candidate: 1 }] },
    _ if k == 11 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![],0)).insert(2,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(1,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 3,term: 1,candidate: 1 }] },
    _ if k == 12 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(0,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(1,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 3,term: 1,candidate: 1 }] },
    _ if k == 13 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(1,Role::Candidate,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(1,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 3,term: 1,candidate: 1 }] },
    _ if k == 14 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Candidate,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(1,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 3,term: 1,candidate: 1 }] },
    _ if k == 15 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Candidate,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(1,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![],0)),
        pending: Multiset::empty().insert(Message { source: 2,dest: 2,term: 2,body: Body::VoteResponse { granted: true } }),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 3,term: 1,candidate: 1 }] },
    _ if k == 16 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Candidate,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],0,None,seq![],0)).insert(3,node(1,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![],0)),
        pending: Multiset::empty().insert(Message { source: 2,dest: 2,term: 2,body: Body::VoteResponse { granted: true } }).insert(Message { source: 2,dest: 3,term: 2,body: Body::VoteRequest { last_term: 0,last_index: 0 } }),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 3,term: 1,candidate: 1 }] },
    _ if k == 17 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Candidate,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)).insert(3,node(1,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 2,dest: 2,term: 2,body: Body::VoteResponse { granted: true } }).insert(Message { source: 2,dest: 3,term: 2,body: Body::VoteRequest { last_term: 0,last_index: 0 } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 }] },
    _ if k == 18 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Candidate,Some(2),seq![],0,set![2int],set![2int],seq![0nat,0nat,0nat],2,Some(2),seq![],0)).insert(3,node(1,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 2,dest: 3,term: 2,body: Body::VoteRequest { last_term: 0,last_index: 0 } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 }] },
    _ if k == 19 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Candidate,Some(2),seq![],0,set![2int],set![2int],seq![0nat,0nat,0nat],2,Some(2),seq![],0)).insert(3,node(2,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 2,dest: 3,term: 2,body: Body::VoteRequest { last_term: 0,last_index: 0 } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 }] },
    _ if k == 20 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Candidate,Some(2),seq![],0,set![2int],set![2int],seq![0nat,0nat,0nat],2,Some(2),seq![],0)).insert(3,node(2,Role::Follower,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![],0)),
        pending: Multiset::empty().insert(Message { source: 3,dest: 2,term: 2,body: Body::VoteResponse { granted: true } }),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 }] },
    _ if k == 21 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Candidate,Some(2),seq![],0,set![2int],set![2int],seq![0nat,0nat,0nat],2,Some(2),seq![],0)).insert(3,node(2,Role::Follower,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 3,dest: 2,term: 2,body: Body::VoteResponse { granted: true } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 }] },
    _ if k == 22 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Candidate,Some(2),seq![],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![],0)).insert(3,node(2,Role::Follower,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 }] },
    _ if k == 23 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![],0)).insert(3,node(2,Role::Follower,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 }] },
    _ if k == 24 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![],0)).insert(3,node(2,Role::Follower,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 }] },
    _ if k == 25 => LState { nodes: IMap::empty().insert(1,node(1,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(2,Role::Follower,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 }] },
    _ if k == 26 => LState { nodes: IMap::empty().insert(1,node(1,Role::Follower,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(2,Role::Follower,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 }] },
    _ if k == 27 => LState { nodes: IMap::empty().insert(1,node(2,Role::Candidate,Some(1),seq![1nat],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(2,Role::Follower,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 }] },
    _ if k == 28 => LState { nodes: IMap::empty().insert(1,node(3,Role::Candidate,Some(1),seq![1nat],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(2,Role::Follower,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 }] },
    _ if k == 29 => LState { nodes: IMap::empty().insert(1,node(3,Role::Candidate,Some(1),seq![1nat],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(2,Role::Follower,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)),
        pending: Multiset::empty().insert(Message { source: 1,dest: 1,term: 3,body: Body::VoteResponse { granted: true } }),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 }] },
    _ if k == 30 => LState { nodes: IMap::empty().insert(1,node(3,Role::Candidate,Some(1),seq![1nat],0,set![],set![],seq![0nat,0nat,0nat],1,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(2,Role::Follower,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)),
        pending: Multiset::empty().insert(Message { source: 1,dest: 1,term: 3,body: Body::VoteResponse { granted: true } }).insert(Message { source: 1,dest: 3,term: 3,body: Body::VoteRequest { last_term: 1,last_index: 1 } }),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 }] },
    _ if k == 31 => LState { nodes: IMap::empty().insert(1,node(3,Role::Candidate,Some(1),seq![1nat],0,set![],set![],seq![0nat,0nat,0nat],3,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(2,Role::Follower,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 1,dest: 1,term: 3,body: Body::VoteResponse { granted: true } }).insert(Message { source: 1,dest: 3,term: 3,body: Body::VoteRequest { last_term: 1,last_index: 1 } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 }] },
    _ if k == 32 => LState { nodes: IMap::empty().insert(1,node(3,Role::Candidate,Some(1),seq![1nat],0,set![1int],set![1int],seq![0nat,0nat,0nat],3,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(2,Role::Follower,Some(2),seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 1,dest: 3,term: 3,body: Body::VoteRequest { last_term: 1,last_index: 1 } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 }] },
    _ if k == 33 => LState { nodes: IMap::empty().insert(1,node(3,Role::Candidate,Some(1),seq![1nat],0,set![1int],set![1int],seq![0nat,0nat,0nat],3,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,None,seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 1,dest: 3,term: 3,body: Body::VoteRequest { last_term: 1,last_index: 1 } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 }] },
    _ if k == 34 => LState { nodes: IMap::empty().insert(1,node(3,Role::Candidate,Some(1),seq![1nat],0,set![1int],set![1int],seq![0nat,0nat,0nat],3,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],2,Some(2),seq![],0)),
        pending: Multiset::empty().insert(Message { source: 3,dest: 1,term: 3,body: Body::VoteResponse { granted: true } }),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 }] },
    _ if k == 35 => LState { nodes: IMap::empty().insert(1,node(3,Role::Candidate,Some(1),seq![1nat],0,set![1int],set![1int],seq![0nat,0nat,0nat],3,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],3,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 3,dest: 1,term: 3,body: Body::VoteResponse { granted: true } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 },Ballot { voter: 3,term: 3,candidate: 1 }] },
    _ if k == 36 => LState { nodes: IMap::empty().insert(1,node(3,Role::Candidate,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![0nat,0nat,0nat],3,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],3,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 },Ballot { voter: 3,term: 3,candidate: 1 }] },
    _ if k == 37 => LState { nodes: IMap::empty().insert(1,node(3,Role::Leader,Some(1),seq![1nat],0,set![1int,3int],set![1int,3int],seq![1nat,0nat,0nat],3,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],3,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 },Ballot { voter: 3,term: 3,candidate: 1 }] },
    _ if k == 38 => LState { nodes: IMap::empty().insert(1,node(3,Role::Leader,Some(1),seq![1nat,3nat],0,set![1int,3int],set![1int,3int],seq![1nat,0nat,0nat],3,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],3,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 },Ballot { voter: 3,term: 3,candidate: 1 }] },
    _ if k == 39 => LState { nodes: IMap::empty().insert(1,node(3,Role::Leader,Some(1),seq![1nat,3nat],0,set![1int,3int],set![1int,3int],seq![1nat,0nat,0nat],3,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],3,Some(1),seq![],0)),
        pending: Multiset::empty().insert(Message { source: 1,dest: 1,term: 3,body: Body::AppendResponse { mode: Mode::App,success: true,matched: 2 } }),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 },Ballot { voter: 3,term: 3,candidate: 1 }] },
    _ if k == 40 => LState { nodes: IMap::empty().insert(1,node(3,Role::Leader,Some(1),seq![1nat,3nat],0,set![1int,3int],set![1int,3int],seq![1nat,0nat,0nat],3,Some(1),seq![1nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],3,Some(1),seq![],0)),
        pending: Multiset::empty().insert(Message { source: 1,dest: 1,term: 3,body: Body::AppendResponse { mode: Mode::App,success: true,matched: 2 } }).insert(Message { source: 1,dest: 3,term: 3,body: Body::AppendRequest { mode: Mode::App,prev: 0,prev_term: 0,entries: seq![1nat,3nat],commit: 0 } }),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 },Ballot { voter: 3,term: 3,candidate: 1 }] },
    _ if k == 41 => LState { nodes: IMap::empty().insert(1,node(3,Role::Leader,Some(1),seq![1nat,3nat],0,set![1int,3int],set![1int,3int],seq![1nat,0nat,0nat],3,Some(1),seq![1nat,3nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],3,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 1,dest: 1,term: 3,body: Body::AppendResponse { mode: Mode::App,success: true,matched: 2 } }).insert(Message { source: 1,dest: 3,term: 3,body: Body::AppendRequest { mode: Mode::App,prev: 0,prev_term: 0,entries: seq![1nat,3nat],commit: 0 } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 },Ballot { voter: 3,term: 3,candidate: 1 }] },
    _ if k == 42 => LState { nodes: IMap::empty().insert(1,node(3,Role::Leader,Some(1),seq![1nat,3nat],0,set![1int,3int],set![1int,3int],seq![2nat,0nat,0nat],3,Some(1),seq![1nat,3nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,Some(1),seq![],0,set![],set![],seq![0nat,0nat,0nat],3,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 1,dest: 3,term: 3,body: Body::AppendRequest { mode: Mode::App,prev: 0,prev_term: 0,entries: seq![1nat,3nat],commit: 0 } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 },Ballot { voter: 3,term: 3,candidate: 1 }] },
    _ if k == 43 => LState { nodes: IMap::empty().insert(1,node(3,Role::Leader,Some(1),seq![1nat,3nat],0,set![1int,3int],set![1int,3int],seq![2nat,0nat,0nat],3,Some(1),seq![1nat,3nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,Some(1),seq![1nat,3nat],0,set![],set![],seq![0nat,0nat,0nat],3,Some(1),seq![],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 1,dest: 3,term: 3,body: Body::AppendRequest { mode: Mode::App,prev: 0,prev_term: 0,entries: seq![1nat,3nat],commit: 0 } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 },Ballot { voter: 3,term: 3,candidate: 1 }] },
    _ if k == 44 => LState { nodes: IMap::empty().insert(1,node(3,Role::Leader,Some(1),seq![1nat,3nat],0,set![1int,3int],set![1int,3int],seq![2nat,0nat,0nat],3,Some(1),seq![1nat,3nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,Some(1),seq![1nat,3nat],0,set![],set![],seq![0nat,0nat,0nat],3,Some(1),seq![],0)),
        pending: Multiset::empty().insert(Message { source: 3,dest: 1,term: 3,body: Body::AppendResponse { mode: Mode::App,success: true,matched: 2 } }),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 },Ballot { voter: 3,term: 3,candidate: 1 }] },
    _ if k == 45 => LState { nodes: IMap::empty().insert(1,node(3,Role::Leader,Some(1),seq![1nat,3nat],0,set![1int,3int],set![1int,3int],seq![2nat,0nat,0nat],3,Some(1),seq![1nat,3nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,Some(1),seq![1nat,3nat],0,set![],set![],seq![0nat,0nat,0nat],3,Some(1),seq![1nat,3nat],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty().insert(Message { source: 3,dest: 1,term: 3,body: Body::AppendResponse { mode: Mode::App,success: true,matched: 2 } }),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 },Ballot { voter: 3,term: 3,candidate: 1 }] },
    _ if k == 46 => LState { nodes: IMap::empty().insert(1,node(3,Role::Leader,Some(1),seq![1nat,3nat],0,set![1int,3int],set![1int,3int],seq![2nat,0nat,2nat],3,Some(1),seq![1nat,3nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,Some(1),seq![1nat,3nat],0,set![],set![],seq![0nat,0nat,0nat],3,Some(1),seq![1nat,3nat],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 },Ballot { voter: 3,term: 3,candidate: 1 }] },
    _ if k == 47 => LState { nodes: IMap::empty().insert(1,node(3,Role::Leader,Some(1),seq![1nat,3nat],2,set![1int,3int],set![1int,3int],seq![2nat,0nat,2nat],3,Some(1),seq![1nat,3nat],0)).insert(2,node(2,Role::Leader,Some(2),seq![2nat],0,set![2int,3int],set![2int,3int],seq![0nat,0nat,0nat],2,Some(2),seq![2nat],0)).insert(3,node(3,Role::Follower,Some(1),seq![1nat,3nat],0,set![],set![],seq![0nat,0nat,0nat],3,Some(1),seq![1nat,3nat],0)),
        pending: Multiset::empty(),
        messages: Multiset::empty(),votes: set![Ballot { voter: 1,term: 1,candidate: 1 },Ballot { voter: 1,term: 3,candidate: 1 },Ballot { voter: 2,term: 2,candidate: 2 },Ballot { voter: 3,term: 1,candidate: 1 },Ballot { voter: 3,term: 2,candidate: 2 },Ballot { voter: 3,term: 3,candidate: 1 }] },
    _ => initial(constants()),
} }
#[verifier::opaque]
pub open spec fn action(k: int) -> Action { match k {
    _ if k == 0 => Action::Timeout(1),
    _ if k == 1 => Action::RequestVote { i: 1,j: 1 },
    _ if k == 2 => Action::RequestVote { i: 1,j: 3 },
    _ if k == 3 => Action::Ready(1),
    _ if k == 4 => Action::Receive { m: Message { source: 1,dest: 1,term: 1,body: Body::VoteResponse { granted: true } },how: Receive::VoteResponse },
    _ if k == 5 => Action::Receive { m: Message { source: 1,dest: 3,term: 1,body: Body::VoteRequest { last_term: 0,last_index: 0 } },how: Receive::UpdateTerm },
    _ if k == 6 => Action::Receive { m: Message { source: 1,dest: 3,term: 1,body: Body::VoteRequest { last_term: 0,last_index: 0 } },how: Receive::VoteRequest },
    _ if k == 7 => Action::Ready(3),
    _ if k == 8 => Action::Receive { m: Message { source: 3,dest: 1,term: 1,body: Body::VoteResponse { granted: true } },how: Receive::VoteResponse },
    _ if k == 9 => Action::BecomeLeader(1),
    _ if k == 10 => Action::ClientRequest(1),
    _ if k == 11 => Action::Ready(1),
    _ if k == 12 => Action::Timeout(2),
    _ if k == 13 => Action::Timeout(2),
    _ if k == 14 => Action::RequestVote { i: 2,j: 2 },
    _ if k == 15 => Action::RequestVote { i: 2,j: 3 },
    _ if k == 16 => Action::Ready(2),
    _ if k == 17 => Action::Receive { m: Message { source: 2,dest: 2,term: 2,body: Body::VoteResponse { granted: true } },how: Receive::VoteResponse },
    _ if k == 18 => Action::Receive { m: Message { source: 2,dest: 3,term: 2,body: Body::VoteRequest { last_term: 0,last_index: 0 } },how: Receive::UpdateTerm },
    _ if k == 19 => Action::Receive { m: Message { source: 2,dest: 3,term: 2,body: Body::VoteRequest { last_term: 0,last_index: 0 } },how: Receive::VoteRequest },
    _ if k == 20 => Action::Ready(3),
    _ if k == 21 => Action::Receive { m: Message { source: 3,dest: 2,term: 2,body: Body::VoteResponse { granted: true } },how: Receive::VoteResponse },
    _ if k == 22 => Action::BecomeLeader(2),
    _ if k == 23 => Action::ClientRequest(2),
    _ if k == 24 => Action::Ready(2),
    _ if k == 25 => Action::StepDown(1),
    _ if k == 26 => Action::Timeout(1),
    _ if k == 27 => Action::Timeout(1),
    _ if k == 28 => Action::RequestVote { i: 1,j: 1 },
    _ if k == 29 => Action::RequestVote { i: 1,j: 3 },
    _ if k == 30 => Action::Ready(1),
    _ if k == 31 => Action::Receive { m: Message { source: 1,dest: 1,term: 3,body: Body::VoteResponse { granted: true } },how: Receive::VoteResponse },
    _ if k == 32 => Action::Receive { m: Message { source: 1,dest: 3,term: 3,body: Body::VoteRequest { last_term: 1,last_index: 1 } },how: Receive::UpdateTerm },
    _ if k == 33 => Action::Receive { m: Message { source: 1,dest: 3,term: 3,body: Body::VoteRequest { last_term: 1,last_index: 1 } },how: Receive::VoteRequest },
    _ if k == 34 => Action::Ready(3),
    _ if k == 35 => Action::Receive { m: Message { source: 3,dest: 1,term: 3,body: Body::VoteResponse { granted: true } },how: Receive::VoteResponse },
    _ if k == 36 => Action::BecomeLeader(1),
    _ if k == 37 => Action::ClientRequest(1),
    _ if k == 38 => Action::SelfAppend(1),
    _ if k == 39 => Action::Append { i: 1,j: 3,begin: 1,end: 3 },
    _ if k == 40 => Action::Ready(1),
    _ if k == 41 => Action::Receive { m: Message { source: 1,dest: 1,term: 3,body: Body::AppendResponse { mode: Mode::App,success: true,matched: 2 } },how: Receive::AppendResponse },
    _ if k == 42 => Action::Receive { m: Message { source: 1,dest: 3,term: 3,body: Body::AppendRequest { mode: Mode::App,prev: 0,prev_term: 0,entries: seq![1nat,3nat],commit: 0 } },how: Receive::AppendExtend },
    _ if k == 43 => Action::Receive { m: Message { source: 1,dest: 3,term: 3,body: Body::AppendRequest { mode: Mode::App,prev: 0,prev_term: 0,entries: seq![1nat,3nat],commit: 0 } },how: Receive::AppendDone },
    _ if k == 44 => Action::Ready(3),
    _ if k == 45 => Action::Receive { m: Message { source: 3,dest: 1,term: 3,body: Body::AppendResponse { mode: Mode::App,success: true,matched: 2 } },how: Receive::AppendResponse },
    _ if k == 46 => Action::AdvanceCommit(1),
    _ => Action::Stutter,
} }
pub proof fn edge_0()
    ensures enabled(state(0),constants(),action(0)),apply(state(0),constants(),action(0)) == state(1)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(0); let a=action(0); let u=apply(s,constants(),a); let v=state(1);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_1()
    ensures enabled(state(1),constants(),action(1)),apply(state(1),constants(),action(1)) == state(2)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(1); let a=action(1); let u=apply(s,constants(),a); let v=state(2);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_2()
    ensures enabled(state(2),constants(),action(2)),apply(state(2),constants(),action(2)) == state(3)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(2); let a=action(2); let u=apply(s,constants(),a); let v=state(3);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_3()
    ensures enabled(state(3),constants(),action(3)),apply(state(3),constants(),action(3)) == state(4)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(3); let a=action(3); let u=apply(s,constants(),a); let v=state(4);
    election::record_released(s,1,Message { source: 1,dest: 1,term: 1,body: Body::VoteResponse { granted: true } });
    assert forall |b: Ballot| u.votes.contains(b) implies v.votes.contains(b) by {
        if !s.votes.contains(b) { let m=election::released_origin(s,1,b); }
    }
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_4()
    ensures enabled(state(4),constants(),action(4)),apply(state(4),constants(),action(4)) == state(5)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(4); let a=action(4); let u=apply(s,constants(),a); let v=state(5);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_5()
    ensures enabled(state(5),constants(),action(5)),apply(state(5),constants(),action(5)) == state(6)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(5); let a=action(5); let u=apply(s,constants(),a); let v=state(6);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_6()
    ensures enabled(state(6),constants(),action(6)),apply(state(6),constants(),action(6)) == state(7)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(6); let a=action(6); let u=apply(s,constants(),a); let v=state(7);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_7()
    ensures enabled(state(7),constants(),action(7)),apply(state(7),constants(),action(7)) == state(8)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(7); let a=action(7); let u=apply(s,constants(),a); let v=state(8);
    election::record_released(s,3,Message { source: 3,dest: 1,term: 1,body: Body::VoteResponse { granted: true } });
    assert forall |b: Ballot| u.votes.contains(b) implies v.votes.contains(b) by {
        if !s.votes.contains(b) { let m=election::released_origin(s,3,b); }
    }
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_8()
    ensures enabled(state(8),constants(),action(8)),apply(state(8),constants(),action(8)) == state(9)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(8); let a=action(8); let u=apply(s,constants(),a); let v=state(9);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_9()
    ensures enabled(state(9),constants(),action(9)),apply(state(9),constants(),action(9)) == state(10)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(9); let a=action(9); let u=apply(s,constants(),a); let v=state(10);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_10()
    ensures enabled(state(10),constants(),action(10)),apply(state(10),constants(),action(10)) == state(11)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(10); let a=action(10); let u=apply(s,constants(),a); let v=state(11);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_11()
    ensures enabled(state(11),constants(),action(11)),apply(state(11),constants(),action(11)) == state(12)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(11); let a=action(11); let u=apply(s,constants(),a); let v=state(12);
    assert forall |b: Ballot| u.votes.contains(b) implies v.votes.contains(b) by {
        if !s.votes.contains(b) { let m=election::released_origin(s,1,b); }
    }
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_12()
    ensures enabled(state(12),constants(),action(12)),apply(state(12),constants(),action(12)) == state(13)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(12); let a=action(12); let u=apply(s,constants(),a); let v=state(13);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_13()
    ensures enabled(state(13),constants(),action(13)),apply(state(13),constants(),action(13)) == state(14)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(13); let a=action(13); let u=apply(s,constants(),a); let v=state(14);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_14()
    ensures enabled(state(14),constants(),action(14)),apply(state(14),constants(),action(14)) == state(15)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(14); let a=action(14); let u=apply(s,constants(),a); let v=state(15);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_15()
    ensures enabled(state(15),constants(),action(15)),apply(state(15),constants(),action(15)) == state(16)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(15); let a=action(15); let u=apply(s,constants(),a); let v=state(16);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_16()
    ensures enabled(state(16),constants(),action(16)),apply(state(16),constants(),action(16)) == state(17)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(16); let a=action(16); let u=apply(s,constants(),a); let v=state(17);
    election::record_released(s,2,Message { source: 2,dest: 2,term: 2,body: Body::VoteResponse { granted: true } });
    assert forall |b: Ballot| u.votes.contains(b) implies v.votes.contains(b) by {
        if !s.votes.contains(b) { let m=election::released_origin(s,2,b); }
    }
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_17()
    ensures enabled(state(17),constants(),action(17)),apply(state(17),constants(),action(17)) == state(18)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(17); let a=action(17); let u=apply(s,constants(),a); let v=state(18);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_18()
    ensures enabled(state(18),constants(),action(18)),apply(state(18),constants(),action(18)) == state(19)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(18); let a=action(18); let u=apply(s,constants(),a); let v=state(19);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_19()
    ensures enabled(state(19),constants(),action(19)),apply(state(19),constants(),action(19)) == state(20)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(19); let a=action(19); let u=apply(s,constants(),a); let v=state(20);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_20()
    ensures enabled(state(20),constants(),action(20)),apply(state(20),constants(),action(20)) == state(21)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(20); let a=action(20); let u=apply(s,constants(),a); let v=state(21);
    election::record_released(s,3,Message { source: 3,dest: 2,term: 2,body: Body::VoteResponse { granted: true } });
    assert forall |b: Ballot| u.votes.contains(b) implies v.votes.contains(b) by {
        if !s.votes.contains(b) { let m=election::released_origin(s,3,b); }
    }
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_21()
    ensures enabled(state(21),constants(),action(21)),apply(state(21),constants(),action(21)) == state(22)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(21); let a=action(21); let u=apply(s,constants(),a); let v=state(22);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_22()
    ensures enabled(state(22),constants(),action(22)),apply(state(22),constants(),action(22)) == state(23)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(22); let a=action(22); let u=apply(s,constants(),a); let v=state(23);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_23()
    ensures enabled(state(23),constants(),action(23)),apply(state(23),constants(),action(23)) == state(24)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(23); let a=action(23); let u=apply(s,constants(),a); let v=state(24);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_24()
    ensures enabled(state(24),constants(),action(24)),apply(state(24),constants(),action(24)) == state(25)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(24); let a=action(24); let u=apply(s,constants(),a); let v=state(25);
    assert forall |b: Ballot| u.votes.contains(b) implies v.votes.contains(b) by {
        if !s.votes.contains(b) { let m=election::released_origin(s,2,b); }
    }
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_25()
    ensures enabled(state(25),constants(),action(25)),apply(state(25),constants(),action(25)) == state(26)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(25); let a=action(25); let u=apply(s,constants(),a); let v=state(26);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_26()
    ensures enabled(state(26),constants(),action(26)),apply(state(26),constants(),action(26)) == state(27)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(26); let a=action(26); let u=apply(s,constants(),a); let v=state(27);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_27()
    ensures enabled(state(27),constants(),action(27)),apply(state(27),constants(),action(27)) == state(28)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(27); let a=action(27); let u=apply(s,constants(),a); let v=state(28);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_28()
    ensures enabled(state(28),constants(),action(28)),apply(state(28),constants(),action(28)) == state(29)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(28); let a=action(28); let u=apply(s,constants(),a); let v=state(29);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_29()
    ensures enabled(state(29),constants(),action(29)),apply(state(29),constants(),action(29)) == state(30)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(29); let a=action(29); let u=apply(s,constants(),a); let v=state(30);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_30()
    ensures enabled(state(30),constants(),action(30)),apply(state(30),constants(),action(30)) == state(31)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(30); let a=action(30); let u=apply(s,constants(),a); let v=state(31);
    election::record_released(s,1,Message { source: 1,dest: 1,term: 3,body: Body::VoteResponse { granted: true } });
    assert forall |b: Ballot| u.votes.contains(b) implies v.votes.contains(b) by {
        if !s.votes.contains(b) { let m=election::released_origin(s,1,b); }
    }
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_31()
    ensures enabled(state(31),constants(),action(31)),apply(state(31),constants(),action(31)) == state(32)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(31); let a=action(31); let u=apply(s,constants(),a); let v=state(32);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_32()
    ensures enabled(state(32),constants(),action(32)),apply(state(32),constants(),action(32)) == state(33)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(32); let a=action(32); let u=apply(s,constants(),a); let v=state(33);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_33()
    ensures enabled(state(33),constants(),action(33)),apply(state(33),constants(),action(33)) == state(34)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(33); let a=action(33); let u=apply(s,constants(),a); let v=state(34);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_34()
    ensures enabled(state(34),constants(),action(34)),apply(state(34),constants(),action(34)) == state(35)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(34); let a=action(34); let u=apply(s,constants(),a); let v=state(35);
    election::record_released(s,3,Message { source: 3,dest: 1,term: 3,body: Body::VoteResponse { granted: true } });
    assert forall |b: Ballot| u.votes.contains(b) implies v.votes.contains(b) by {
        if !s.votes.contains(b) { let m=election::released_origin(s,3,b); }
    }
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_35()
    ensures enabled(state(35),constants(),action(35)),apply(state(35),constants(),action(35)) == state(36)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(35); let a=action(35); let u=apply(s,constants(),a); let v=state(36);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_36()
    ensures enabled(state(36),constants(),action(36)),apply(state(36),constants(),action(36)) == state(37)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(36); let a=action(36); let u=apply(s,constants(),a); let v=state(37);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_37()
    ensures enabled(state(37),constants(),action(37)),apply(state(37),constants(),action(37)) == state(38)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(37); let a=action(37); let u=apply(s,constants(),a); let v=state(38);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_38()
    ensures enabled(state(38),constants(),action(38)),apply(state(38),constants(),action(38)) == state(39)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(38); let a=action(38); let u=apply(s,constants(),a); let v=state(39);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_39()
    ensures enabled(state(39),constants(),action(39)),apply(state(39),constants(),action(39)) == state(40)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(39); let a=action(39); let u=apply(s,constants(),a); let v=state(40);
    assert(super::etcd::sub(s.nodes[1].log,1,2) =~= seq![1nat,3nat]);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_40()
    ensures enabled(state(40),constants(),action(40)),apply(state(40),constants(),action(40)) == state(41)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(40); let a=action(40); let u=apply(s,constants(),a); let v=state(41);
    assert forall |b: Ballot| u.votes.contains(b) implies v.votes.contains(b) by {
        if !s.votes.contains(b) { let m=election::released_origin(s,1,b); }
    }
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_41()
    ensures enabled(state(41),constants(),action(41)),apply(state(41),constants(),action(41)) == state(42)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(41); let a=action(41); let u=apply(s,constants(),a); let v=state(42);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_42()
    ensures enabled(state(42),constants(),action(42)),apply(state(42),constants(),action(42)) == state(43)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(42); let a=action(42); let u=apply(s,constants(),a); let v=state(43);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_43()
    ensures enabled(state(43),constants(),action(43)),apply(state(43),constants(),action(43)) == state(44)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(43); let a=action(43); let u=apply(s,constants(),a); let v=state(44);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_44()
    ensures enabled(state(44),constants(),action(44)),apply(state(44),constants(),action(44)) == state(45)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(44); let a=action(44); let u=apply(s,constants(),a); let v=state(45);
    assert forall |b: Ballot| u.votes.contains(b) implies v.votes.contains(b) by {
        if !s.votes.contains(b) { let m=election::released_origin(s,3,b); }
    }
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_45()
    ensures enabled(state(45),constants(),action(45)),apply(state(45),constants(),action(45)) == state(46)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(45); let a=action(45); let u=apply(s,constants(),a); let v=state(46);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge_46()
    ensures enabled(state(46),constants(),action(46)),apply(state(46),constants(),action(46)) == state(47)
{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state(46); let a=action(46); let u=apply(s,constants(),a); let v=state(47);
    let agreed=agreed_indices(s.nodes[1],constants());
    assert forall |index: int| 1 <= index <= 2 implies #[trigger] agreed.contains(index) by {
        assert(constants().voters.filter(|j: int| s.nodes[1].matched[j] >= index) =~= set![1int,3int]);
    }
    assert(agreed =~= set![1int,2int]); origins::maximum_correct(agreed);
    assert(agreed.contains(2)); assert(maximum(agreed) == 2);
    assert(u.nodes[1].commit == 2);
    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);
    assert(u.nodes[1].log =~= v.nodes[1].log); assert(u.nodes[1].disk.log =~= v.nodes[1].disk.log);
    assert(u.nodes[1].matched =~= v.nodes[1].matched);
    assert(u.nodes[2].log =~= v.nodes[2].log); assert(u.nodes[2].disk.log =~= v.nodes[2].disk.log);
    assert(u.nodes[2].matched =~= v.nodes[2].matched);
    assert(u.nodes[3].log =~= v.nodes[3].log); assert(u.nodes[3].disk.log =~= v.nodes[3].disk.log);
    assert(u.nodes[3].matched =~= v.nodes[3].matched);
    assert(u.nodes =~= v.nodes);
}
pub proof fn edge(k: int)
    requires 0 <= k < 47
    ensures enabled(state(k),constants(),action(k)),apply(state(k),constants(),action(k)) == state(k+1)
{ match k {
    _ if k == 0 => edge_0(),
    _ if k == 1 => edge_1(),
    _ if k == 2 => edge_2(),
    _ if k == 3 => edge_3(),
    _ if k == 4 => edge_4(),
    _ if k == 5 => edge_5(),
    _ if k == 6 => edge_6(),
    _ if k == 7 => edge_7(),
    _ if k == 8 => edge_8(),
    _ if k == 9 => edge_9(),
    _ if k == 10 => edge_10(),
    _ if k == 11 => edge_11(),
    _ if k == 12 => edge_12(),
    _ if k == 13 => edge_13(),
    _ if k == 14 => edge_14(),
    _ if k == 15 => edge_15(),
    _ if k == 16 => edge_16(),
    _ if k == 17 => edge_17(),
    _ if k == 18 => edge_18(),
    _ if k == 19 => edge_19(),
    _ if k == 20 => edge_20(),
    _ if k == 21 => edge_21(),
    _ if k == 22 => edge_22(),
    _ if k == 23 => edge_23(),
    _ if k == 24 => edge_24(),
    _ if k == 25 => edge_25(),
    _ if k == 26 => edge_26(),
    _ if k == 27 => edge_27(),
    _ if k == 28 => edge_28(),
    _ if k == 29 => edge_29(),
    _ if k == 30 => edge_30(),
    _ if k == 31 => edge_31(),
    _ if k == 32 => edge_32(),
    _ if k == 33 => edge_33(),
    _ if k == 34 => edge_34(),
    _ if k == 35 => edge_35(),
    _ if k == 36 => edge_36(),
    _ if k == 37 => edge_37(),
    _ if k == 38 => edge_38(),
    _ if k == 39 => edge_39(),
    _ if k == 40 => edge_40(),
    _ if k == 41 => edge_41(),
    _ if k == 42 => edge_42(),
    _ if k == 43 => edge_43(),
    _ if k == 44 => edge_44(),
    _ if k == 45 => edge_45(),
    _ if k == 46 => edge_46(),
    _ => {},
} }
pub proof fn counterexample() -> (b: Behavior<LState>)
    ensures election::safety_spec(b,constants()),!leader_completeness(b[47],constants())
{
    reveal(state);
    let c=constants(); let s=state(0);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    assert(s.nodes[1].matched =~= initial(c).nodes[1].matched);
    assert(s.nodes[2].matched =~= initial(c).nodes[2].matched);
    assert(s.nodes[3].matched =~= initial(c).nodes[3].matched);
    assert(s.nodes =~= initial(c).nodes);
    assert(s == initial(c));
    let b=IMap::new(|k: int| k >= 0,|k: int| state(if k < 47 { k } else { 47 }));
    assert forall |k: int| k >= 0 implies #[trigger] next(b[k],b[k+1],c) by {
        reveal(next);
        if k < 47 {
            edge(k); assert(enabled(b[k],c,action(k)) && b[k+1] == apply(b[k],c,action(k)));
        } else {
            reveal(enabled); reveal(apply);
            assert(enabled(b[k],c,Action::Stutter) && b[k+1] == apply(b[k],c,Action::Stutter));
        }
    }
    assert(b[47].nodes[1].commit == 2);
    assert(b[47].nodes[1].log[0] == 1);
    assert(b[47].nodes[2].role == Role::Leader && b[47].nodes[2].term == 2 && b[47].nodes[2].log[0] == 2);
    b
}
} // verus!
