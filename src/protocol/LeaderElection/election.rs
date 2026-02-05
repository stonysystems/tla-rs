use crate::protocol::LeaderElection::types::*;
use vstd::prelude::*;

verus! {
    /// Initialize the election protocol state
    /// All nodes start alive, no one is electing, no leader yet
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.electing == Set::<int>::empty()
        &&& s.has_leader == false
        &&& s.leader == 0int
        &&& s.alive == c.nodes
        &&& s.has_highest == false
        &&& s.highest_heard == 0int
    }

    /// A node starts an election
    /// The node enters election state; leader is cleared
    pub open spec fn LStartElection(s: LState, s_: LState, c: LConstants, node: int) -> bool {
        &&& s.alive.contains(node)
        &&& s_.electing == s.electing.insert(node)
        &&& s_.has_leader == false
        &&& s_.leader == 0int
        &&& s_.alive == s.alive
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
    }

    /// A higher-ID node responds to an election, updating highest_heard
    /// This models receiving an OK/alive message from a higher node
    pub open spec fn LRespondHigher(s: LState, s_: LState, c: LConstants, node: int) -> bool {
        &&& s.alive.contains(node)
        &&& !s.has_highest || node > s.highest_heard
        &&& s_.has_highest == true
        &&& s_.highest_heard == node
        &&& s_.electing == s.electing
        &&& s_.has_leader == s.has_leader
        &&& s_.leader == s.leader
        &&& s_.alive == s.alive
    }

    /// A node wins the election and becomes leader
    /// Only possible if the node is alive and was participating in election
    pub open spec fn LBecomeLeader(s: LState, s_: LState, c: LConstants, node: int) -> bool {
        &&& s.alive.contains(node)
        &&& s.electing.contains(node)
        &&& s_.has_leader == true
        &&& s_.leader == node
        &&& s_.electing == s.electing.remove(node)
        &&& s_.alive == s.alive
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
    }

    /// A node fails (crashes)
    /// If the failed node was the leader, leadership is cleared
    pub open spec fn LNodeFail(s: LState, s_: LState, c: LConstants, node: int) -> bool {
        &&& s.alive.contains(node)
        &&& s_.alive == s.alive.remove(node)
        &&& s_.electing == s.electing.remove(node)
        &&& if s.has_leader && s.leader == node {
            &&& s_.has_leader == false
            &&& s_.leader == 0int
        } else {
            &&& s_.has_leader == s.has_leader
            &&& s_.leader == s.leader
        }
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
    }

    /// Next-state relation: disjunction of all possible transitions
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        ||| exists |node: int| LStartElection(s, s_, c, node)
        ||| exists |node: int| LRespondHigher(s, s_, c, node)
        ||| exists |node: int| LBecomeLeader(s, s_, c, node)
        ||| exists |node: int| LNodeFail(s, s_, c, node)
    }
}
