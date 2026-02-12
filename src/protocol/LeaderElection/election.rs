use crate::protocol::LeaderElection::types::*;
use vstd::prelude::*;

verus! {
    /// Initialize the election protocol state
    /// All nodes start alive, no one is electing, no leader yet, no messages
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.electing == Set::<int>::empty()
        &&& s.has_leader == false
        &&& s.leader == 0int
        &&& s.alive == c.nodes
        &&& s.has_highest == false
        &&& s.highest_heard == 0int
        &&& s.msgs_election == false
        &&& s.msgs_election_sender == 0int
        &&& s.msgs_answer == false
        &&& s.msgs_answer_responder == 0int
        &&& s.msgs_coordinator == false
        &&& s.msgs_coordinator_leader == 0int
        &&& s.waiting_answer == false
        &&& s.waiting_node == 0int
    }

    /// A node detects leader failure and starts an election
    /// Sends an Election message and enters election state
    pub open spec fn LDetectFailure(s: LState, s_: LState, c: LConstants, node: int) -> bool {
        &&& s.alive.contains(node)
        &&& s.has_leader == true
        &&& !s.alive.contains(s.leader)
        // Node starts election
        &&& s_.electing == s.electing.insert(node)
        // Send Election message
        &&& s_.msgs_election == true
        &&& s_.msgs_election_sender == node
        // Mark waiting for answer
        &&& s_.waiting_answer == true
        &&& s_.waiting_node == node
        // Frame
        &&& s_.has_leader == s.has_leader
        &&& s_.leader == s.leader
        &&& s_.alive == s.alive
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
        &&& s_.msgs_answer == s.msgs_answer
        &&& s_.msgs_answer_responder == s.msgs_answer_responder
        &&& s_.msgs_coordinator == s.msgs_coordinator
        &&& s_.msgs_coordinator_leader == s.msgs_coordinator_leader
    }

    /// A node starts an election (general trigger, e.g., timeout)
    /// The node enters election state and sends Election message
    pub open spec fn LStartElection(s: LState, s_: LState, c: LConstants, node: int) -> bool {
        &&& s.alive.contains(node)
        // Node starts election
        &&& s_.electing == s.electing.insert(node)
        &&& s_.has_leader == false
        &&& s_.leader == 0int
        // Send Election message
        &&& s_.msgs_election == true
        &&& s_.msgs_election_sender == node
        // Mark waiting for answer
        &&& s_.waiting_answer == true
        &&& s_.waiting_node == node
        // Frame
        &&& s_.alive == s.alive
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
        &&& s_.msgs_answer == s.msgs_answer
        &&& s_.msgs_answer_responder == s.msgs_answer_responder
        &&& s_.msgs_coordinator == s.msgs_coordinator
        &&& s_.msgs_coordinator_leader == s.msgs_coordinator_leader
    }

    /// A higher-ID node responds to an election with an Answer message
    /// This suppresses the lower node's election attempt
    pub open spec fn LSendAnswer(s: LState, s_: LState, c: LConstants, node: int) -> bool {
        &&& s.alive.contains(node)
        &&& s.msgs_election == true
        &&& node > s.msgs_election_sender
        // Send Answer message
        &&& s_.msgs_answer == true
        &&& s_.msgs_answer_responder == node
        // Higher node also enters election
        &&& s_.electing == s.electing.insert(node)
        // Update highest heard
        &&& s_.has_highest == true
        &&& s_.highest_heard == (if !s.has_highest || node > s.highest_heard { node } else { s.highest_heard })
        // Frame
        &&& s_.has_leader == s.has_leader
        &&& s_.leader == s.leader
        &&& s_.alive == s.alive
        &&& s_.msgs_election == s.msgs_election
        &&& s_.msgs_election_sender == s.msgs_election_sender
        &&& s_.msgs_coordinator == s.msgs_coordinator
        &&& s_.msgs_coordinator_leader == s.msgs_coordinator_leader
        &&& s_.waiting_answer == s.waiting_answer
        &&& s_.waiting_node == s.waiting_node
    }

    /// A node receives an Answer, stops its election attempt
    pub open spec fn LReceiveAnswer(s: LState, s_: LState, c: LConstants, node: int) -> bool {
        &&& s.alive.contains(node)
        &&& s.msgs_answer == true
        &&& s.waiting_answer == true
        &&& s.waiting_node == node
        // Node stops waiting, defers to higher node
        &&& s_.waiting_answer == false
        &&& s_.waiting_node == 0int
        &&& s_.electing == s.electing.remove(node)
        // Clear Answer message
        &&& s_.msgs_answer == false
        &&& s_.msgs_answer_responder == 0int
        // Frame
        &&& s_.has_leader == s.has_leader
        &&& s_.leader == s.leader
        &&& s_.alive == s.alive
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
        &&& s_.msgs_election == s.msgs_election
        &&& s_.msgs_election_sender == s.msgs_election_sender
        &&& s_.msgs_coordinator == s.msgs_coordinator
        &&& s_.msgs_coordinator_leader == s.msgs_coordinator_leader
    }

    /// A node wins the election (no Answer received) and sends Coordinator message
    pub open spec fn LSendCoordinator(s: LState, s_: LState, c: LConstants, node: int) -> bool {
        &&& s.alive.contains(node)
        &&& s.electing.contains(node)
        &&& s.waiting_answer == true
        &&& s.waiting_node == node
        &&& s.msgs_answer == false
        // Node becomes leader
        &&& s_.has_leader == true
        &&& s_.leader == node
        &&& s_.electing == s.electing.remove(node)
        // Send Coordinator message
        &&& s_.msgs_coordinator == true
        &&& s_.msgs_coordinator_leader == node
        // Clear waiting and election message
        &&& s_.waiting_answer == false
        &&& s_.waiting_node == 0int
        &&& s_.msgs_election == false
        &&& s_.msgs_election_sender == 0int
        // Frame
        &&& s_.alive == s.alive
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
        &&& s_.msgs_answer == s.msgs_answer
        &&& s_.msgs_answer_responder == s.msgs_answer_responder
    }

    /// A node receives a Coordinator message and accepts the new leader
    pub open spec fn LReceiveCoordinator(s: LState, s_: LState, c: LConstants, node: int) -> bool {
        &&& s.alive.contains(node)
        &&& s.msgs_coordinator == true
        // Accept the new leader
        &&& s_.has_leader == true
        &&& s_.leader == s.msgs_coordinator_leader
        // Stop any ongoing election for this node
        &&& s_.electing == s.electing.remove(node)
        // Clear Coordinator message
        &&& s_.msgs_coordinator == false
        &&& s_.msgs_coordinator_leader == 0int
        // Frame
        &&& s_.alive == s.alive
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
        &&& s_.msgs_election == s.msgs_election
        &&& s_.msgs_election_sender == s.msgs_election_sender
        &&& s_.msgs_answer == s.msgs_answer
        &&& s_.msgs_answer_responder == s.msgs_answer_responder
        &&& s_.waiting_answer == s.waiting_answer
        &&& s_.waiting_node == s.waiting_node
    }

    /// A node fails (crashes)
    /// If the failed node was the leader, leadership is cleared
    pub open spec fn LNodeFail(s: LState, s_: LState, c: LConstants, node: int) -> bool {
        &&& s.alive.contains(node)
        &&& s_.alive == s.alive.remove(node)
        &&& s_.electing == s.electing.remove(node)
        // If failed node was the leader, clear leadership
        &&& s_.has_leader == (if s.has_leader && s.leader == node { false } else { s.has_leader })
        &&& s_.leader == (if s.has_leader && s.leader == node { 0int } else { s.leader })
        // Clear messages if they involved the failed node
        &&& s_.msgs_election == (if s.msgs_election && s.msgs_election_sender == node { false } else { s.msgs_election })
        &&& s_.msgs_election_sender == (if s.msgs_election && s.msgs_election_sender == node { 0int } else { s.msgs_election_sender })
        &&& s_.msgs_answer == (if s.msgs_answer && s.msgs_answer_responder == node { false } else { s.msgs_answer })
        &&& s_.msgs_answer_responder == (if s.msgs_answer && s.msgs_answer_responder == node { 0int } else { s.msgs_answer_responder })
        &&& s_.msgs_coordinator == (if s.msgs_coordinator && s.msgs_coordinator_leader == node { false } else { s.msgs_coordinator })
        &&& s_.msgs_coordinator_leader == (if s.msgs_coordinator && s.msgs_coordinator_leader == node { 0int } else { s.msgs_coordinator_leader })
        // Clear waiting if the waiting node failed
        &&& s_.waiting_answer == (if s.waiting_answer && s.waiting_node == node { false } else { s.waiting_answer })
        &&& s_.waiting_node == (if s.waiting_answer && s.waiting_node == node { 0int } else { s.waiting_node })
        // Frame
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
    }

    /// Next-state relation: disjunction of all possible transitions
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        ||| exists |node: int| LDetectFailure(s, s_, c, node)
        ||| exists |node: int| LStartElection(s, s_, c, node)
        ||| exists |node: int| LSendAnswer(s, s_, c, node)
        ||| exists |node: int| LReceiveAnswer(s, s_, c, node)
        ||| exists |node: int| LSendCoordinator(s, s_, c, node)
        ||| exists |node: int| LReceiveCoordinator(s, s_, c, node)
        ||| exists |node: int| LNodeFail(s, s_, c, node)
    }
}
