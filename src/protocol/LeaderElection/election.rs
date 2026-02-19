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
        &&& s.waiting_answer == false
        &&& s.waiting_node == 0int
    }

    /// A node detects leader failure and starts an election
    /// Sends an Election message and enters election state
    pub open spec fn LDetectFailure(
        s: LState, s_: LState, c: LConstants, node: int,
        sent_packets: Seq<LElectionMessage>,
    ) -> bool {
        &&& s.alive.contains(node)
        &&& s.has_leader == true
        &&& !s.alive.contains(s.leader)
        // Node starts election
        &&& s_.electing == s.electing.insert(node)
        // Mark waiting for answer
        &&& s_.waiting_answer == true
        &&& s_.waiting_node == node
        // Frame
        &&& s_.has_leader == s.has_leader
        &&& s_.leader == s.leader
        &&& s_.alive == s.alive
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
        // Send Election message
        &&& sent_packets == seq![LElectionMessage::Election { sender: node }]
    }

    /// A node starts an election (general trigger, e.g., timeout)
    /// The node enters election state and sends Election message
    pub open spec fn LStartElection(
        s: LState, s_: LState, c: LConstants, node: int,
        sent_packets: Seq<LElectionMessage>,
    ) -> bool {
        &&& s.alive.contains(node)
        // Node starts election
        &&& s_.electing == s.electing.insert(node)
        &&& s_.has_leader == false
        &&& s_.leader == 0int
        // Mark waiting for answer
        &&& s_.waiting_answer == true
        &&& s_.waiting_node == node
        // Frame
        &&& s_.alive == s.alive
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
        // Send Election message
        &&& sent_packets == seq![LElectionMessage::Election { sender: node }]
    }

    /// A higher-ID node responds to an election with an Answer message
    /// This suppresses the lower node's election attempt
    pub open spec fn LSendAnswer(
        s: LState, s_: LState, c: LConstants, node: int, sender: int,
        sent_packets: Seq<LElectionMessage>,
    ) -> bool {
        &&& s.alive.contains(node)
        &&& node > sender
        // Higher node also enters election
        &&& s_.electing == s.electing.insert(node)
        // Update highest heard
        &&& s_.has_highest == true
        &&& s_.highest_heard == (if !s.has_highest || node > s.highest_heard { node } else { s.highest_heard })
        // Frame
        &&& s_.has_leader == s.has_leader
        &&& s_.leader == s.leader
        &&& s_.alive == s.alive
        &&& s_.waiting_answer == s.waiting_answer
        &&& s_.waiting_node == s.waiting_node
        // Send Answer message
        &&& sent_packets == seq![LElectionMessage::Answer { responder: node }]
    }

    /// A node receives an Answer, stops its election attempt
    pub open spec fn LReceiveAnswer(
        s: LState, s_: LState, c: LConstants, node: int, responder: int,
        sent_packets: Seq<LElectionMessage>,
    ) -> bool {
        &&& s.alive.contains(node)
        &&& s.waiting_answer == true
        &&& s.waiting_node == node
        // Node stops waiting, defers to higher node
        &&& s_.waiting_answer == false
        &&& s_.waiting_node == 0int
        &&& s_.electing == s.electing.remove(node)
        // Frame
        &&& s_.has_leader == s.has_leader
        &&& s_.leader == s.leader
        &&& s_.alive == s.alive
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
        // No messages sent
        &&& sent_packets == Seq::<LElectionMessage>::empty()
    }

    /// A node wins the election (no Answer received) and sends Coordinator message
    pub open spec fn LSendCoordinator(
        s: LState, s_: LState, c: LConstants, node: int,
        sent_packets: Seq<LElectionMessage>,
    ) -> bool {
        &&& s.alive.contains(node)
        &&& s.electing.contains(node)
        &&& s.waiting_answer == true
        &&& s.waiting_node == node
        // Node becomes leader
        &&& s_.has_leader == true
        &&& s_.leader == node
        &&& s_.electing == s.electing.remove(node)
        // Clear waiting
        &&& s_.waiting_answer == false
        &&& s_.waiting_node == 0int
        // Frame
        &&& s_.alive == s.alive
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
        // Send Coordinator message
        &&& sent_packets == seq![LElectionMessage::Coordinator { leader: node }]
    }

    /// A node receives a Coordinator message and accepts the new leader
    pub open spec fn LReceiveCoordinator(
        s: LState, s_: LState, c: LConstants, node: int, leader: int,
        sent_packets: Seq<LElectionMessage>,
    ) -> bool {
        &&& s.alive.contains(node)
        // Accept the new leader
        &&& s_.has_leader == true
        &&& s_.leader == leader
        // Stop any ongoing election for this node
        &&& s_.electing == s.electing.remove(node)
        // Frame
        &&& s_.alive == s.alive
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
        &&& s_.waiting_answer == s.waiting_answer
        &&& s_.waiting_node == s.waiting_node
        // No messages sent
        &&& sent_packets == Seq::<LElectionMessage>::empty()
    }

    /// A node fails (crashes)
    /// If the failed node was the leader, leadership is cleared
    pub open spec fn LNodeFail(
        s: LState, s_: LState, c: LConstants, node: int,
        sent_packets: Seq<LElectionMessage>,
    ) -> bool {
        &&& s.alive.contains(node)
        &&& s_.alive == s.alive.remove(node)
        &&& s_.electing == s.electing.remove(node)
        // If failed node was the leader, clear leadership
        &&& s_.has_leader == (if s.has_leader && s.leader == node { false } else { s.has_leader })
        &&& s_.leader == (if s.has_leader && s.leader == node { 0int } else { s.leader })
        // Clear waiting if the waiting node failed
        &&& s_.waiting_answer == (if s.waiting_answer && s.waiting_node == node { false } else { s.waiting_answer })
        &&& s_.waiting_node == (if s.waiting_answer && s.waiting_node == node { 0int } else { s.waiting_node })
        // Frame
        &&& s_.has_highest == s.has_highest
        &&& s_.highest_heard == s.highest_heard
        // No messages sent
        &&& sent_packets == Seq::<LElectionMessage>::empty()
    }

    /// Next-state relation: disjunction of all possible transitions
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        ||| exists |node: int, sent_packets: Seq<LElectionMessage>| LDetectFailure(s, s_, c, node, sent_packets)
        ||| exists |node: int, sent_packets: Seq<LElectionMessage>| LStartElection(s, s_, c, node, sent_packets)
        ||| exists |node: int, sender: int, sent_packets: Seq<LElectionMessage>| LSendAnswer(s, s_, c, node, sender, sent_packets)
        ||| exists |node: int, responder: int, sent_packets: Seq<LElectionMessage>| LReceiveAnswer(s, s_, c, node, responder, sent_packets)
        ||| exists |node: int, sent_packets: Seq<LElectionMessage>| LSendCoordinator(s, s_, c, node, sent_packets)
        ||| exists |node: int, leader: int, sent_packets: Seq<LElectionMessage>| LReceiveCoordinator(s, s_, c, node, leader, sent_packets)
        ||| exists |node: int, sent_packets: Seq<LElectionMessage>| LNodeFail(s, s_, c, node, sent_packets)
    }
}
