use crate::protocol::Paxos::types::*;
use vstd::prelude::*;

verus! {
    /// Initialize the Paxos protocol state
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        // Acceptor state
        &&& s.promised_bal == 0
        &&& s.accepted_bal == 0
        &&& s.accepted_val == 0
        // Proposer state
        &&& s.proposer_bal == 0
        &&& s.phase is Idle
        &&& s.promises_rcvd == Set::<int>::empty()
        &&& s.highest_accepted_bal == 0
        &&& s.highest_accepted_val == 0
        &&& s.proposed_val == 0
        // Learner state
        &&& s.accepts_rcvd == Set::<int>::empty()
        &&& s.decided_val == 0
    }

    /// Phase 1a: Proposer starts a new round with ballot b
    /// Generates a unique ballot and enters Phase 1
    pub open spec fn LSend1a(s: LState, s_: LState, c: LConstants, b: int) -> bool {
        &&& s.phase is Idle
        &&& b > s.proposer_bal
        // Update proposer state
        &&& s_.proposer_bal == b
        &&& s_.phase is Phase1
        &&& s_.promises_rcvd == Set::<int>::empty()
        &&& s_.highest_accepted_bal == 0
        &&& s_.highest_accepted_val == 0
        &&& s_.proposed_val == s.proposed_val
        // Acceptor state unchanged
        &&& s_.promised_bal == s.promised_bal
        &&& s_.accepted_bal == s.accepted_bal
        &&& s_.accepted_val == s.accepted_val
        // Learner state unchanged
        &&& s_.accepts_rcvd == s.accepts_rcvd
        &&& s_.decided_val == s.decided_val
    }

    /// Phase 1b: Acceptor receives Prepare(b), promises not to accept lower ballots
    /// Sends back a promise with its last accepted ballot and value
    pub open spec fn LSend1b(s: LState, s_: LState, c: LConstants, b: int) -> bool {
        &&& b >= s.promised_bal
        // Update acceptor: promise this ballot
        &&& s_.promised_bal == b
        // Acceptor's accepted state unchanged
        &&& s_.accepted_bal == s.accepted_bal
        &&& s_.accepted_val == s.accepted_val
        // Proposer state unchanged
        &&& s_.proposer_bal == s.proposer_bal
        &&& s_.phase == s.phase
        &&& s_.promises_rcvd == s.promises_rcvd
        &&& s_.highest_accepted_bal == s.highest_accepted_bal
        &&& s_.highest_accepted_val == s.highest_accepted_val
        &&& s_.proposed_val == s.proposed_val
        // Learner state unchanged
        &&& s_.accepts_rcvd == s.accepts_rcvd
        &&& s_.decided_val == s.decided_val
    }

    /// Proposer receives a promise from acceptor a for its ballot
    /// Tracks the promise and updates highest accepted value if needed
    pub open spec fn LRecvPromise(s: LState, s_: LState, c: LConstants, a: int, a_accepted_bal: int, a_accepted_val: int) -> bool {
        &&& s.phase is Phase1
        &&& c.acceptors.contains(a)
        &&& !s.promises_rcvd.contains(a)
        // Update proposer: record promise
        &&& s_.promises_rcvd == s.promises_rcvd.insert(a)
        // If this acceptor had a higher accepted ballot, adopt its value
        &&& s_.highest_accepted_bal == (if a_accepted_bal > s.highest_accepted_bal { a_accepted_bal } else { s.highest_accepted_bal })
        &&& s_.highest_accepted_val == (if a_accepted_bal > s.highest_accepted_bal { a_accepted_val } else { s.highest_accepted_val })
        // Other proposer state unchanged
        &&& s_.proposer_bal == s.proposer_bal
        &&& s_.phase is Phase1
        &&& s_.proposed_val == s.proposed_val
        // Acceptor state unchanged
        &&& s_.promised_bal == s.promised_bal
        &&& s_.accepted_bal == s.accepted_bal
        &&& s_.accepted_val == s.accepted_val
        // Learner state unchanged
        &&& s_.accepts_rcvd == s.accepts_rcvd
        &&& s_.decided_val == s.decided_val
    }

    /// Phase 2a: Proposer has quorum of promises, sends Accept with value
    /// If any acceptor had an accepted value, use the highest one; otherwise use own value
    pub open spec fn LSend2a(s: LState, s_: LState, c: LConstants, v: int) -> bool {
        &&& s.phase is Phase1
        &&& s.promises_rcvd.len() >= c.quorum_size
        // Pick value: highest accepted from promises, or own value v
        &&& s_.proposed_val == (if s.highest_accepted_bal > 0 { s.highest_accepted_val } else { v })
        // Transition to Phase 2
        &&& s_.phase is Phase2
        &&& s_.accepts_rcvd == Set::<int>::empty()
        // Proposer state preserved
        &&& s_.proposer_bal == s.proposer_bal
        &&& s_.promises_rcvd == s.promises_rcvd
        &&& s_.highest_accepted_bal == s.highest_accepted_bal
        &&& s_.highest_accepted_val == s.highest_accepted_val
        // Acceptor state unchanged
        &&& s_.promised_bal == s.promised_bal
        &&& s_.accepted_bal == s.accepted_bal
        &&& s_.accepted_val == s.accepted_val
        // Learner state unchanged
        &&& s_.decided_val == s.decided_val
    }

    /// Phase 2b: Acceptor receives Accept(b, v), accepts if ballot >= promised
    pub open spec fn LSend2b(s: LState, s_: LState, c: LConstants, b: int, v: int) -> bool {
        &&& b >= s.promised_bal
        // Update acceptor: accept this ballot and value
        &&& s_.promised_bal == b
        &&& s_.accepted_bal == b
        &&& s_.accepted_val == v
        // Proposer state unchanged
        &&& s_.proposer_bal == s.proposer_bal
        &&& s_.phase == s.phase
        &&& s_.promises_rcvd == s.promises_rcvd
        &&& s_.highest_accepted_bal == s.highest_accepted_bal
        &&& s_.highest_accepted_val == s.highest_accepted_val
        &&& s_.proposed_val == s.proposed_val
        // Learner state unchanged
        &&& s_.accepts_rcvd == s.accepts_rcvd
        &&& s_.decided_val == s.decided_val
    }

    /// Proposer receives an Accept acknowledgment from acceptor a
    pub open spec fn LRecvAccepted(s: LState, s_: LState, c: LConstants, a: int) -> bool {
        &&& s.phase is Phase2
        &&& c.acceptors.contains(a)
        &&& !s.accepts_rcvd.contains(a)
        // Update learner: record accept
        &&& s_.accepts_rcvd == s.accepts_rcvd.insert(a)
        // Other state unchanged
        &&& s_.proposer_bal == s.proposer_bal
        &&& s_.phase is Phase2
        &&& s_.promises_rcvd == s.promises_rcvd
        &&& s_.highest_accepted_bal == s.highest_accepted_bal
        &&& s_.highest_accepted_val == s.highest_accepted_val
        &&& s_.proposed_val == s.proposed_val
        &&& s_.promised_bal == s.promised_bal
        &&& s_.accepted_bal == s.accepted_bal
        &&& s_.accepted_val == s.accepted_val
        &&& s_.decided_val == s.decided_val
    }

    /// Learn: quorum of acceptors have accepted, value is decided
    pub open spec fn LLearn(s: LState, s_: LState, c: LConstants) -> bool {
        &&& s.phase is Phase2
        &&& s.accepts_rcvd.len() >= c.quorum_size
        // Transition to Decided
        &&& s_.phase is Decided
        &&& s_.decided_val == s.proposed_val
        // Other state unchanged
        &&& s_.proposer_bal == s.proposer_bal
        &&& s_.promises_rcvd == s.promises_rcvd
        &&& s_.highest_accepted_bal == s.highest_accepted_bal
        &&& s_.highest_accepted_val == s.highest_accepted_val
        &&& s_.proposed_val == s.proposed_val
        &&& s_.accepts_rcvd == s.accepts_rcvd
        &&& s_.promised_bal == s.promised_bal
        &&& s_.accepted_bal == s.accepted_bal
        &&& s_.accepted_val == s.accepted_val
    }

    /// Paxos safety invariant: an acceptor cannot have accepted above its promise.
    pub open spec fn LSafetyAcceptedBallotBoundedByPromise(s: LState, c: LConstants) -> bool {
        s.accepted_bal <= s.promised_bal
    }

    /// Paxos safety invariant: reaching Decided implies quorum evidence exists.
    pub open spec fn LSafetyDecidedRequiresQuorum(s: LState, c: LConstants) -> bool {
        (s.phase is Decided) ==> (s.accepts_rcvd.len() >= c.quorum_size)
    }

    /// Paxos safety invariant: decided value must match the value chosen in Phase2.
    pub open spec fn LSafetyDecidedMatchesProposedValue(s: LState, c: LConstants) -> bool {
        (s.phase is Decided) ==> (s.decided_val == s.proposed_val)
    }

    /// Next-state relation: disjunction of all possible transitions
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        ||| (exists |b: int| LSend1a(s, s_, c, b))
        ||| (exists |b: int| LSend1b(s, s_, c, b))
        ||| (exists |a: int, ab: int, av: int| LRecvPromise(s, s_, c, a, ab, av))
        ||| (exists |v: int| LSend2a(s, s_, c, v))
        ||| (exists |b: int, v: int| LSend2b(s, s_, c, b, v))
        ||| (exists |a: int| LRecvAccepted(s, s_, c, a))
        ||| LLearn(s, s_, c)
    }
}
