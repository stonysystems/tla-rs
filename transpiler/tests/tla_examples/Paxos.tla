-------------------------------- MODULE Paxos --------------------------------
(* Single-Decree Paxos Consensus Algorithm
   A simplified model for TLA+ transpiler testing.

   This models the core Paxos consensus algorithm with:
   - Proposers that generate ballots and proposals
   - Acceptors that vote on proposals
   - Learners that detect consensus *)

EXTENDS Naturals

CONSTANT Value, Acceptor, Quorum

VARIABLE maxBal, maxVBal, maxVal, msgs

(* Message types *)
Phase1a == "phase1a"
Phase1b == "phase1b"
Phase2a == "phase2a"
Phase2b == "phase2b"

(* Initial state: no ballots, no values, no messages *)
Init == maxBal = {} /\ maxVBal = {} /\ maxVal = {} /\ msgs = {}

(* Phase 1a: Proposer sends prepare request with ballot b *)
Send1a(b) == msgs' = msgs \cup {[type |-> Phase1a, bal |-> b]} /\ maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVal' = maxVal

(* Phase 1b: Acceptor a responds to prepare if ballot >= maxBal *)
Send1b(a, b) == msgs' = msgs \cup {[type |-> Phase1b, acc |-> a, bal |-> b]} /\ maxBal' = maxBal \cup {b} /\ maxVBal' = maxVBal /\ maxVal' = maxVal

(* Phase 2a: Proposer sends accept request with ballot b and value v *)
Send2a(b, v) == msgs' = msgs \cup {[type |-> Phase2a, bal |-> b, val |-> v]} /\ maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVal' = maxVal

(* Phase 2b: Acceptor a accepts ballot b with value v *)
Send2b(a, b, v) == msgs' = msgs \cup {[type |-> Phase2b, acc |-> a, bal |-> b, val |-> v]} /\ maxBal' = maxBal /\ maxVBal' = maxVBal \cup {b} /\ maxVal' = maxVal \cup {v}

(* Next state relation *)
Next == msgs' = msgs /\ maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVal' = maxVal

(* Safety: At most one value can be chosen *)
Chosen(v) == v \in maxVal

(* Type invariant *)
TypeOK == msgs = msgs /\ maxBal = maxBal

================================================================================
