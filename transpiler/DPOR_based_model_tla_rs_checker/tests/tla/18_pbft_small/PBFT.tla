-------------------------------- MODULE PBFT --------------------------------
(* Practical Byzantine Fault Tolerance (Simplified)
   A simplified model for TLA+ transpiler testing.

   This models core PBFT phases:
   - Pre-prepare: Primary broadcasts request
   - Prepare: Replicas exchange prepare messages
   - Commit: Replicas exchange commit messages
   - Reply: Replicas send result to client *)

EXTENDS Naturals

CONSTANT Replica, Primary, F

VARIABLE view, phase, prepareCount, commitCount, msgs

(* Phase constants *)
PrePrepare == "pre-prepare"
Prepare == "prepare"
Commit == "commit"
Reply == "reply"

(* Quorum size for BFT: 2f+1 *)
QuorumSize == 2 * F + 1

(* Initial state *)
Init == view = 0 /\ phase = PrePrepare /\ prepareCount = 0 /\ commitCount = 0 /\ msgs = {}

(* Primary sends pre-prepare message *)
SendPrePrepare(v, n, d) == phase = PrePrepare /\ msgs' = msgs \cup {[type |-> PrePrepare, view |-> v, seq |-> n, digest |-> d]} /\ phase' = Prepare /\ view' = view /\ prepareCount' = prepareCount /\ commitCount' = commitCount

(* Replica sends prepare message *)
SendPrepare(r, v, n, d) == phase = Prepare /\ msgs' = msgs \cup {[type |-> Prepare, replica |-> r, view |-> v, seq |-> n, digest |-> d]} /\ prepareCount' = prepareCount + 1 /\ phase' = phase /\ view' = view /\ commitCount' = commitCount

(* Prepared predicate: received 2f prepares *)
Prepared == prepareCount >= QuorumSize

(* Transition to commit phase when prepared *)
EnterCommit == Prepared /\ phase = Prepare /\ phase' = Commit /\ view' = view /\ prepareCount' = prepareCount /\ commitCount' = commitCount /\ msgs' = msgs

(* Replica sends commit message *)
SendCommit(r, v, n, d) == phase = Commit /\ msgs' = msgs \cup {[type |-> Commit, replica |-> r, view |-> v, seq |-> n, digest |-> d]} /\ commitCount' = commitCount + 1 /\ phase' = phase /\ view' = view /\ prepareCount' = prepareCount

(* Committed predicate: received 2f+1 commits *)
Committed == commitCount >= QuorumSize

(* Execute and reply when committed *)
ExecuteAndReply == Committed /\ phase = Commit /\ phase' = Reply /\ view' = view /\ prepareCount' = prepareCount /\ commitCount' = commitCount /\ msgs' = msgs

(* View change: increment view on timeout *)
ViewChange == view' = view + 1 /\ phase' = PrePrepare /\ prepareCount' = 0 /\ commitCount' = 0 /\ msgs' = {}

(* Next state relation *)
Next == EnterCommit \/ ExecuteAndReply \/ ViewChange

(* Safety: once committed, value is stable *)
CommitSafety == Committed => phase = Reply \/ phase = Commit

(* Type invariant *)
TypeOK == view \in Nat /\ prepareCount \in Nat /\ commitCount \in Nat /\ (phase = PrePrepare \/ phase = Prepare \/ phase = Commit \/ phase = Reply)

================================================================================
