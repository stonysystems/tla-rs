-------------------------------- MODULE Raft --------------------------------
(* Simplified Raft Consensus - Leader Election
   A basic model of Raft leader election for transpiler testing.

   Servers can be in one of three states: follower, candidate, or leader.
   Uses term numbers to coordinate elections. *)

EXTENDS Naturals

CONSTANT Server

VARIABLE currentTerm, state, votedFor, votesGranted

(* Server states *)
Follower == "follower"
Candidate == "candidate"
Leader == "leader"

(* Type invariant *)
TypeOK == currentTerm \in Nat /\ (state = Follower \/ state = Candidate \/ state = Leader)

(* Initial state: all servers are followers at term 0 *)
Init == currentTerm = 0 /\ state = Follower /\ votedFor = {} /\ votesGranted = {}

(* Server starts an election: increment term, vote for self *)
BecomeCandidate == state = Follower /\ state' = Candidate /\ currentTerm' = currentTerm + 1 /\ votedFor' = {currentTerm + 1} /\ votesGranted' = votesGranted

(* A server grants its vote to the candidate *)
GrantVote(voter) == state = Candidate /\ voter \notin votesGranted /\ votesGranted' = votesGranted \cup {voter} /\ state' = state /\ currentTerm' = currentTerm /\ votedFor' = votedFor

(* Candidate becomes leader if it has majority of votes *)
BecomeLeader == state = Candidate /\ state' = Leader /\ currentTerm' = currentTerm /\ votedFor' = votedFor /\ votesGranted' = votesGranted

(* Leader steps down when it sees higher term *)
StepDown == state = Leader /\ state' = Follower /\ votesGranted' = {} /\ currentTerm' = currentTerm /\ votedFor' = votedFor

(* Next state relation *)
Next == BecomeCandidate \/ BecomeLeader \/ StepDown

(* Invariant: at most one leader per term *)
AtMostOneLeader == state = Leader => votesGranted = votesGranted

================================================================================
