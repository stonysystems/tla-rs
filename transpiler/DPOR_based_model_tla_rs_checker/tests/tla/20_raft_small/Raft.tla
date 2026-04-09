-------------------------------- MODULE Raft --------------------------------
\* Small bounded Raft election model for DPOR case 20.
\* Tracks a candidate and granted votes across three concrete servers.

EXTENDS Naturals

CONSTANT server

VARIABLE currentTerm, role, candidate, votesGranted

Follower == "follower"
Candidate == "candidate"
Leader == "leader"

HasQuorum(vs) ==
    \/ (1 \in vs /\ 2 \in vs)
    \/ (1 \in vs /\ 3 \in vs)
    \/ (2 \in vs /\ 3 \in vs)

Init ==
    /\ server >= 3
    /\ currentTerm = 0
    /\ role = Follower
    /\ candidate = 0
    /\ votesGranted = {}

StartElection(cand) ==
    /\ role = Follower
    /\ (cand = 1 \/ cand = 2 \/ cand = 3)
    /\ role' = Candidate
    /\ currentTerm' = currentTerm + 1
    /\ candidate' = cand
    /\ votesGranted' = {cand}

GrantVote(voter) ==
    /\ role = Candidate
    /\ (voter = 1 \/ voter = 2 \/ voter = 3)
    /\ voter <= server
    /\ voter \notin votesGranted
    /\ votesGranted' = votesGranted \cup {voter}
    /\ role' = role
    /\ currentTerm' = currentTerm
    /\ candidate' = candidate

BecomeLeader(cand) ==
    /\ role = Candidate
    /\ cand = candidate
    /\ (cand = 1 \/ cand = 2 \/ cand = 3)
    /\ HasQuorum(votesGranted)
    /\ role' = Leader
    /\ currentTerm' = currentTerm
    /\ candidate' = candidate
    /\ votesGranted' = votesGranted

StepDown ==
    /\ role = Leader
    /\ role' = Follower
    /\ candidate' = 0
    /\ votesGranted' = {}
    /\ currentTerm' = currentTerm

Next ==
    \/ StartElection(1)
    \/ StartElection(2)
    \/ StartElection(3)
    \/ GrantVote(1)
    \/ GrantVote(2)
    \/ GrantVote(3)
    \/ BecomeLeader(1)
    \/ BecomeLeader(2)
    \/ BecomeLeader(3)
    \/ StepDown

ElectionSafety ==
    /\ role = Leader => HasQuorum(votesGranted)
    /\ role = Leader => (candidate = 1 \/ candidate = 2 \/ candidate = 3)

TypeOK ==
    /\ currentTerm \in Nat
    /\ (role = Follower \/ role = Candidate \/ role = Leader)
    /\ (candidate = 0 \/ candidate = 1 \/ candidate = 2 \/ candidate = 3)
    /\ votesGranted \subseteq {1, 2, 3}

================================================================================
