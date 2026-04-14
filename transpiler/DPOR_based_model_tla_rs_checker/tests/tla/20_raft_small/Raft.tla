-------------------------------- MODULE Raft --------------------------------
\* Bounded Raft election model for DPOR case 20.
\* 5 servers for a meaningful state space with quorum reasoning.

EXTENDS Naturals

CONSTANT server

VARIABLE currentTerm, role, candidate, votesGranted

Follower == "follower"
Candidate == "candidate"
Leader == "leader"

Servers == {1, 2, 3, 4, 5}

HasQuorum(vs) ==
    \/ (1 \in vs /\ 2 \in vs /\ 3 \in vs)
    \/ (1 \in vs /\ 2 \in vs /\ 4 \in vs)
    \/ (1 \in vs /\ 2 \in vs /\ 5 \in vs)
    \/ (1 \in vs /\ 3 \in vs /\ 4 \in vs)
    \/ (1 \in vs /\ 3 \in vs /\ 5 \in vs)
    \/ (1 \in vs /\ 4 \in vs /\ 5 \in vs)
    \/ (2 \in vs /\ 3 \in vs /\ 4 \in vs)
    \/ (2 \in vs /\ 3 \in vs /\ 5 \in vs)
    \/ (2 \in vs /\ 4 \in vs /\ 5 \in vs)
    \/ (3 \in vs /\ 4 \in vs /\ 5 \in vs)

Init ==
    /\ server >= 5
    /\ currentTerm = 0
    /\ role = Follower
    /\ candidate = 0
    /\ votesGranted = {}

StartElection(cand) ==
    /\ role = Follower
    /\ cand \in Servers
    /\ role' = Candidate
    /\ currentTerm' = currentTerm + 1
    /\ candidate' = cand
    /\ votesGranted' = {cand}

GrantVote(voter) ==
    /\ role = Candidate
    /\ voter \in Servers
    /\ voter <= server
    /\ voter \notin votesGranted
    /\ votesGranted' = votesGranted \cup {voter}
    /\ role' = role
    /\ currentTerm' = currentTerm
    /\ candidate' = candidate

BecomeLeader(cand) ==
    /\ role = Candidate
    /\ cand = candidate
    /\ cand \in Servers
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
    \/ StartElection(1) \/ StartElection(2) \/ StartElection(3)
    \/ StartElection(4) \/ StartElection(5)
    \/ GrantVote(1) \/ GrantVote(2) \/ GrantVote(3)
    \/ GrantVote(4) \/ GrantVote(5)
    \/ BecomeLeader(1) \/ BecomeLeader(2) \/ BecomeLeader(3)
    \/ BecomeLeader(4) \/ BecomeLeader(5)
    \/ StepDown

ElectionSafety ==
    /\ role = Leader => HasQuorum(votesGranted)
    /\ role = Leader => candidate \in Servers

TypeOK ==
    /\ currentTerm \in Nat
    /\ (role = Follower \/ role = Candidate \/ role = Leader)
    /\ (candidate = 0 \/ candidate \in Servers)
    /\ votesGranted \subseteq Servers

================================================================================
