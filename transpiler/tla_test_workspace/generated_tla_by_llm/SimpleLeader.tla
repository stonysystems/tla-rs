---- MODULE SimpleLeader ----
\* LLM-generated simplified leader election.
\* Uses flat state variables and set operations.

EXTENDS Naturals

VARIABLE isLeader, term, voted, candidates

Init ==
    /\ isLeader = FALSE
    /\ term = 0
    /\ voted = {}
    /\ candidates = {}

StartElection ==
    /\ isLeader = FALSE
    /\ term' = term + 1
    /\ candidates' = candidates \cup {term + 1}
    /\ voted' = voted
    /\ isLeader' = isLeader

CastVote(candidate) ==
    /\ candidate \in candidates
    /\ candidate \notin voted
    /\ voted' = voted \cup {candidate}
    /\ term' = term
    /\ candidates' = candidates
    /\ isLeader' = isLeader

WinElection ==
    /\ isLeader = FALSE
    /\ isLeader' = TRUE
    /\ term' = term
    /\ voted' = voted
    /\ candidates' = candidates

StepDown ==
    /\ isLeader = TRUE
    /\ isLeader' = FALSE
    /\ term' = term
    /\ voted' = {}
    /\ candidates' = {}

Next == StartElection \/ WinElection \/ StepDown

====
