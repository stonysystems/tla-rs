---- MODULE SimpleConsensus ----
\* LLM-generated basic consensus protocol.
\* Uses only supported parser features.

EXTENDS Naturals

VARIABLE proposed, accepted, decided, round

Init ==
    /\ proposed = 0
    /\ accepted = 0
    /\ decided = FALSE
    /\ round = 0

Propose(v) ==
    /\ decided = FALSE
    /\ proposed' = v
    /\ accepted' = accepted
    /\ decided' = decided
    /\ round' = round + 1

Accept ==
    /\ proposed > 0
    /\ decided = FALSE
    /\ accepted' = proposed
    /\ proposed' = proposed
    /\ decided' = decided
    /\ round' = round

Decide ==
    /\ accepted > 0
    /\ decided = FALSE
    /\ decided' = TRUE
    /\ proposed' = proposed
    /\ accepted' = accepted
    /\ round' = round

Next == Decide \/ Accept

====
