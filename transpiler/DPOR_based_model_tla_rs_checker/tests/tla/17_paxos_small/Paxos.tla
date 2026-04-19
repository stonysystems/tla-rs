-------------------------------- MODULE Paxos --------------------------------
\* Single-decree Paxos model for DPOR case 17.
\* 3 acceptors / 3 values for meaningful state space.

EXTENDS Naturals

VARIABLE maxBal, maxVBal, maxVal

\* Phase 38.18.9 scale-up sweep (post-symmetry-reduction):
\*   3/3 → 232 states / 0.37 s   (baseline, no symmetry)
\*   6/5 → 24,256 → 1,447 states / 25.0 s   (17× state reduction
\*                                            via Phase 38.18.9
\*                                            cross-field acceptor
\*                                            symmetry on maxBal/maxVBal)
\*   7/5 → 2,972 states / 75 s   (post-symmetry)
\*   8/5 → 6,033 states / 204 s  (chosen — half the budget)
\*   9/5 → 12,166 states / 555 s (over-budget margin)
Acceptors == {1, 2, 3, 4, 5, 6, 7, 8}
Values == {1, 2, 3, 4, 5}

Init ==
    /\ maxBal = {}
    /\ maxVBal = {}
    /\ maxVal = {}

Send1a(b) ==
    /\ b \in Acceptors
    /\ maxBal' = maxBal
    /\ maxVBal' = maxVBal
    /\ maxVal' = maxVal

Send1b(a, b) ==
    /\ a \in Acceptors
    /\ b \in Acceptors
    /\ maxBal' = maxBal \cup {b}
    /\ maxVBal' = maxVBal
    /\ maxVal' = maxVal

Send2a(b, v) ==
    /\ b \in Acceptors
    /\ v \in Values
    /\ (maxVal = {} \/ v \in maxVal)
    /\ maxBal' = maxBal
    /\ maxVBal' = maxVBal \cup {b}
    /\ maxVal' = maxVal

Send2b(a, b, v) ==
    /\ a \in Acceptors
    /\ b \in Acceptors
    /\ v \in Values
    /\ (maxVal = {} \/ v \in maxVal)
    /\ maxBal' = maxBal
    /\ maxVBal' = maxVBal \cup {b}
    /\ maxVal' = maxVal \cup {v}

\* Phase 38.18.8: with 38.18.6 handling the nested ∨-inside-∧-inside-
\* ∃ pattern, Next can use \E-quantifier form — branch discovery
\* automatically unrolls the action parameters to concrete branches.
\* This scales automatically when Acceptors/Values grow.
Next ==
    \/ \E b \in Acceptors : Send1a(b)
    \/ \E a \in Acceptors, b \in Acceptors : Send1b(a, b)
    \/ \E b \in Acceptors, v \in Values : Send2a(b, v)
    \/ \E a \in Acceptors, b \in Acceptors, v \in Values : Send2b(a, b, v)

ChosenValueAgreement ==
    \A v1, v2 \in maxVal : v1 = v2

TypeOK ==
    /\ maxBal \subseteq Acceptors
    /\ maxVBal \subseteq Acceptors
    /\ maxVal \subseteq Values

================================================================================
