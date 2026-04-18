-------------------------------- MODULE Paxos --------------------------------
\* Single-decree Paxos model for DPOR case 17.
\* 3 acceptors / 3 values for meaningful state space.

EXTENDS Naturals

VARIABLE maxBal, maxVBal, maxVal

\* Phase 38.18.8 scale-up sweep (post-inliner-fix):
\*   3/3 → 232 states / 0.37 s   (baseline)
\*   4/4 → 1,216 states / 6.7 s
\*   5/4 → 4,992 states / 46.7 s
\*   5/5 → 5,984 states / 60.3 s
\*   6/4 → 20,224 states / 267 s
\*   6/5 → 24,256 states / 370 s  (chosen — fits in 10-min budget
\*                                 with ~4 min headroom, 100× the
\*                                 original state count)
Acceptors == {1, 2, 3, 4, 5, 6}
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
