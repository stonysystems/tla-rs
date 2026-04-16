-------------------------------- MODULE Paxos --------------------------------
\* Single-decree Paxos model for DPOR case 17.
\* 3 acceptors / 3 values for meaningful state space.

EXTENDS Naturals

VARIABLE maxBal, maxVBal, maxVal

\* Phase 38.20.3: scale axis explored:
\*   3/3 (baseline): 232 states, 0.51 s
\*   3/4 (more values): >600 s timeout
\*   4/3 (more acceptors): >600 s timeout
\*   4/4: >600 s timeout
\* Settled on keeping 3/3 — single-decree Paxos's reachable-state
\* space at any larger bound exceeds the 10-minute DPOR budget on the
\* current single-threaded explorer. Future scale-up depends on
\* Phase 38.18.1 (parallelize the explorer).
Acceptors == {1, 2, 3}
Values == {1, 2, 3}

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

\* Next is fully unrolled (no \E quantifiers) so the Phase-38.17.2
\* action-call inliner can convert each branch to direct-assignment
\* form. \E-quantified Next regressed Paxos to >600 s.
Next ==
    \/ Send1a(1) \/ Send1a(2) \/ Send1a(3)
    \/ Send1b(1, 1) \/ Send1b(1, 2) \/ Send1b(1, 3)
    \/ Send1b(2, 1) \/ Send1b(2, 2) \/ Send1b(2, 3)
    \/ Send1b(3, 1) \/ Send1b(3, 2) \/ Send1b(3, 3)
    \/ Send2a(1, 1) \/ Send2a(1, 2) \/ Send2a(1, 3)
    \/ Send2a(2, 1) \/ Send2a(2, 2) \/ Send2a(2, 3)
    \/ Send2a(3, 1) \/ Send2a(3, 2) \/ Send2a(3, 3)
    \/ Send2b(1, 1, 1) \/ Send2b(1, 1, 2) \/ Send2b(1, 1, 3)
    \/ Send2b(1, 2, 1) \/ Send2b(1, 2, 2) \/ Send2b(1, 2, 3)
    \/ Send2b(1, 3, 1) \/ Send2b(1, 3, 2) \/ Send2b(1, 3, 3)
    \/ Send2b(2, 1, 1) \/ Send2b(2, 1, 2) \/ Send2b(2, 1, 3)
    \/ Send2b(2, 2, 1) \/ Send2b(2, 2, 2) \/ Send2b(2, 2, 3)
    \/ Send2b(2, 3, 1) \/ Send2b(2, 3, 2) \/ Send2b(2, 3, 3)
    \/ Send2b(3, 1, 1) \/ Send2b(3, 1, 2) \/ Send2b(3, 1, 3)
    \/ Send2b(3, 2, 1) \/ Send2b(3, 2, 2) \/ Send2b(3, 2, 3)
    \/ Send2b(3, 3, 1) \/ Send2b(3, 3, 2) \/ Send2b(3, 3, 3)

ChosenValueAgreement ==
    \A v1, v2 \in maxVal : v1 = v2

TypeOK ==
    /\ maxBal \subseteq Acceptors
    /\ maxVBal \subseteq Acceptors
    /\ maxVal \subseteq Values

================================================================================
