-------------------------------- MODULE Paxos --------------------------------
\* Small single-decree Paxos model for DPOR case 17.
\* Fixed 2-acceptor / 2-value bounds keep the model tractable.

EXTENDS Naturals

VARIABLE maxBal, maxVBal, maxVal

Acceptors == {1, 2}
Values == {1, 2}

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

Next ==
    \/ Send1a(1)
    \/ Send1a(2)
    \/ Send1b(1, 1)
    \/ Send1b(1, 2)
    \/ Send1b(2, 1)
    \/ Send1b(2, 2)
    \/ Send2a(1, 1)
    \/ Send2a(1, 2)
    \/ Send2a(2, 1)
    \/ Send2a(2, 2)
    \/ Send2b(1, 1, 1)
    \/ Send2b(1, 1, 2)
    \/ Send2b(1, 2, 1)
    \/ Send2b(1, 2, 2)
    \/ Send2b(2, 1, 1)
    \/ Send2b(2, 1, 2)
    \/ Send2b(2, 2, 1)
    \/ Send2b(2, 2, 2)

ChosenValueAgreement ==
    \A v1, v2 \in maxVal : v1 = v2

TypeOK ==
    /\ maxBal \subseteq Acceptors
    /\ maxVBal \subseteq Acceptors
    /\ maxVal \subseteq Values

================================================================================
