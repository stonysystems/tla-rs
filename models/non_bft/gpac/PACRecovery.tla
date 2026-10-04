------------------------- MODULE PACRecovery -------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* PAC, Algorithm 3, PVLDB 2019, and its PVLDB 2021 erratum.
\* Election collects a quorum atomically. All initial votes are commit.
\* This model isolates the recovery-value selection defect. It does not
\* model the full sharded G-PAC protocol or an explicit message network.
CONSTANT Corrected
Nodes == 1..5
Ballots == 1..3
None == 0
Abort == 1
Commit == 2

VARIABLES promised, acceptedBallot, acceptedValue, decided,
          proposal, votes, step
vars == <<promised, acceptedBallot, acceptedValue, decided,
          proposal, votes, step>>

Quorum(q) == q \subseteq Nodes /\ Cardinality(q) >= 3

Init == /\ promised = [a \in Nodes |-> 0]
        /\ acceptedBallot = [a \in Nodes |-> 0]
        /\ acceptedValue = [a \in Nodes |-> None]
        /\ decided = [a \in Nodes |-> None]
        /\ proposal = [b \in Ballots |-> None]
        /\ votes = [b \in Ballots |-> {}]
        /\ step = 0

DecidedResponders(q) == {a \in q: decided[a] # None}
AcceptedResponders(q) == {a \in q: acceptedValue[a] # None}
Highest(q) == CHOOSE a \in AcceptedResponders(q):
                 \A c \in AcceptedResponders(q):
                   acceptedBallot[c] <= acceptedBallot[a]

RecoveryValue(q) ==
  IF DecidedResponders(q) # {}
  THEN decided[CHOOSE a \in DecidedResponders(q): TRUE]
  ELSE IF Corrected /\ AcceptedResponders(q) # {}
       THEN acceptedValue[Highest(q)]
       ELSE IF ~Corrected /\ (\E a \in q: acceptedValue[a] = Commit)
            THEN Commit
            ELSE IF q = Nodes THEN Commit ELSE Abort

Elect(b, q) == /\ Quorum(q)
               /\ proposal[b] = None
               /\ \A a \in q: b > promised[a]
               /\ promised' = [a \in Nodes |->
                                 IF a \in q THEN b ELSE promised[a]]
               /\ proposal' = [proposal EXCEPT ![b] = RecoveryValue(q)]
               /\ UNCHANGED <<acceptedBallot, acceptedValue, decided, votes>>

Accept(b, a) == /\ proposal[b] # None
                /\ b >= promised[a]
                /\ decided[a] = None
                /\ promised' = [promised EXCEPT ![a] = b]
                /\ acceptedBallot' = [acceptedBallot EXCEPT ![a] = b]
                /\ acceptedValue' = [acceptedValue EXCEPT ![a] = proposal[b]]
                /\ votes' = [votes EXCEPT ![b] = @ \cup {a}]
                /\ UNCHANGED <<proposal, decided>>

Decide(b, a) == /\ Quorum(votes[b])
                /\ acceptedBallot[a] = b
                /\ decided[a] = None
                /\ decided' = [decided EXCEPT ![a] = proposal[b]]
                /\ UNCHANGED <<promised, acceptedBallot, acceptedValue,
                                proposal, votes>>

\* The published witness, using C1=1, C2=2 and C3=3. Leader 1
\* stops after one acceptance; leader 2 stops after delivering one
\* decision. Delayed nodes can reappear. No Byzantine behavior occurs.
ReplayNext == /\ step' = step + 1
              /\ CASE step = 0 -> Elect(1, Nodes)
                   [] step = 1 -> Accept(1, 1)
                   [] step = 2 -> Elect(2, {2, 3, 4})
                   [] step = 3 -> Accept(2, 2)
                   [] step = 4 -> Accept(2, 3)
                   [] step = 5 -> Accept(2, 4)
                   [] step = 6 -> Decide(2, 2)
                   [] step = 7 -> Elect(3, {1, 3, 4})
                   [] step = 8 -> Accept(3, 1)
                   [] step = 9 -> Accept(3, 3)
                   [] step = 10 -> Accept(3, 4)
                   [] step = 11 -> Decide(3, 3)
                   [] OTHER -> FALSE

Agreement == \A a, b \in Nodes:
                (decided[a] # None /\ decided[b] # None)
                => decided[a] = decided[b]
TypeOK == /\ promised \in [Nodes -> 0..3]
          /\ acceptedBallot \in [Nodes -> 0..3]
          /\ acceptedValue \in [Nodes -> 0..2]
          /\ decided \in [Nodes -> 0..2]
          /\ proposal \in [Ballots -> 0..2]
          /\ votes \in [Ballots -> SUBSET Nodes]
          /\ step \in 0..12

\* Also checks that the correction does not merely stop the replay early.
ReplayCompletes == <>(step = 12)
Spec == Init /\ [][ReplayNext]_vars /\ WF_vars(ReplayNext)
======================================================================
