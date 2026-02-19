---- MODULE SimplePBFT ----
\* LLM-generated simplified PBFT specification.
\* Models the normal-case operation of Practical Byzantine Fault Tolerance.

EXTENDS Naturals, FiniteSets

CONSTANT Replica, F, MaxSeq

VARIABLE viewNum, seqNum, phase, prepareCount, commitCount, executed

PrePrepare == "pre-prepare"
Prepare == "prepare"
Commit == "commit"
Executed == "executed"
Idle == "idle"

N == Cardinality(Replica)

Primary == CHOOSE r \in Replica : \A s \in Replica : r <= s

Init ==
    /\ viewNum = 0
    /\ seqNum = 0
    /\ phase = [r \in Replica |-> Idle]
    /\ prepareCount = [r \in Replica |-> 0]
    /\ commitCount = [r \in Replica |-> 0]
    /\ executed = [r \in Replica |-> 0]

ReceiveRequest ==
    /\ seqNum < MaxSeq
    /\ phase[Primary] = Idle
    /\ seqNum' = seqNum + 1
    /\ phase' = [phase EXCEPT ![Primary] = PrePrepare]
    /\ UNCHANGED <<viewNum, prepareCount, commitCount, executed>>

ReceivePrePrepare(r) ==
    /\ r # Primary
    /\ phase[Primary] = PrePrepare
    /\ phase[r] = Idle
    /\ phase' = [phase EXCEPT ![r] = Prepare]
    /\ UNCHANGED <<viewNum, seqNum, prepareCount, commitCount, executed>>

ReceivePrepare(r) ==
    /\ phase[r] \in {PrePrepare, Prepare}
    /\ prepareCount' = [prepareCount EXCEPT ![r] = prepareCount[r] + 1]
    /\ IF prepareCount[r] + 1 >= 2 * F
       THEN phase' = [phase EXCEPT ![r] = Commit]
       ELSE phase' = phase
    /\ UNCHANGED <<viewNum, seqNum, commitCount, executed>>

ReceiveCommit(r) ==
    /\ phase[r] = Commit
    /\ commitCount' = [commitCount EXCEPT ![r] = commitCount[r] + 1]
    /\ IF commitCount[r] + 1 >= 2 * F + 1
       THEN /\ phase' = [phase EXCEPT ![r] = Executed]
            /\ executed' = [executed EXCEPT ![r] = executed[r] + 1]
       ELSE /\ phase' = phase
            /\ executed' = executed
    /\ UNCHANGED <<viewNum, seqNum, prepareCount>>

ResetForNextRequest(r) ==
    /\ phase[r] = Executed
    /\ phase' = [phase EXCEPT ![r] = Idle]
    /\ prepareCount' = [prepareCount EXCEPT ![r] = 0]
    /\ commitCount' = [commitCount EXCEPT ![r] = 0]
    /\ UNCHANGED <<viewNum, seqNum, executed>>

Next ==
    \/ ReceiveRequest
    \/ \E r \in Replica : ReceivePrePrepare(r)
    \/ \E r \in Replica : ReceivePrepare(r)
    \/ \E r \in Replica : ReceiveCommit(r)
    \/ \E r \in Replica : ResetForNextRequest(r)

Spec == Init /\ [][Next]_<<viewNum, seqNum, phase, prepareCount, commitCount, executed>>

Safety ==
    \A r1, r2 \in Replica :
        executed[r1] <= executed[r2] + 1 /\ executed[r2] <= executed[r1] + 1

====
