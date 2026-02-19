---- MODULE SimpleEPaxos ----
\* LLM-generated simplified Egalitarian Paxos specification.
\* Models leaderless consensus with conflict-based fast/slow paths.

EXTENDS Naturals, FiniteSets

CONSTANT Replica, MaxCmd

VARIABLE cmdBallot, cmdSeq, cmdStatus, preacceptors, acceptors

StatusNone == "none"
StatusPreAccepted == "preaccepted"
StatusAccepted == "accepted"
StatusCommitted == "committed"

N == Cardinality(Replica)
FastQuorum == (3 * N + 1) \div 4 + 1
SlowQuorum == N \div 2 + 1

Init ==
    /\ cmdBallot = 0
    /\ cmdSeq = 0
    /\ cmdStatus = [r \in Replica |-> StatusNone]
    /\ preacceptors = {}
    /\ acceptors = {}

Propose(leader, seq) ==
    /\ cmdStatus[leader] = StatusNone
    /\ seq <= MaxCmd
    /\ cmdSeq' = seq
    /\ cmdBallot' = cmdBallot + 1
    /\ cmdStatus' = [cmdStatus EXCEPT ![leader] = StatusPreAccepted]
    /\ preacceptors' = {leader}
    /\ UNCHANGED acceptors

PreAcceptOk(replica) ==
    /\ cmdStatus[replica] = StatusNone
    /\ cmdSeq > 0
    /\ cmdStatus' = [cmdStatus EXCEPT ![replica] = StatusPreAccepted]
    /\ preacceptors' = preacceptors \cup {replica}
    /\ UNCHANGED <<cmdBallot, cmdSeq, acceptors>>

FastCommit ==
    /\ Cardinality(preacceptors) >= FastQuorum
    /\ \E r \in Replica : cmdStatus[r] = StatusPreAccepted
    /\ cmdStatus' = [r \in Replica |->
        IF cmdStatus[r] = StatusPreAccepted
        THEN StatusCommitted
        ELSE cmdStatus[r]]
    /\ UNCHANGED <<cmdBallot, cmdSeq, preacceptors, acceptors>>

StartAcceptPhase ==
    /\ Cardinality(preacceptors) >= SlowQuorum
    /\ Cardinality(preacceptors) < FastQuorum
    /\ cmdStatus' = [r \in Replica |->
        IF cmdStatus[r] = StatusPreAccepted
        THEN StatusAccepted
        ELSE cmdStatus[r]]
    /\ acceptors' = preacceptors
    /\ UNCHANGED <<cmdBallot, cmdSeq, preacceptors>>

AcceptOk(replica) ==
    /\ cmdStatus[replica] = StatusNone
    /\ \E r \in Replica : cmdStatus[r] = StatusAccepted
    /\ cmdStatus' = [cmdStatus EXCEPT ![replica] = StatusAccepted]
    /\ acceptors' = acceptors \cup {replica}
    /\ UNCHANGED <<cmdBallot, cmdSeq, preacceptors>>

SlowCommit ==
    /\ Cardinality(acceptors) >= SlowQuorum
    /\ \E r \in Replica : cmdStatus[r] = StatusAccepted
    /\ cmdStatus' = [r \in Replica |->
        IF cmdStatus[r] = StatusAccepted
        THEN StatusCommitted
        ELSE cmdStatus[r]]
    /\ UNCHANGED <<cmdBallot, cmdSeq, preacceptors, acceptors>>

Next ==
    \/ \E r \in Replica, s \in 1..MaxCmd : Propose(r, s)
    \/ \E r \in Replica : PreAcceptOk(r)
    \/ FastCommit
    \/ StartAcceptPhase
    \/ \E r \in Replica : AcceptOk(r)
    \/ SlowCommit

Spec == Init /\ [][Next]_<<cmdBallot, cmdSeq, cmdStatus, preacceptors, acceptors>>

CommitAgreement ==
    \A r1, r2 \in Replica :
        (cmdStatus[r1] = StatusCommitted /\ cmdStatus[r2] = StatusCommitted) =>
        TRUE

====
