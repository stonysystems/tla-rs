---- MODULE EPaxos ----
\* LLM-generated Egalitarian Paxos specification.
\* Models leaderless consensus with fast/slow commit paths and dependency tracking.

EXTENDS Naturals, FiniteSets

CONSTANTS Replica, MaxCmd, MaxBallot

\* Derived constants
N == Cardinality(Replica)
FastQuorum == (3 * N) \div 4 + 1
SlowQuorum == N \div 2 + 1

\* Phase tags
Empty       == "empty"
PreAccepted == "preaccepted"
Accepted    == "accepted"
CommittedP  == "committed"
ExecutedP   == "executed"

VARIABLE ballot, phase, cmd, seq, isLeader,
         preacceptSenders, acceptSenders, hasConflict,
         committedCount, executedCount, maxRespSeq

Init ==
    /\ ballot          = [r \in Replica |-> 0]
    /\ phase           = [r \in Replica |-> Empty]
    /\ cmd             = [r \in Replica |-> 0]
    /\ seq             = [r \in Replica |-> 0]
    /\ isLeader        = [r \in Replica |-> FALSE]
    /\ preacceptSenders = [r \in Replica |-> {}]
    /\ acceptSenders   = [r \in Replica |-> {}]
    /\ hasConflict     = [r \in Replica |-> FALSE]
    /\ committedCount  = [r \in Replica |-> 0]
    /\ executedCount   = [r \in Replica |-> 0]
    /\ maxRespSeq      = [r \in Replica |-> 0]

\* --- Pre-Accept Phase ---

\* Leader proposes a new command instance
Propose(leader, value) ==
    /\ phase[leader] = Empty
    /\ value \in 1..MaxCmd
    /\ ballot'          = [ballot EXCEPT ![leader] = ballot[leader]]
    /\ phase'           = [phase EXCEPT ![leader] = PreAccepted]
    /\ cmd'             = [cmd EXCEPT ![leader] = value]
    /\ seq'             = [seq EXCEPT ![leader] = committedCount[leader] + 1]
    /\ isLeader'        = [isLeader EXCEPT ![leader] = TRUE]
    /\ preacceptSenders' = [preacceptSenders EXCEPT ![leader] = {leader}]
    /\ acceptSenders'   = [acceptSenders EXCEPT ![leader] = {}]
    /\ hasConflict'     = [hasConflict EXCEPT ![leader] = FALSE]
    /\ maxRespSeq'      = [maxRespSeq EXCEPT ![leader] = 0]
    /\ UNCHANGED <<committedCount, executedCount>>

\* Replica receives pre-accept and responds (may report conflict)
ReceivePreAcceptOk(leader, responder, respSeq, conflict) ==
    /\ phase[leader] = PreAccepted
    /\ isLeader[leader] = TRUE
    /\ responder \in Replica
    /\ responder # leader
    /\ ~(responder \in preacceptSenders[leader])
    /\ respSeq \in 0..MaxCmd
    /\ preacceptSenders' = [preacceptSenders EXCEPT ![leader] =
        preacceptSenders[leader] \cup {responder}]
    /\ hasConflict' = [hasConflict EXCEPT ![leader] =
        IF conflict THEN TRUE ELSE hasConflict[leader]]
    /\ seq' = [seq EXCEPT ![leader] =
        IF respSeq > seq[leader] THEN respSeq ELSE seq[leader]]
    /\ maxRespSeq' = [maxRespSeq EXCEPT ![leader] =
        IF respSeq > maxRespSeq[leader] THEN respSeq ELSE maxRespSeq[leader]]
    /\ UNCHANGED <<ballot, phase, cmd, isLeader, acceptSenders,
                   committedCount, executedCount>>

\* --- Fast Path ---

FastCommit(leader) ==
    /\ phase[leader] = PreAccepted
    /\ isLeader[leader] = TRUE
    /\ Cardinality(preacceptSenders[leader]) >= FastQuorum
    /\ hasConflict[leader] = FALSE
    /\ phase'          = [phase EXCEPT ![leader] = CommittedP]
    /\ committedCount' = [committedCount EXCEPT ![leader] = committedCount[leader] + 1]
    /\ UNCHANGED <<ballot, cmd, seq, isLeader, preacceptSenders,
                   acceptSenders, hasConflict, executedCount, maxRespSeq>>

\* --- Slow Path ---

StartAccept(leader) ==
    /\ phase[leader] = PreAccepted
    /\ isLeader[leader] = TRUE
    /\ Cardinality(preacceptSenders[leader]) >= SlowQuorum
    /\ hasConflict[leader] = TRUE
    /\ phase'         = [phase EXCEPT ![leader] = Accepted]
    /\ acceptSenders' = [acceptSenders EXCEPT ![leader] = {leader}]
    /\ UNCHANGED <<ballot, cmd, seq, isLeader, preacceptSenders,
                   hasConflict, committedCount, executedCount, maxRespSeq>>

ReceiveAcceptOk(leader, responder) ==
    /\ phase[leader] = Accepted
    /\ isLeader[leader] = TRUE
    /\ responder \in Replica
    /\ ~(responder \in acceptSenders[leader])
    /\ acceptSenders' = [acceptSenders EXCEPT ![leader] =
        acceptSenders[leader] \cup {responder}]
    /\ UNCHANGED <<ballot, phase, cmd, seq, isLeader, preacceptSenders,
                   hasConflict, committedCount, executedCount, maxRespSeq>>

SlowCommit(leader) ==
    /\ phase[leader] = Accepted
    /\ isLeader[leader] = TRUE
    /\ Cardinality(acceptSenders[leader]) >= SlowQuorum
    /\ phase'          = [phase EXCEPT ![leader] = CommittedP]
    /\ committedCount' = [committedCount EXCEPT ![leader] = committedCount[leader] + 1]
    /\ UNCHANGED <<ballot, cmd, seq, isLeader, preacceptSenders,
                   acceptSenders, hasConflict, executedCount, maxRespSeq>>

\* --- Execution and Recovery ---

Execute(r) ==
    /\ phase[r] = CommittedP
    /\ phase'         = [phase EXCEPT ![r] = ExecutedP]
    /\ executedCount' = [executedCount EXCEPT ![r] = executedCount[r] + 1]
    /\ UNCHANGED <<ballot, cmd, seq, isLeader, preacceptSenders,
                   acceptSenders, hasConflict, committedCount, maxRespSeq>>

Recover(r, newBallot) ==
    /\ phase[r] \in {PreAccepted, Accepted}
    /\ newBallot > ballot[r]
    /\ newBallot \in 1..MaxBallot
    /\ ballot'          = [ballot EXCEPT ![r] = newBallot]
    /\ phase'           = [phase EXCEPT ![r] = PreAccepted]
    /\ isLeader'        = [isLeader EXCEPT ![r] = TRUE]
    /\ preacceptSenders' = [preacceptSenders EXCEPT ![r] = {r}]
    /\ acceptSenders'   = [acceptSenders EXCEPT ![r] = {}]
    /\ hasConflict'     = [hasConflict EXCEPT ![r] = FALSE]
    /\ maxRespSeq'      = [maxRespSeq EXCEPT ![r] = 0]
    /\ UNCHANGED <<cmd, seq, committedCount, executedCount>>

NewInstance(r) ==
    /\ phase[r] = ExecutedP
    /\ phase'           = [phase EXCEPT ![r] = Empty]
    /\ cmd'             = [cmd EXCEPT ![r] = 0]
    /\ seq'             = [seq EXCEPT ![r] = 0]
    /\ isLeader'        = [isLeader EXCEPT ![r] = FALSE]
    /\ preacceptSenders' = [preacceptSenders EXCEPT ![r] = {}]
    /\ acceptSenders'   = [acceptSenders EXCEPT ![r] = {}]
    /\ hasConflict'     = [hasConflict EXCEPT ![r] = FALSE]
    /\ maxRespSeq'      = [maxRespSeq EXCEPT ![r] = 0]
    /\ UNCHANGED <<ballot, committedCount, executedCount>>

Next ==
    \/ \E r \in Replica, v \in 1..MaxCmd : Propose(r, v)
    \/ \E l, r \in Replica, s \in 0..MaxCmd, c \in BOOLEAN : ReceivePreAcceptOk(l, r, s, c)
    \/ \E r \in Replica : FastCommit(r)
    \/ \E r \in Replica : StartAccept(r)
    \/ \E l, r \in Replica : ReceiveAcceptOk(l, r)
    \/ \E r \in Replica : SlowCommit(r)
    \/ \E r \in Replica : Execute(r)
    \/ \E r \in Replica, b \in 1..MaxBallot : Recover(r, b)
    \/ \E r \in Replica : NewInstance(r)

vars == <<ballot, phase, cmd, seq, isLeader,
          preacceptSenders, acceptSenders, hasConflict,
          committedCount, executedCount, maxRespSeq>>
Spec == Init /\ [][Next]_vars

\* --- Safety Invariants ---

\* Executed count never exceeds committed count
ExecutedLeqCommitted ==
    \A r \in Replica : executedCount[r] <= committedCount[r]

\* Phase is valid
PhaseValid ==
    \A r \in Replica :
        phase[r] \in {Empty, PreAccepted, Accepted, CommittedP, ExecutedP}

\* Ballot is non-negative
BallotNonNeg ==
    \A r \in Replica : ballot[r] >= 0

\* Pre-accept and accept sender sets only contain valid replicas
SendersValid ==
    \A r \in Replica :
        /\ preacceptSenders[r] \subseteq Replica
        /\ acceptSenders[r] \subseteq Replica

\* Sequence number is non-negative
SeqNonNeg ==
    \A r \in Replica : seq[r] >= 0

====
