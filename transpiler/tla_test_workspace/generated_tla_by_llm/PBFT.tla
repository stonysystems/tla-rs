---- MODULE PBFT ----
\* LLM-generated Practical Byzantine Fault Tolerance specification.
\* Models normal-case operation and view changes for BFT consensus.

EXTENDS Naturals, FiniteSets

CONSTANTS Replica, F, MaxSeq, MaxView

\* Derived constants
N == Cardinality(Replica)

\* Phase tags
Idle       == "idle"
PrePrepare == "pre-prepare"
Prepare    == "prepare"
Commit     == "commit"
Committed  == "committed"

VARIABLE view, seqNum, phase, prepareMsgs, commitMsgs, executed, isPrimary

\* Primary for a given view: deterministic selection
PrimaryOf(v) == CHOOSE r \in Replica : \A s \in Replica : r <= s

Init ==
    /\ view        = [r \in Replica |-> 0]
    /\ seqNum      = 0
    /\ phase       = [r \in Replica |-> Idle]
    /\ prepareMsgs = [r \in Replica |-> {}]
    /\ commitMsgs  = [r \in Replica |-> {}]
    /\ executed    = [r \in Replica |-> 0]
    /\ isPrimary   = [r \in Replica |-> r = PrimaryOf(0)]

\* --- Normal Case ---

\* Primary assigns sequence number and sends pre-prepare
SendPrePrepare(p) ==
    /\ isPrimary[p] = TRUE
    /\ phase[p] = Idle
    /\ seqNum < MaxSeq
    /\ seqNum' = seqNum + 1
    /\ phase' = [phase EXCEPT ![p] = PrePrepare]
    /\ UNCHANGED <<view, prepareMsgs, commitMsgs, executed, isPrimary>>

\* Backup receives pre-prepare from primary and enters prepare phase
ReceivePrePrepare(r) ==
    /\ isPrimary[r] = FALSE
    /\ phase[r] = Idle
    /\ \E p \in Replica : isPrimary[p] /\ phase[p] = PrePrepare
    /\ phase' = [phase EXCEPT ![r] = Prepare]
    /\ UNCHANGED <<view, seqNum, prepareMsgs, commitMsgs, executed, isPrimary>>

\* Replica sends prepare message (collecting from other replicas)
SendPrepare(sender, receiver) ==
    /\ sender # receiver
    /\ phase[sender] \in {PrePrepare, Prepare}
    /\ prepareMsgs' = [prepareMsgs EXCEPT ![receiver] = prepareMsgs[receiver] \cup {sender}]
    /\ UNCHANGED <<view, seqNum, phase, commitMsgs, executed, isPrimary>>

\* Replica enters commit phase after receiving 2f prepares
EnterCommit(r) ==
    /\ phase[r] \in {PrePrepare, Prepare}
    /\ Cardinality(prepareMsgs[r]) >= 2 * F
    /\ phase' = [phase EXCEPT ![r] = Commit]
    /\ UNCHANGED <<view, seqNum, prepareMsgs, commitMsgs, executed, isPrimary>>

\* Replica sends commit message
SendCommit(sender, receiver) ==
    /\ sender # receiver
    /\ phase[sender] = Commit
    /\ commitMsgs' = [commitMsgs EXCEPT ![receiver] = commitMsgs[receiver] \cup {sender}]
    /\ UNCHANGED <<view, seqNum, phase, prepareMsgs, executed, isPrimary>>

\* Replica executes after receiving 2f+1 commits
ExecuteRequest(r) ==
    /\ phase[r] = Commit
    /\ Cardinality(commitMsgs[r]) >= 2 * F + 1
    /\ phase'    = [phase EXCEPT ![r] = Committed]
    /\ executed' = [executed EXCEPT ![r] = executed[r] + 1]
    /\ UNCHANGED <<view, seqNum, prepareMsgs, commitMsgs, isPrimary>>

\* Reset for next request
ResetForNext(r) ==
    /\ phase[r] = Committed
    /\ phase'       = [phase EXCEPT ![r] = Idle]
    /\ prepareMsgs' = [prepareMsgs EXCEPT ![r] = {}]
    /\ commitMsgs'  = [commitMsgs EXCEPT ![r] = {}]
    /\ UNCHANGED <<view, seqNum, executed, isPrimary>>

\* --- View Change ---

ViewChange(r) ==
    /\ view[r] < MaxView
    /\ view'      = [view EXCEPT ![r] = view[r] + 1]
    /\ isPrimary' = [isPrimary EXCEPT ![r] = r = PrimaryOf(view[r] + 1)]
    /\ phase'     = [phase EXCEPT ![r] = Idle]
    /\ prepareMsgs' = [prepareMsgs EXCEPT ![r] = {}]
    /\ commitMsgs'  = [commitMsgs EXCEPT ![r] = {}]
    /\ UNCHANGED <<seqNum, executed>>

Next ==
    \/ \E p \in Replica : SendPrePrepare(p)
    \/ \E r \in Replica : ReceivePrePrepare(r)
    \/ \E s, r \in Replica : SendPrepare(s, r)
    \/ \E r \in Replica : EnterCommit(r)
    \/ \E s, r \in Replica : SendCommit(s, r)
    \/ \E r \in Replica : ExecuteRequest(r)
    \/ \E r \in Replica : ResetForNext(r)
    \/ \E r \in Replica : ViewChange(r)

vars == <<view, seqNum, phase, prepareMsgs, commitMsgs, executed, isPrimary>>
Spec == Init /\ [][Next]_vars

\* --- Safety Invariants ---

\* Agreement: all correct replicas execute the same number of requests (within 1)
Agreement ==
    \A r1, r2 \in Replica :
        executed[r1] <= executed[r2] + 1

\* At most one primary per view among replicas in the same view
UniquePrimary ==
    \A r1, r2 \in Replica :
        (isPrimary[r1] /\ isPrimary[r2] /\ view[r1] = view[r2]) => r1 = r2

\* Commit requires sufficient prepares
CommitRequiresPrepares ==
    \A r \in Replica :
        phase[r] = Commit => Cardinality(prepareMsgs[r]) >= 2 * F

\* Sequence number never exceeds maximum
SeqBounded ==
    seqNum <= MaxSeq

\* View is bounded
ViewBounded ==
    \A r \in Replica : view[r] <= MaxView

====
