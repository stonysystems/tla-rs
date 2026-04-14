-------------------------------- MODULE PBFT --------------------------------
\* PBFT model for DPOR case 18.
\* 7 replicas (f=2, quorum=5) for meaningful state space.
\* Multiple sequence numbers and digests for wider exploration.

EXTENDS Naturals

CONSTANT replica, f

VARIABLE view, phase, prepareCount, commitCount

PrePrepare == "pre-prepare"
Prepare == "prepare"
Commit == "commit"
Reply == "reply"

QuorumSize == 2 * f + 1

Init ==
    /\ replica >= 7
    /\ f = 2
    /\ view = 0
    /\ phase = PrePrepare
    /\ prepareCount = 0
    /\ commitCount = 0

SendPrePrepare(v, n, d) ==
    /\ phase = PrePrepare
    /\ v = view
    /\ (n = 0 \/ n = 1 \/ n = 2)
    /\ (d = 0 \/ d = 1 \/ d = 2)
    /\ phase' = Prepare
    /\ view' = view
    /\ prepareCount' = prepareCount
    /\ commitCount' = commitCount

SendPrepare(r, v, n, d) ==
    /\ phase = Prepare
    /\ prepareCount < replica
    /\ r >= 1
    /\ r <= replica
    /\ v = view
    /\ (n = 0 \/ n = 1 \/ n = 2)
    /\ (d = 0 \/ d = 1 \/ d = 2)
    /\ prepareCount' = prepareCount + 1
    /\ phase' = phase
    /\ view' = view
    /\ commitCount' = commitCount

Prepared == prepareCount >= QuorumSize

EnterCommit ==
    /\ Prepared
    /\ phase = Prepare
    /\ phase' = Commit
    /\ view' = view
    /\ prepareCount' = prepareCount
    /\ commitCount' = commitCount

SendCommit(r, v, n, d) ==
    /\ phase = Commit
    /\ Prepared
    /\ commitCount < replica
    /\ r >= 1
    /\ r <= replica
    /\ v = view
    /\ (n = 0 \/ n = 1 \/ n = 2)
    /\ (d = 0 \/ d = 1 \/ d = 2)
    /\ commitCount' = commitCount + 1
    /\ phase' = phase
    /\ view' = view
    /\ prepareCount' = prepareCount

Committed == commitCount >= QuorumSize

ExecuteAndReply ==
    /\ Committed
    /\ phase = Commit
    /\ phase' = Reply
    /\ view' = view
    /\ prepareCount' = prepareCount
    /\ commitCount' = commitCount

ViewChange ==
    /\ view' = view + 1
    /\ phase' = PrePrepare
    /\ prepareCount' = 0
    /\ commitCount' = 0

Next ==
    \/ SendPrePrepare(0, 0, 0) \/ SendPrePrepare(0, 1, 0) \/ SendPrePrepare(0, 2, 0)
    \/ SendPrePrepare(0, 0, 1) \/ SendPrePrepare(0, 1, 1) \/ SendPrePrepare(0, 2, 1)
    \/ SendPrePrepare(0, 0, 2) \/ SendPrePrepare(0, 1, 2) \/ SendPrePrepare(0, 2, 2)
    \/ SendPrepare(1, 0, 0, 0) \/ SendPrepare(2, 0, 0, 0) \/ SendPrepare(3, 0, 0, 0)
    \/ SendPrepare(4, 0, 0, 0) \/ SendPrepare(5, 0, 0, 0) \/ SendPrepare(6, 0, 0, 0)
    \/ SendPrepare(7, 0, 0, 0)
    \/ EnterCommit
    \/ SendCommit(1, 0, 0, 0) \/ SendCommit(2, 0, 0, 0) \/ SendCommit(3, 0, 0, 0)
    \/ SendCommit(4, 0, 0, 0) \/ SendCommit(5, 0, 0, 0) \/ SendCommit(6, 0, 0, 0)
    \/ SendCommit(7, 0, 0, 0)
    \/ ExecuteAndReply
    \/ ViewChange

PBFTSafety ==
    /\ (phase = Commit \/ phase = Reply) => Prepared
    /\ phase = Reply => Committed
    /\ prepareCount <= replica
    /\ commitCount <= replica

TypeOK ==
    /\ view \in Nat
    /\ prepareCount \in Nat
    /\ commitCount \in Nat
    /\ (phase = PrePrepare \/ phase = Prepare \/ phase = Commit \/ phase = Reply)

================================================================================
