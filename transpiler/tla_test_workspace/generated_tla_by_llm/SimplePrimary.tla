---- MODULE SimplePrimary ----
\* LLM-generated simplified primary-backup.
\* Uses flat state variables for parser compatibility.

EXTENDS Naturals

VARIABLE isPrimary, logLen, backupLen, pendingVal, isAcked, viewNum

Init ==
    /\ isPrimary = TRUE
    /\ logLen = 0
    /\ backupLen = 0
    /\ pendingVal = 0
    /\ isAcked = TRUE
    /\ viewNum = 0

Write(val) ==
    /\ isPrimary = TRUE
    /\ isAcked = TRUE
    /\ pendingVal' = val
    /\ isAcked' = FALSE
    /\ isPrimary' = isPrimary
    /\ logLen' = logLen
    /\ backupLen' = backupLen
    /\ viewNum' = viewNum

Replicate ==
    /\ isPrimary = TRUE
    /\ isAcked = FALSE
    /\ backupLen' = backupLen + 1
    /\ isPrimary' = isPrimary
    /\ logLen' = logLen
    /\ pendingVal' = pendingVal
    /\ isAcked' = isAcked
    /\ viewNum' = viewNum

Acknowledge ==
    /\ isPrimary = TRUE
    /\ isAcked = FALSE
    /\ backupLen > logLen
    /\ isAcked' = TRUE
    /\ isPrimary' = isPrimary
    /\ logLen' = logLen
    /\ backupLen' = backupLen
    /\ pendingVal' = pendingVal
    /\ viewNum' = viewNum

Commit ==
    /\ isPrimary = TRUE
    /\ isAcked = TRUE
    /\ pendingVal > 0
    /\ logLen' = logLen + 1
    /\ pendingVal' = 0
    /\ isPrimary' = isPrimary
    /\ backupLen' = backupLen
    /\ isAcked' = isAcked
    /\ viewNum' = viewNum

Failover ==
    /\ isPrimary = TRUE
    /\ isPrimary' = FALSE
    /\ logLen' = logLen
    /\ backupLen' = backupLen
    /\ pendingVal' = 0
    /\ isAcked' = TRUE
    /\ viewNum' = viewNum + 1

Next == Replicate \/ Acknowledge \/ Commit \/ Failover

====
