---- MODULE PrimaryBackup ----
\* LLM-generated Primary-Backup replication specification.
\* Models primary replication to backup with failover.

EXTENDS Naturals, Sequences

CONSTANT MaxVal

VARIABLE role, primaryLog, backupLog, pending, acked, view

Primary == "primary"
Backup == "backup"
Inactive == "inactive"

Init ==
    /\ role = Primary
    /\ primaryLog = <<>>
    /\ backupLog = <<>>
    /\ pending = 0
    /\ acked = TRUE
    /\ view = 0

PrimaryWrite(val) ==
    /\ role = Primary
    /\ acked = TRUE
    /\ pending' = val
    /\ acked' = FALSE
    /\ UNCHANGED <<role, primaryLog, backupLog, view>>

PrimarySendReplicate ==
    /\ role = Primary
    /\ acked = FALSE
    /\ pending # 0
    /\ UNCHANGED <<role, primaryLog, backupLog, pending, acked, view>>

BackupReceiveReplicate ==
    /\ role = Primary
    /\ acked = FALSE
    /\ backupLog' = Append(backupLog, pending)
    /\ UNCHANGED <<role, primaryLog, pending, acked, view>>

BackupSendAck ==
    /\ role = Primary
    /\ acked = FALSE
    /\ Len(backupLog) > Len(primaryLog)
    /\ acked' = TRUE
    /\ UNCHANGED <<role, primaryLog, backupLog, pending, view>>

PrimaryCommit ==
    /\ role = Primary
    /\ acked = TRUE
    /\ pending # 0
    /\ primaryLog' = Append(primaryLog, pending)
    /\ pending' = 0
    /\ UNCHANGED <<role, backupLog, acked, view>>

PrimaryFail ==
    /\ role = Primary
    /\ role' = Inactive
    /\ pending' = 0
    /\ acked' = TRUE
    /\ UNCHANGED <<primaryLog, backupLog, view>>

BackupPromote ==
    /\ role = Inactive
    /\ role' = Primary
    /\ primaryLog' = backupLog
    /\ pending' = 0
    /\ acked' = TRUE
    /\ view' = view + 1
    /\ UNCHANGED backupLog

Next ==
    \/ \E v \in 1..MaxVal : PrimaryWrite(v)
    \/ PrimarySendReplicate
    \/ BackupReceiveReplicate
    \/ BackupSendAck
    \/ PrimaryCommit
    \/ PrimaryFail
    \/ BackupPromote

Spec == Init /\ [][Next]_<<role, primaryLog, backupLog, pending, acked, view>>

BackupPrefix == \A i \in 1..Len(backupLog) :
    i <= Len(primaryLog) => backupLog[i] = primaryLog[i]

====
