---- MODULE Primarybackup ----
\* Hand-written single-node Primary-Backup spec for DPOR case 16.
\* Replaces the prior verus2tla-emitted parameterized Init/Next that TLC
\* could not enumerate (untyped record-tag access on s.role.tag).
\*
\* Models one node's local view in a Primary-Backup pair. The node's
\* role transitions Primary -> Inactive on PrimaryFail and Inactive ->
\* Primary on BackupPromote. Backup state fields (backup_log_length /
\* backup_last_value / backup_synced) track the local node's view of
\* its peer.

EXTENDS Naturals, FiniteSets

VARIABLE role, log_length, last_value,
         has_pending, pending_value, acked,
         backup_log_length, backup_last_value, backup_synced, view

\* Role encoded as a small integer to avoid TLC model-value pitfalls:
\*   1 = Primary, 2 = Backup, 3 = Inactive
Primary  == 1
Backup   == 2
Inactive == 3
Roles    == {Primary, Backup, Inactive}

Values    == {1, 2}
MaxLogLen == 3

Init ==
    /\ role = Primary
    /\ log_length = 0
    /\ last_value = 0
    /\ has_pending = FALSE
    /\ pending_value = 0
    /\ acked = TRUE
    /\ backup_log_length = 0
    /\ backup_last_value = 0
    /\ backup_synced = TRUE
    /\ view = 0

PrimaryWrite(val) ==
    /\ role = Primary
    /\ acked = TRUE
    /\ has_pending = FALSE
    /\ log_length < MaxLogLen
    /\ has_pending' = TRUE
    /\ pending_value' = val
    /\ acked' = FALSE
    /\ role' = role
    /\ log_length' = log_length
    /\ last_value' = last_value
    /\ backup_log_length' = backup_log_length
    /\ backup_last_value' = backup_last_value
    /\ backup_synced' = backup_synced
    /\ view' = view

PrimarySendReplicate ==
    /\ role = Primary
    /\ has_pending = TRUE
    /\ acked = FALSE
    /\ UNCHANGED <<role, log_length, last_value, has_pending, pending_value,
                   acked, backup_log_length, backup_last_value, backup_synced,
                   view>>

BackupReceiveReplicate(val) ==
    /\ role = Primary
    /\ backup_log_length < MaxLogLen + 1
    /\ backup_log_length' = backup_log_length + 1
    /\ backup_last_value' = val
    /\ backup_synced' = TRUE
    /\ role' = role
    /\ log_length' = log_length
    /\ last_value' = last_value
    /\ has_pending' = has_pending
    /\ pending_value' = pending_value
    /\ acked' = acked
    /\ view' = view

BackupSendAck ==
    /\ role = Primary
    /\ backup_synced = TRUE
    /\ UNCHANGED <<role, log_length, last_value, has_pending, pending_value,
                   acked, backup_log_length, backup_last_value, backup_synced,
                   view>>

PrimaryReceiveAck ==
    /\ role = Primary
    /\ has_pending = TRUE
    /\ acked' = TRUE
    /\ role' = role
    /\ log_length' = log_length
    /\ last_value' = last_value
    /\ has_pending' = has_pending
    /\ pending_value' = pending_value
    /\ backup_log_length' = backup_log_length
    /\ backup_last_value' = backup_last_value
    /\ backup_synced' = backup_synced
    /\ view' = view

PrimaryCommit ==
    /\ role = Primary
    /\ acked = TRUE
    /\ has_pending = TRUE
    /\ log_length' = log_length + 1
    /\ last_value' = pending_value
    /\ has_pending' = FALSE
    /\ pending_value' = 0
    /\ acked' = TRUE
    /\ role' = role
    /\ backup_log_length' = backup_log_length
    /\ backup_last_value' = backup_last_value
    /\ backup_synced' = backup_synced
    /\ view' = view

PrimaryFail ==
    /\ role = Primary
    /\ view < 2
    /\ role' = Inactive
    /\ has_pending' = FALSE
    /\ pending_value' = 0
    /\ acked' = TRUE
    /\ log_length' = log_length
    /\ last_value' = last_value
    /\ backup_log_length' = backup_log_length
    /\ backup_last_value' = backup_last_value
    /\ backup_synced' = FALSE
    /\ view' = view

BackupPromote ==
    /\ role = Inactive
    /\ role' = Primary
    /\ log_length' = backup_log_length
    /\ last_value' = backup_last_value
    /\ has_pending' = FALSE
    /\ pending_value' = 0
    /\ acked' = TRUE
    /\ backup_log_length' = backup_log_length
    /\ backup_last_value' = backup_last_value
    /\ backup_synced' = TRUE
    /\ view' = view + 1

Next ==
    \/ \E v \in Values : PrimaryWrite(v)
    \/ PrimarySendReplicate
    \/ \E v \in Values : BackupReceiveReplicate(v)
    \/ BackupSendAck
    \/ PrimaryReceiveAck
    \/ PrimaryCommit
    \/ PrimaryFail
    \/ BackupPromote

SafetyNoPendingImpliesClearedValue ==
    ~has_pending => pending_value = 0

SafetyUnackedImpliesPending ==
    ~acked => has_pending

SafetyInactiveStateIsQuiescent ==
    role = Inactive => (~has_pending /\ acked /\ ~backup_synced)

TypeOK ==
    /\ role \in Roles
    /\ log_length \in 0..MaxLogLen
    /\ last_value \in (Values \cup {0})
    /\ has_pending \in BOOLEAN
    /\ pending_value \in (Values \cup {0})
    /\ acked \in BOOLEAN
    /\ backup_log_length \in 0..(MaxLogLen + 1)
    /\ backup_last_value \in (Values \cup {0})
    /\ backup_synced \in BOOLEAN
    /\ view \in Nat

================================================================================
