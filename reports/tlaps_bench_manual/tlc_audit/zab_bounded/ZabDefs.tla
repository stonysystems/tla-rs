--------------------------- MODULE ZabDefs ---------------------------

EXTENDS ZabModel

Minimum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S: \A m \in S: n <= m

TxnEqual(txn1, txn2) == /\ ZxidEqual(txn1.zxid, txn2.zxid)
                        /\ txn1.value = txn2.value

EpochPrecedeInTxn(txn1, txn2) == txn1.zxid[1] < txn2.zxid[1]

Leadership1 == \A i, j \in Server:
                   /\ IsLeader(i) /\ zabState[i] \in {SYNCHRONIZATION, BROADCAST}
                   /\ IsLeader(j) /\ zabState[j] \in {SYNCHRONIZATION, BROADCAST}
                   /\ currentEpoch[i] = currentEpoch[j]
                  => i = j

Leadership2 == \A epoch \in 1..MAXEPOCH: Cardinality(epochLeader[epoch]) <= 1

PrefixConsistency == \A i, j \in Server:
                        LET smaller == Minimum({lastCommitted[i].index, lastCommitted[j].index})
                        IN \/ smaller = 0
                           \/ /\ smaller > 0
                              /\ \A index \in 1..smaller:
                                   TxnEqual(history[i][index], history[j][index])

Integrity == \A i \in Server:
                /\ IsFollower(i)
                /\ lastCommitted[i].index > 0
                => \A idx \in 1..lastCommitted[i].index: \E proposal \in proposalMsgsLog:
                    LET txn_proposal == [ zxid  |-> proposal.zxid,
                                          value |-> proposal.data ]
                    IN  TxnEqual(history[i][idx], txn_proposal)

Agreement == \A i, j \in Server:
                /\ IsFollower(i) /\ lastCommitted[i].index > 0
                /\ IsFollower(j) /\ lastCommitted[j].index > 0
                =>
                \A idx1 \in 1..lastCommitted[i].index, idx2 \in 1..lastCommitted[j].index :
                    \/ \E idx_j \in 1..lastCommitted[j].index:
                        TxnEqual(history[j][idx_j], history[i][idx1])
                    \/ \E idx_i \in 1..lastCommitted[i].index:
                        TxnEqual(history[i][idx_i], history[j][idx2])

TotalOrder == \A i, j \in Server: 
                LET committed1 == lastCommitted[i].index 
                    committed2 == lastCommitted[j].index  
                IN committed1 >= 2 /\ committed2 >= 2
                    => \A idx_i1 \in 1..(committed1 - 1) : \A idx_i2 \in (idx_i1 + 1)..committed1 :
                    LET logOk == \E idx \in 1..committed2 :
                                     TxnEqual(history[i][idx_i2], history[j][idx])
                    IN \/ ~logOk 
                       \/ /\ logOk 
                          /\ \E idx_j2 \in 1..committed2 : 
                                /\ TxnEqual(history[i][idx_i2], history[j][idx_j2])
                                /\ \E idx_j1 \in 1..(idx_j2 - 1):
                                       TxnEqual(history[i][idx_i1], history[j][idx_j1])

LocalPrimaryOrder == LET p_set(i, e) == {p \in proposalMsgsLog: /\ p.source = i 
                                                                /\ p.epoch  = e }
                         txn_set(i, e) == { [ zxid  |-> p.zxid, 
                                              value |-> p.data ] : p \in p_set(i, e) }
                     IN \A i \in Server: \A e \in 1..currentEpoch[i]:
                         \/ Cardinality(txn_set(i, e)) < 2
                         \/ /\ Cardinality(txn_set(i, e)) >= 2
                            /\ \A txn1, txn2 \in txn_set(i, e):
                             \/ TxnEqual(txn1, txn2)
                             \/ /\ ~TxnEqual(txn1, txn2)
                                /\ LET TxnPre  == IF ZxidCompare(txn1.zxid, txn2.zxid) THEN txn2 ELSE txn1
                                       TxnNext == IF ZxidCompare(txn1.zxid, txn2.zxid) THEN txn1 ELSE txn2
                                   IN \A j \in Server: (\E idx \in 1..lastCommitted[j].index: 
                                                            TxnEqual(history[j][idx], TxnNext))
                                        => \E idx2 \in 1..lastCommitted[j].index: 
                                            /\ TxnEqual(history[j][idx2], TxnNext)
                                            /\ idx2 > 1
                                            /\ \E idx1 \in 1..(idx2 - 1): 
                                                TxnEqual(history[j][idx1], TxnPre)

GlobalPrimaryOrder == \A i \in Server: lastCommitted[i].index >= 2
                         => \A idx1, idx2 \in 1..lastCommitted[i].index:
                                \/ ~EpochPrecedeInTxn(history[i][idx1], history[i][idx2])
                                \/ /\ EpochPrecedeInTxn(history[i][idx1], history[i][idx2])
                                   /\ idx1 < idx2

PrimaryIntegrity == \A i, j \in Server: /\ IsLeader(i)   /\ IsMyLearner(i, j)
                                        /\ IsFollower(j) /\ IsMyLeader(j, i)
                                        /\ zabState[i] = BROADCAST
                                        /\ zabState[j] = BROADCAST
                                        /\ lastCommitted[j].index >= 1
                        => \A idx_j \in 1..lastCommitted[j].index:
                                \/ history[j][idx_j].zxid[1] >= currentEpoch[i]
                                \/ /\ history[j][idx_j].zxid[1] < currentEpoch[i]
                                   /\ \E idx_i \in 1..lastCommitted[i].index: 
                                        TxnEqual(history[i][idx_i], history[j][idx_j])

=============================================================================
