---- MODULE Configuration ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Configuration, AbstractEndPoint

Configuration ==
    [clientIds |-> SUBSET AbstractEndPoint, replica_ids |-> Seq(AbstractEndPoint)]

MinQuorumSize(c) ==
    (Len(c.replica_ids) \div 2) + 1

ReplicasDistinct(replica_ids, i, j) ==
    (0 <= i /\ i < Len(replica_ids) /\ 0 <= j /\ j < Len(replica_ids) /\ replica_ids[i] = replica_ids[j]) => i = j

ReplicasIsUnique(replica_ids) ==
    \A i \in Int, j \in Int : (0 <= i /\ i < Len(replica_ids) /\ 0 <= j /\ j < Len(replica_ids) /\ replica_ids[i] = replica_ids[j]) => i = j

WellFormedLConfiguration(c) ==
    /\ 0 < Len(c.replica_ids)
    /\ \A i \in Int, j \in Int : ReplicasDistinct(c.replica_ids, i, j)
    /\ ReplicasIsUnique(c.replica_ids)

IsReplicaIndex(idx, id, c) ==
    /\ 0 <= idx
    /\ idx < Len(c.replica_ids)
    /\ c.replica_ids[idx] = id

GetReplicaIndex(id, c) ==
    FindIndexInSeq(c.replica_ids, id)

====
