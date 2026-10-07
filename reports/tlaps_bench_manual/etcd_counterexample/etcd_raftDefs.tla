--------------------------------- MODULE etcd_raftDefs ---------------------------------

EXTENDS etcd_raftModel

MaxOrZero(s) == IF s = {} THEN 0 ELSE Max(s)

CurrentLeaders == {i \in Server : state[i] = Leader}

Committed(i) == SubSeq(log[i],1,commitIndex[i])

LogInv ==
    \A i, j \in Server :
        \/ IsPrefix(Committed(i),Committed(j)) 
        \/ IsPrefix(Committed(j),Committed(i))

MoreThanOneLeaderInv ==
    \A i,j \in Server :
        (/\ currentTerm[i] = currentTerm[j]
         /\ state[i] = Leader
         /\ state[j] = Leader)
        => i = j

ElectionSafetyInv ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server :
            MaxOrZero({n \in DOMAIN log[i] : log[i][n].term = currentTerm[i]}) >=
            MaxOrZero({n \in DOMAIN log[j] : log[j][n].term = currentTerm[i]})

LogMatchingInv ==
    \A i, j \in Server :
        \A n \in (1..Len(log[i])) \cap (1..Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

QuorumLogInv ==
    \A i \in Server :
    \A S \in Quorum(GetConfig(i)) :
        \E j \in S :
            IsPrefix(Committed(i), log[j])

MoreUpToDateCorrectInv ==
    \A i, j \in Server :
       (\/ LastTerm(log[i]) > LastTerm(log[j])
        \/ /\ LastTerm(log[i]) = LastTerm(log[j])
           /\ Len(log[i]) >= Len(log[j])) =>
       IsPrefix(Committed(j), log[i])

LeaderCompletenessInv == 
    \A i \in Server :
        LET committed == Committed(i) IN
        \A idx \in 1..Len(committed) :
            LET entry == log[i][idx] IN 
            
            \A l \in CurrentLeaders :
                
                currentTerm[l] > entry.term =>
                
                log[l][idx] = entry

CommittedIsDurableInv ==
    \A i \in Server :
        state[i] = Leader => commitIndex[i] <= durableState[i].log

===============================================================================

