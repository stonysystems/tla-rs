

-------------------------- MODULE OpenAddressingDefs --------------------------
EXTENDS OpenAddressingModel

contains(f,t,seq,Q) == \/ \E i \in 0..Q: isMatch(f,idx(f,i),t)
                       \/ \E i \in 1..Len(seq): seq[i] = f
                       \/ IF f \in ({ lo[x] : x \in DOMAIN lo } \ {0}) THEN evict = TRUE
                                                     ELSE FALSE

Contains == /\ \A seen \in history: 
                           contains(seen,table,external,L)
            /\ \A unseen \in (fps \ history):
                          ~contains(unseen,table,external,L)

abs(number) == IF number < 0 THEN -1 * number ELSE number

FindOrPut == evict = FALSE

Duplicates == FindOrPut => \A i \in 1..K : \A j \in (i+1)..K :
                 (table[i] # empty /\ table[j] # empty) => abs(table[i]) # abs(table[j])

isSorted(seq) == LET sub == SelectSeq(seq, LAMBDA e: e # empty)
                 IN IF Len(sub) < 2 THEN TRUE
                    ELSE \A i \in 1..(Len(sub) - 1):
                            sub[i] < sub[i+1]

Sorted == isSorted(external) /\ isSorted(newexternal)

containedInTable(f) == \E l \in 0..L: table[idx(abs(f), l)] = f

Consistent == FindOrPut => \A seen \in history:
            /\ containedInTable(seen) => ~containsElem(external, seen)
            /\ containedInTable(seen * (-1)) => containsElem(external, seen)
            /\ ~containedInTable(seen) => containsElem(external, seen)

CompleteAsSafety == \A self \in ProcSet: pc[self] = "Done" => (history = fps)

=============================================================================
