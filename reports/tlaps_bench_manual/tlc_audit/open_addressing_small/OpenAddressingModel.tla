

-------------------------- MODULE OpenAddressingModel --------------------------
EXTENDS Sequences, FiniteSets, Integers

CONSTANT K, fps, empty, Writer, Reader, L

ASSUME OAAssumption ==
       /\ K \in (Nat \ {0})
       /\ \A fp \in fps: fp \in (Nat \ {0})
       /\ IsFiniteSet(fps)
       /\ Cardinality(fps) > 1
       /\ empty \notin fps
       /\ L \in Nat
       /\ (2*L) <= K 

ASSUME EmptyNotInt == empty \notin Int

ASSUME WriterFinite == IsFiniteSet(Writer)
ASSUME ReaderFinite == IsFiniteSet(Reader)

last(seq) == seq[Len(seq)]                     

largestElem(sortedSeq) == IF sortedSeq = <<>> THEN 0 ELSE last(sortedSeq)

subSeqSmaller(seq1, seq2, elem) == SelectSeq(seq1, LAMBDA p:
                                     p < elem /\ p > largestElem(seq2))               

subSeqLarger(seq1, seq2) == IF seq2 = <<>> 
                            THEN seq1 
                            ELSE SelectSeq(seq1, LAMBDA p:
                                                    p > largestElem(seq2))               

containsElem(seq, elem) == elem \in { seq[i] : i \in DOMAIN seq }

min(S) == CHOOSE s \in S: \A a \in S: s <= a 
max(S) == CHOOSE s \in S: \A a \in S: s >= a 

minimum(a, b) == IF a < b THEN a ELSE b

mod(i,len) == IF i % len = 0 THEN len ELSE (i % len)

rescale(k,maxF,minF,fp,p) == LET f == (k - 1) \div (maxF - minF)
                             IN mod((f * (fp - minF + 1)) + p, k)

idx(fp, p) == rescale(K, max(fps), min(fps), fp, p)

isMatch(fp, pos, tbl) == \/ tbl[pos] = fp
                          \/ tbl[pos] = (-1*fp)

isEmpty(pos, tbl) == tbl[pos] = empty

isMarked(pos, tbl) == tbl[pos] < 0

wrapped(fp, pos) == idx(fp, 0) > mod(pos, K) 

compare(fp1,i1,fp2,i2) == 
                IF fp1 \in fps /\ fp2 \in fps                         
                THEN IF wrapped(fp1, i1) = wrapped(fp2, i2)           
                     THEN IF i1 > i2 /\ fp1 < fp2 THEN -1 ELSE 1
                     ELSE IF i1 < i2 /\ fp1 < fp2 THEN -1 ELSE        
                          IF i1 > i2 /\ fp1 > fp2 THEN -1 ELSE 0      
                ELSE 0            

VARIABLES table, external, newexternal, evict, waitCnt, history, pc, stack, 
          ei, ej, lo, fp, index, result, expected

vars == << table, external, newexternal, evict, waitCnt, history, pc, stack, 
           ei, ej, lo, fp, index, result, expected >>

ProcSet == (Writer)

Init == 
        /\ table = [i \in 1..K |-> empty]
        /\ external = <<>>
        /\ newexternal = <<>>
        /\ evict = FALSE
        /\ waitCnt = 0
        /\ history = {}
        
        /\ ei = [ self \in ProcSet |-> 1]
        /\ ej = [ self \in ProcSet |-> 1]
        /\ lo = [ self \in ProcSet |-> 0]
        
        /\ fp = [self \in Writer |-> 0]
        /\ index = [self \in Writer |-> 0]
        /\ result = [self \in Writer |-> FALSE]
        /\ expected = [self \in Writer |-> -1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "pick"]

strIns(self) == /\ pc[self] = "strIns"
                /\ IF ei[self] <= K+L
                      THEN /\ lo' = [lo EXCEPT ![self] = table[mod(ei[self] + 1, K)]]
                           /\ pc' = [pc EXCEPT ![self] = "nestedIns"]
                           /\ ei' = ei
                      ELSE /\ ei' = [ei EXCEPT ![self] = 1]
                           /\ pc' = [pc EXCEPT ![self] = "flush"]
                           /\ lo' = lo
                /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                                history, stack, ej, fp, index, result, 
                                expected >>

nestedIns(self) == /\ pc[self] = "nestedIns"
                   /\ IF compare(lo[self], mod(ei[self] + 1, K),
                            table[mod(ej[self], K)], mod(ej[self], K)) <= -1
                         THEN /\ table' = [table EXCEPT ![mod(ej[self] + 1, K)] = table[mod(ej[self], K)]]
                              /\ IF ej[self] = 0
                                    THEN /\ ej' = [ej EXCEPT ![self] = ej[self] - 1]
                                         /\ pc' = [pc EXCEPT ![self] = "set"]
                                    ELSE /\ ej' = [ej EXCEPT ![self] = ej[self] - 1]
                                         /\ pc' = [pc EXCEPT ![self] = "nestedIns"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "set"]
                              /\ UNCHANGED << table, ej >>
                   /\ UNCHANGED << external, newexternal, evict, waitCnt, 
                                   history, stack, ei, lo, fp, index, result, 
                                   expected >>

set(self) == /\ pc[self] = "set"
             /\ table' = [table EXCEPT ![mod(ej[self] + 1, K)] = lo[self]]
             /\ ej' = [ej EXCEPT ![self] = ei[self] + 1]
             /\ ei' = [ei EXCEPT ![self] = ei[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "strIns"]
             /\ UNCHANGED << external, newexternal, evict, waitCnt, history, 
                             stack, lo, fp, index, result, expected >>

flush(self) == /\ pc[self] = "flush"
               /\ IF ei[self] <= K+L
                     THEN /\ lo' = [lo EXCEPT ![self] = table[mod(ei[self], K)]]
                          /\ IF lo'[self] # empty /\
                                lo'[self] > largestElem(newexternal) /\
                                ((ei[self] <= K /\ ~wrapped(lo'[self],ei[self])) \/
                                 (ei[self] > K /\ wrapped(lo'[self],ei[self])))
                                THEN /\ newexternal' =         Append(newexternal \o
                                                       subSeqSmaller(external, newexternal, lo'[self]), lo'[self])
                                     /\ table' = [table EXCEPT ![mod(ei[self], K)] = lo'[self] * (-1)]
                                ELSE /\ TRUE
                                     /\ UNCHANGED << table, newexternal >>
                          /\ ei' = [ei EXCEPT ![self] = ei[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "flush"]
                          /\ UNCHANGED external
                     ELSE /\ external' = newexternal \o
                                          subSeqLarger(external, newexternal)
                          /\ newexternal' = <<>>
                          /\ pc' = [pc EXCEPT ![self] = "rtrn"]
                          /\ UNCHANGED << table, ei, lo >>
               /\ UNCHANGED << evict, waitCnt, history, stack, ej, fp, index, 
                               result, expected >>

rtrn(self) == /\ pc[self] = "rtrn"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ ei' = [ei EXCEPT ![self] = Head(stack[self]).ei]
              /\ ej' = [ej EXCEPT ![self] = Head(stack[self]).ej]
              /\ lo' = [lo EXCEPT ![self] = Head(stack[self]).lo]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                              history, fp, index, result, expected >>

Evict(self) == strIns(self) \/ nestedIns(self) \/ set(self) \/ flush(self)
                  \/ rtrn(self)

pick(self) == /\ pc[self] = "pick"
              /\ IF (fps \ history) = {}
                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ fp' = fp
                    ELSE /\ \E f \in (fps \ history):
                              fp' = [fp EXCEPT ![self] = f]
                         /\ pc' = [pc EXCEPT ![self] = "put"]
              /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                              history, stack, ei, ej, lo, index, result, 
                              expected >>

put(self) == /\ pc[self] = "put"
             /\ index' = [index EXCEPT ![self] = 0]
             /\ result' = [result EXCEPT ![self] = FALSE]
             /\ expected' = [expected EXCEPT ![self] = L]
             /\ IF evict
                   THEN /\ waitCnt' = waitCnt + 1
                        /\ pc' = [pc EXCEPT ![self] = "waitEv"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "chkSnc"]
                        /\ UNCHANGED waitCnt
             /\ UNCHANGED << table, external, newexternal, evict, history, 
                             stack, ei, ej, lo, fp >>

waitEv(self) == /\ pc[self] = "waitEv"
                /\ evict = FALSE
                /\ pc' = [pc EXCEPT ![self] = "endWEv"]
                /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                                history, stack, ei, ej, lo, fp, index, result, 
                                expected >>

endWEv(self) == /\ pc[self] = "endWEv"
                /\ waitCnt' = waitCnt - 1
                /\ pc' = [pc EXCEPT ![self] = "put"]
                /\ UNCHANGED << table, external, newexternal, evict, history, 
                                stack, ei, ej, lo, fp, index, result, expected >>

chkSnc(self) == /\ pc[self] = "chkSnc"
                /\ IF external # <<>>
                      THEN /\ pc' = [pc EXCEPT ![self] = "cntns"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "insrt"]
                /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                                history, stack, ei, ej, lo, fp, index, result, 
                                expected >>

cntns(self) == /\ pc[self] = "cntns"
               /\ IF index[self] < L
                     THEN /\ IF isMatch(fp[self], idx(fp[self], index[self]), table)
                                THEN /\ pc' = [pc EXCEPT ![self] = "pick"]
                                     /\ UNCHANGED << index, expected >>
                                ELSE /\ IF isEmpty(idx(fp[self], index[self]), table)
                                           THEN /\ expected' = [expected EXCEPT ![self] = minimum(expected[self], index[self])]
                                                /\ pc' = [pc EXCEPT ![self] = "onSnc"]
                                                /\ index' = index
                                           ELSE /\ IF isMarked(idx(fp[self], index[self]), table)
                                                      THEN /\ expected' = [expected EXCEPT ![self] = minimum(expected[self], index[self])]
                                                           /\ index' = [index EXCEPT ![self] = index[self] + 1]
                                                      ELSE /\ index' = [index EXCEPT ![self] = index[self] + 1]
                                                           /\ UNCHANGED expected
                                                /\ pc' = [pc EXCEPT ![self] = "cntns"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "onSnc"]
                          /\ UNCHANGED << index, expected >>
               /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                               history, stack, ei, ej, lo, fp, result >>

onSnc(self) == /\ pc[self] = "onSnc"
               /\ IF containsElem(external,fp[self])
                     THEN /\ pc' = [pc EXCEPT ![self] = "pick"]
                          /\ UNCHANGED << index, expected >>
                     ELSE /\ index' = [index EXCEPT ![self] = expected[self]]
                          /\ expected' = [expected EXCEPT ![self] = -1]
                          /\ pc' = [pc EXCEPT ![self] = "insrt"]
               /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                               history, stack, ei, ej, lo, fp, result >>

insrt(self) == /\ pc[self] = "insrt"
               /\ IF index[self] < L
                     THEN /\ expected' = [expected EXCEPT ![self] = table[idx(fp[self],index[self])]]
                          /\ IF expected'[self] = empty \/
                                (expected'[self] < 0 /\ expected'[self] # (-1) * fp[self])
                                THEN /\ pc' = [pc EXCEPT ![self] = "cas"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "isMth"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "tryEv"]
                          /\ UNCHANGED expected
               /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                               history, stack, ei, ej, lo, fp, index, result >>

isMth(self) == /\ pc[self] = "isMth"
               /\ IF isMatch(fp[self],idx(fp[self],index[self]),table)
                     THEN /\ pc' = [pc EXCEPT ![self] = "pick"]
                          /\ index' = index
                     ELSE /\ index' = [index EXCEPT ![self] = index[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "insrt"]
               /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                               history, stack, ei, ej, lo, fp, result, 
                               expected >>

cas(self) == /\ pc[self] = "cas"
             /\ IF table[(idx(fp[self],index[self]))] = expected[self]
                   THEN /\ table' = [table EXCEPT ![(idx(fp[self],index[self]))] = fp[self]]
                        /\ result' = [result EXCEPT ![self] = TRUE]
                   ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                        /\ table' = table
             /\ IF result'[self]
                   THEN /\ history' = (history \cup {fp[self]})
                        /\ pc' = [pc EXCEPT ![self] = "pick"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "insrt"]
                        /\ UNCHANGED history
             /\ UNCHANGED << external, newexternal, evict, waitCnt, stack, ei, 
                             ej, lo, fp, index, expected >>

tryEv(self) == /\ pc[self] = "tryEv"
               /\ IF evict = FALSE
                     THEN /\ evict' = TRUE
                          /\ pc' = [pc EXCEPT ![self] = "waitIns"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "put"]
                          /\ evict' = evict
               /\ UNCHANGED << table, external, newexternal, waitCnt, history, 
                               stack, ei, ej, lo, fp, index, result, expected >>

waitIns(self) == /\ pc[self] = "waitIns"
                 /\ waitCnt = Cardinality(Writer) - 1 + Cardinality(Reader)
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Evict",
                                                          pc        |->  "endEv",
                                                          ei        |->  ei[self],
                                                          ej        |->  ej[self],
                                                          lo        |->  lo[self] ] >>
                                                      \o stack[self]]
                 /\ ei' = [ei EXCEPT ![self] = 1]
                 /\ ej' = [ej EXCEPT ![self] = 1]
                 /\ lo' = [lo EXCEPT ![self] = 0]
                 /\ pc' = [pc EXCEPT ![self] = "strIns"]
                 /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                                 history, fp, index, result, expected >>

endEv(self) == /\ pc[self] = "endEv"
               /\ evict' = FALSE
               /\ pc' = [pc EXCEPT ![self] = "put"]
               /\ UNCHANGED << table, external, newexternal, waitCnt, history, 
                               stack, ei, ej, lo, fp, index, result, expected >>

p(self) == pick(self) \/ put(self) \/ waitEv(self) \/ endWEv(self)
              \/ chkSnc(self) \/ cntns(self) \/ onSnc(self) \/ insrt(self)
              \/ isMth(self) \/ cas(self) \/ tryEv(self) \/ waitIns(self)
              \/ endEv(self)

Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Evict(self))
           \/ (\E self \in Writer: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Writer : WF_vars(p(self)) /\ WF_vars(Evict(self))

=============================================================================
