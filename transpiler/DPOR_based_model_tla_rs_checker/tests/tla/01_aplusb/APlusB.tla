---- MODULE APlusB ----
EXTENDS Naturals
\* Smallest end-to-end sanity check: two variables, one step, one invariant.

VARIABLE a, b

Init == a = 0 /\ b = 0

Add == a' = a + 1 /\ b' = b + 1

Next == Add

TypeOK == a >= 0 /\ b >= 0

SumInvariant == a = b

====
