------------------------ MODULE MCLamportMutexClean ------------------------
EXTENDS LamportMutexClean
CONSTANT MaxNat
ASSUME MaxNat \in Nat
NatOverride == 0 .. MaxNat
Constraint == ClockConstraint /\ SeqConstraint
=============================================================================
