---------------------------- MODULE SimpleCounter ----------------------------
(* A simple counter that counts up to a maximum value.
   This is a basic TLA+ spec to test fundamental parsing and translation. *)

EXTENDS Naturals

CONSTANT MaxCount

VARIABLE count

TypeOK == count \in Nat /\ count <= MaxCount

Init == count = 0

Increment == count < MaxCount /\ count' = count + 1

Decrement == count > 0 /\ count' = count - 1

Reset == count' = 0

Next == Increment \/ Decrement \/ Reset

================================================================================
