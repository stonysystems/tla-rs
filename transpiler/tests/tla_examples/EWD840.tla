-------------------------------- MODULE EWD840 --------------------------------
(* Dijkstra's EWD840 Termination Detection Algorithm.
   A simplified version for TLA+ transpiler testing.

   The algorithm detects when all N processes in a ring have terminated.
   A token circulates around the ring carrying color information. *)

EXTENDS Naturals

CONSTANT N

VARIABLE active, color, tpos, tcolor

(* Type invariant *)
TypeOK == tpos \in Nat /\ tpos < N /\ (tcolor = 0 \/ tcolor = 1)

(* Initial state: all processes active, token at position 0 *)
Init == active = {} /\ color = {} /\ tpos = 0 /\ tcolor = 0

(* Process i initiates termination - becomes inactive *)
Terminate(i) == active' = active \ {i} /\ color' = color /\ tpos' = tpos /\ tcolor' = tcolor

(* Process i sends a message to process j (i < j sends black) *)
SendMsg(i, j) == color' = (IF i > j THEN color \cup {i} ELSE color) /\ active' = active /\ tpos' = tpos /\ tcolor' = tcolor

(* Token passes from process tpos to next process *)
PassToken == tpos > 0 /\ tpos' = tpos - 1 /\ tcolor' = (IF tpos \in color THEN 1 ELSE tcolor) /\ active' = active /\ color' = color

(* Token returns to initiator, resets if environment detected *)
InitiateProbe == tpos = 0 /\ tpos' = N - 1 /\ tcolor' = 0 /\ color' = {} /\ active' = active

(* System has terminated when token completes a round with white color *)
Terminated == tpos = 0 /\ tcolor = 0 /\ active = {}

(* Next state relation - simplified *)
Next == PassToken \/ InitiateProbe

================================================================================
