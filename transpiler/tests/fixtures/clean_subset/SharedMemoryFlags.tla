------------------------- MODULE SharedMemoryFlags ---------------------------
(* A shared-memory mutual-exclusion spec (Phase 52.M0 negative fixture).

   This is the other big family of non-projectable specs: there is no network
   at all, and progress depends on reading the other process's variables
   instantaneously. No amount of mechanical rewriting fixes this — the human
   must introduce messages first. *)

EXTENDS Naturals

CONSTANT Proc

VARIABLE flag, turn

Enter(i, j) ==
    flag[i] = FALSE
    /\ flag[j] = FALSE
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ turn' = i

Exit(i) ==
    flag[i] = TRUE
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ turn' = turn

Init ==
    flag = [i \in Proc |-> FALSE]
    /\ turn = 0

Next ==
    (\E i \in Proc : \E j \in Proc : Enter(i, j))
    \/ (\E i \in Proc : Exit(i))

==============================================================================
