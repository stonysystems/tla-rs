----------------------------- MODULE SimpleClean -----------------------------
(***************************************************************************)
(* Lamport's TeachingConcurrency "Simple", rewritten into the clean subset  *)
(* (C1-C5) defined in docs/clean_tla_subset.md.                            *)
(*                                                                         *)
(* The original's whole content is one instantaneous cross-node read:       *)
(*                                                                         *)
(*     b(self) == y'[self] = x[(self-1) % N]                                *)
(*                                                                         *)
(* Message-ifying it is a design decision, and the property being preserved *)
(* is what decides it. See rewrite.md: a push (neighbour broadcasts x after *)
(* setting it) makes y always 1 and deletes real behaviours; a local cache  *)
(* of the neighbour's value lets the last reader see a stale 0 and breaks   *)
(* PCorrect. What preserves both the observations and the property is a     *)
(* request/response: the reader asks, and the neighbour answers with the    *)
(* value it holds at answer time.                                          *)
(***************************************************************************)
EXTENDS Integers

CONSTANT N

ASSUME NAssump == (N \in Nat) /\ (N > 0)

Proc == 0 .. (N - 1)
Left(i) == (i - 1) % N

VARIABLES
  x,        \* this process's own value
  y,        \* what this process read from its left neighbour
  pc,       \* control state
  network   \* messages sent but not yet received

Message == [type: {"read", "val"}, src: Proc, dst: Proc, val: {0, 1}]

ReadRequest(s, d)   == [type |-> "read", src |-> s, dst |-> d, val |-> 0]
ValueReply(s, d, v) == [type |-> "val", src |-> s, dst |-> d, val |-> v]

TypeOK ==
  /\ x \in [Proc -> {0, 1}]
  /\ y \in [Proc -> {0, 1}]
  /\ pc \in [Proc -> {"a", "b", "w", "Done"}]
  /\ network \subseteq Message

Init ==
  /\ x = [i \in Proc |-> 0]
  /\ y = [i \in Proc |-> 0]
  /\ pc = [i \in Proc |-> "a"]
  /\ network = {}

(***************************************************************************)
(* Step a: set my own value. Unchanged from the original.                  *)
(***************************************************************************)
a(self) ==
  /\ pc[self] = "a"
  /\ x' = [x EXCEPT ![self] = 1]
  /\ pc' = [pc EXCEPT ![self] = "b"]
  /\ UNCHANGED <<y, network>>

(***************************************************************************)
(* Step b, first half: ask the left neighbour for its value.               *)
(***************************************************************************)
b(self) ==
  /\ pc[self] = "b"
  /\ network' = network \cup {ReadRequest(self, Left(self))}
  /\ pc' = [pc EXCEPT ![self] = "w"]
  /\ UNCHANGED <<x, y>>

(***************************************************************************)
(* Answering a read. This is deliberately enabled in any control state:     *)
(* the original's read observes the neighbour's value at read time, whether *)
(* or not the neighbour has run its own step a, and the reply must be able  *)
(* to carry either 0 or 1 for the same reason.                             *)
(***************************************************************************)
Reply(self, m) ==
  /\ m.dst = self
  /\ m.type = "read"
  /\ network' = (network \ {m}) \cup {ValueReply(self, m.src, x[self])}
  /\ UNCHANGED <<x, y, pc>>

(***************************************************************************)
(* Step b, second half: record the answer.                                 *)
(***************************************************************************)
Recv(self, m) ==
  /\ m.dst = self
  /\ m.type = "val"
  /\ pc[self] = "w"
  /\ y' = [y EXCEPT ![self] = m.val]
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ network' = network \ {m}
  /\ UNCHANGED x

(***************************************************************************)
(* Allow infinite stuttering to prevent deadlock on termination, as in the  *)
(* original.                                                               *)
(***************************************************************************)
Terminating ==
  /\ \A i \in Proc : pc[i] = "Done"
  /\ UNCHANGED <<x, y, pc, network>>

Next ==
  \/ \E self \in Proc :
        \/ a(self)
        \/ b(self)
        \/ \E m \in network : Reply(self, m) \/ Recv(self, m)
  \/ Terminating

vars == <<x, y, pc, network>>

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The property to preserve: once every process has finished, at least one  *)
(* of them read a 1. Stated exactly as in the original.                    *)
(***************************************************************************)
PCorrect ==
  (\A i \in Proc : pc[i] = "Done") => (\E i \in Proc : y[i] = 1)

==============================================================================
