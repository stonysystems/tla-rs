----------------------- MODULE DiningPhilosophersClean ----------------------
(***************************************************************************)
(* Chandy-Misra dining philosophers, rewritten into the clean subset       *)
(* (C1-C5) of docs/clean_tla_subset.md. See rewrite.md.                    *)
(*                                                                         *)
(* The original models the forks as a **global array indexed by fork**,    *)
(* each entry carrying a `holder`. A philosopher reads and writes          *)
(* `forks[LeftFork(self)]`, which is the fork it shares with its left      *)
(* neighbour -- so every fork transfer is an instantaneous write into      *)
(* state the neighbour also reads. That is the C2 violation, three times.  *)
(*                                                                         *)
(* Chandy-Misra is **natively a message algorithm**: philosophers hand     *)
(* forks to each other, and a request token travels the other way. The     *)
(* original just declined to model the handing. So this is not a           *)
(* re-design -- it is the same algorithm with the messages written down.   *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT NP

Proc == 1 .. NP

(***************************************************************************)
(* The ring. `Left`/`Right` are the original's `LeftPhilosopher` and       *)
(* `RightPhilosopher`; the fork *indices* disappear, because after the     *)
(* rewrite a fork is not an object with a holder -- it is a fact each      *)
(* endpoint holds about one of its edges.                                  *)
(***************************************************************************)
Left(p) == IF p = 1 THEN NP ELSE p - 1
Right(p) == IF p = NP THEN 1 ELSE p + 1

Adjacent(p, q) == q = Left(p) \/ q = Right(p)

(***************************************************************************)
(* Message tags.                                                           *)
(***************************************************************************)
RequestMsg == "req"
ForkMsg    == "fork"

VARIABLES
  hasFork,    \* hasFork[p][q]: p holds the fork it shares with q
  forkClean,  \* forkClean[p][q]: that fork is clean
  hasToken,   \* hasToken[p][q]: p holds the request token for that edge
  hungry,     \* this philosopher wants to eat
  eating,     \* this philosopher is eating
  msgs        \* messages sent

Message ==
       [mtype: {RequestMsg}, msource: Proc, mdest: Proc]
  \cup [mtype: {ForkMsg}, msource: Proc, mdest: Proc]

Request(s, d) == [mtype |-> RequestMsg, msource |-> s, mdest |-> d]
Fork(s, d) == [mtype |-> ForkMsg, msource |-> s, mdest |-> d]

TypeOK ==
  /\ hasFork \in [Proc -> [Proc -> BOOLEAN]]
  /\ forkClean \in [Proc -> [Proc -> BOOLEAN]]
  /\ hasToken \in [Proc -> [Proc -> BOOLEAN]]
  /\ hungry \in [Proc -> BOOLEAN]
  /\ eating \in [Proc -> BOOLEAN]
  /\ msgs \subseteq Message

(***************************************************************************)
(* Chandy-Misra's initial condition: on every edge the fork sits with the  *)
(* lower-numbered endpoint and the request token with the other, and every *)
(* fork is dirty. The original says the same thing in its own terms --     *)
(* "each fork held by the lowest-number philosopher adjacent to the fork", *)
(* "each fork starts out dirty" -- and has no token because it has no      *)
(* requests to defer.                                                      *)
(*                                                                         *)
(* The asymmetry is not cosmetic: it is what makes the precedence graph    *)
(* acyclic, and an acyclic precedence graph is why this algorithm cannot   *)
(* deadlock where Dijkstra's formulation can.                              *)
(***************************************************************************)
Init ==
  /\ hasFork = [p \in Proc |-> [q \in Proc |-> Adjacent(p, q) /\ p < q]]
  /\ forkClean = [p \in Proc |-> [q \in Proc |-> FALSE]]
  /\ hasToken = [p \in Proc |-> [q \in Proc |-> Adjacent(p, q) /\ p > q]]
  /\ hungry = [p \in Proc |-> TRUE]
  /\ eating = [p \in Proc |-> FALSE]
  /\ msgs = {}

(***************************************************************************)
(* A hungry philosopher asks a neighbour for the fork it is missing. The   *)
(* request token goes with the message, which is the whole point of the    *)
(* token: it stops a philosopher asking twice.                             *)
(***************************************************************************)
RequestFork(p, q) ==
  /\ hungry[p]
  /\ ~eating[p]
  /\ Adjacent(p, q)
  /\ ~hasFork[p][q]
  /\ hasToken[p][q]
  /\ hasToken' = [hasToken EXCEPT ![p][q] = FALSE]
  /\ msgs' = msgs \cup {Request(p, q)}
  /\ UNCHANGED <<hasFork, forkClean, hungry, eating>>

(***************************************************************************)
(* A request arrives. The philosopher takes the token; whether it gives up *)
(* the fork is a separate decision, taken by `ReleaseFork` below.          *)
(*                                                                         *)
(* Splitting the two is what the original's `Loop` does as well: its first *)
(* conjunct hands over any *dirty* fork it holds, independently of whether *)
(* anyone asked. Here the asking is explicit, so the deferral is too.      *)
(***************************************************************************)
HandleRequest(p, m) ==
  /\ m.mdest = p
  /\ m.mtype = RequestMsg
  /\ hasToken' = [hasToken EXCEPT ![p][m.msource] = TRUE]
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<hasFork, forkClean, hungry, eating>>

(***************************************************************************)
(* The rule that makes the algorithm work: **give up a dirty fork, keep a  *)
(* clean one**. A dirty fork is one this philosopher has already eaten     *)
(* with, so yielding it cannot starve anyone; a clean one has been given   *)
(* to it and not yet used.                                                 *)
(*                                                                         *)
(* Cleaning on hand-over is the original's `clean |-> TRUE` in the same    *)
(* branch.                                                                 *)
(***************************************************************************)
ReleaseFork(p, q) ==
  /\ Adjacent(p, q)
  /\ hasFork[p][q]
  /\ ~forkClean[p][q]
  /\ hasToken[p][q]
  /\ ~eating[p]
  /\ hasFork' = [hasFork EXCEPT ![p][q] = FALSE]
  /\ msgs' = msgs \cup {Fork(p, q)}
  /\ UNCHANGED <<forkClean, hasToken, hungry, eating>>

(***************************************************************************)
(* A fork arrives, and it arrives clean.                                   *)
(***************************************************************************)
HandleFork(p, m) ==
  /\ m.mdest = p
  /\ m.mtype = ForkMsg
  /\ hasFork' = [hasFork EXCEPT ![p][m.msource] = TRUE]
  /\ forkClean' = [forkClean EXCEPT ![p][m.msource] = TRUE]
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<hasToken, hungry, eating>>

(***************************************************************************)
(* Eating requires both forks, and both clean -- the original's `CanEat`.  *)
(* Both forks become dirty, which is what obliges this philosopher to hand *)
(* them on when asked.                                                     *)
(***************************************************************************)
Eat(p) ==
  /\ hungry[p]
  /\ ~eating[p]
  /\ hasFork[p][Left(p)]
  /\ hasFork[p][Right(p)]
  /\ forkClean[p][Left(p)]
  /\ forkClean[p][Right(p)]
  /\ eating' = [eating EXCEPT ![p] = TRUE]
  /\ hungry' = [hungry EXCEPT ![p] = FALSE]
  /\ forkClean' = [forkClean EXCEPT ![p][Left(p)] = FALSE,
                                    ![p][Right(p)] = FALSE]
  /\ msgs' = msgs
  /\ UNCHANGED <<hasFork, hasToken>>

(***************************************************************************)
(* Finishing a meal and becoming hungry again are **one action**, as they   *)
(* are in the original: `Think` is precisely where `hungry := TRUE`. An     *)
(* earlier draft split them, so a philosopher could sit not-hungry and      *)
(* not-eating for as long as it liked -- and the V2 comparison caught it,   *)
(* reporting 11 `hungry` states the original cannot reach. The original     *)
(* reaches exactly five: all hungry, or one philosopher not.                *)
(***************************************************************************)
Think(p) ==
  /\ eating[p]
  /\ eating' = [eating EXCEPT ![p] = FALSE]
  /\ hungry' = [hungry EXCEPT ![p] = TRUE]
  /\ msgs' = msgs
  /\ UNCHANGED <<hasFork, forkClean, hasToken>>

Next ==
  \E p \in Proc :
      \/ \E q \in Proc : RequestFork(p, q)
      \/ \E q \in Proc : ReleaseFork(p, q)
      \/ Eat(p)
      \/ Think(p)
      \/ \E m \in msgs :
            \/ HandleRequest(p, m)
            \/ HandleFork(p, m)

vars == <<hasFork, forkClean, hasToken, hungry, eating, msgs>>

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety, restated. The original says "if two philosophers share a fork,  *)
(* they cannot eat at the same time" and identifies sharing by index       *)
(* arithmetic over `LeftFork`/`RightFork`. After the rewrite, sharing a    *)
(* fork *is* adjacency, so the property reads directly.                    *)
(***************************************************************************)
ExclusiveAccess ==
  \A p, q \in Proc :
      (p # q /\ Adjacent(p, q)) => ~(eating[p] /\ eating[q])

(***************************************************************************)
(* The invariant that makes the rewrite checkable at all: a fork sits on   *)
(* exactly one side of each edge, and so does its token. If the rewrite    *)
(* lost or duplicated a fork, this is what would catch it -- and the       *)
(* original cannot state it, because there a fork is a single object with  *)
(* a `holder` and the property is true by construction.                    *)
(***************************************************************************)
ForkConservation ==
  \A p, q \in Proc :
      Adjacent(p, q) =>
          /\ ~(hasFork[p][q] /\ hasFork[q][p])
          /\ ~(hasToken[p][q] /\ hasToken[q][p])

=============================================================================
