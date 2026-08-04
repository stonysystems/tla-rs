-------------------------- MODULE LamportMutexClean --------------------------
(***************************************************************************)
(* Lamport's 1978 distributed mutual-exclusion algorithm, rewritten into    *)
(* the clean subset (C1-C5) defined in docs/clean_tla_subset.md.            *)
(*                                                                         *)
(* What changed and why is recorded in rewrite.md. In short: the network    *)
(* became one set of addressed messages, `crit` became per-node, and the    *)
(* receive actions take the message they consume as a parameter so that a   *)
(* step is taken by exactly one node.                                       *)
(*                                                                         *)
(* The subset has no channels, so the per-connection FIFO ordering the      *)
(* original relied on is carried explicitly in protocol state: every        *)
(* message has a sequence number, senders number their messages per         *)
(* destination, and a receiver only accepts the next number it expects from *)
(* that sender. This is not decoration -- without it TLC finds a            *)
(* MutualExclusion violation in twelve steps (see rewrite.md).              *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N, maxClock

ASSUME NType == N \in Nat
ASSUME maxClockType == maxClock \in Nat

Proc == 1 .. N
Clock == Nat \ {0}

VARIABLES
  clock,    \* local clock of each process
  req,      \* requests this process has received, by sender (0 = none)
  ack,      \* processes that have acknowledged this process's request
  network,  \* messages sent but not yet received
  crit,     \* whether this process is in its critical section
  sendSeq,  \* next sequence number this process will use toward each peer
  recvSeq   \* next sequence number this process will accept from each peer

(***************************************************************************)
(* Messages carry their sender and recipient, because the network is one    *)
(* set rather than a per-connection channel.                                *)
(***************************************************************************)
Message ==
  [type: {"req", "ack", "rel"}, src: Proc, dst: Proc, clock: Nat, seq: Nat]

ReqMessage(s, d, c, n) ==
  [type |-> "req", src |-> s, dst |-> d, clock |-> c, seq |-> n]
AckMessage(s, d, n) ==
  [type |-> "ack", src |-> s, dst |-> d, clock |-> 0, seq |-> n]
RelMessage(s, d, n) ==
  [type |-> "rel", src |-> s, dst |-> d, clock |-> 0, seq |-> n]

BroadcastReq(s, c) == { ReqMessage(s, d, c, sendSeq[s][d]) : d \in Proc \ {s} }
BroadcastRel(s)    == { RelMessage(s, d, sendSeq[s][d]) : d \in Proc \ {s} }

(***************************************************************************)
(* Numbering used by a broadcast: every peer's counter advances, the        *)
(* sender's own does not.                                                   *)
(***************************************************************************)
AdvanceAll(s) ==
  [sendSeq EXCEPT ![s] = [d \in Proc |->
      IF d = s THEN sendSeq[s][d] ELSE sendSeq[s][d] + 1]]

AdvanceOne(s, d) == [sendSeq EXCEPT ![s][d] = sendSeq[s][d] + 1]

(***************************************************************************)
(* A message is deliverable to p only when it is the next one p expects     *)
(* from that sender. This is what replaces the original's FIFO channels.    *)
(***************************************************************************)
Deliverable(p, m) == m.dst = p /\ m.seq = recvSeq[p][m.src]

Accept(p, m) == [recvSeq EXCEPT ![p][m.src] = recvSeq[p][m.src] + 1]

TypeOK ==
  /\ clock \in [Proc -> Clock]
  /\ req \in [Proc -> [Proc -> Nat]]
  /\ ack \in [Proc -> SUBSET Proc]
  /\ crit \in [Proc -> BOOLEAN]
  /\ sendSeq \in [Proc -> [Proc -> Nat]]
  /\ recvSeq \in [Proc -> [Proc -> Nat]]
  /\ network \subseteq Message

Init ==
  /\ clock = [p \in Proc |-> 1]
  /\ req = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ ack = [p \in Proc |-> {}]
  /\ crit = [p \in Proc |-> FALSE]
  /\ sendSeq = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ recvSeq = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ network = {}

(***************************************************************************)
(* beats(p,q) is true if p believes its request outranks q's. Every read is *)
(* into p's own table, so this is unchanged from the original.             *)
(***************************************************************************)
beats(p, q) ==
  \/ req[p][q] = 0
  \/ req[p][p] < req[p][q]
  \/ req[p][p] = req[p][q] /\ p < q

(***************************************************************************)
(* Process p requests access to the critical section.                      *)
(***************************************************************************)
Request(p) ==
  /\ req[p][p] = 0
  /\ req' = [req EXCEPT ![p][p] = clock[p]]
  /\ network' = network \cup BroadcastReq(p, clock[p])
  /\ sendSeq' = AdvanceAll(p)
  /\ ack' = [ack EXCEPT ![p] = {p}]
  /\ UNCHANGED <<clock, crit, recvSeq>>

(***************************************************************************)
(* Process p receives a request and acknowledges it. The sender is read     *)
(* off the message rather than bound by the action.                        *)
(***************************************************************************)
ReceiveRequest(p, m) ==
  /\ Deliverable(p, m)
  /\ m.type = "req"
  /\ req' = [req EXCEPT ![p][m.src] = m.clock]
  /\ clock' = [clock EXCEPT ![p] = IF m.clock > clock[p] THEN m.clock + 1 ELSE @ + 1]
  /\ network' = (network \ {m}) \cup {AckMessage(p, m.src, sendSeq[p][m.src])}
  /\ sendSeq' = AdvanceOne(p, m.src)
  /\ recvSeq' = Accept(p, m)
  /\ UNCHANGED <<ack, crit>>

(***************************************************************************)
(* Process p receives an acknowledgement.                                  *)
(***************************************************************************)
ReceiveAck(p, m) ==
  /\ Deliverable(p, m)
  /\ m.type = "ack"
  /\ ack' = [ack EXCEPT ![p] = @ \union {m.src}]
  /\ network' = network \ {m}
  /\ recvSeq' = Accept(p, m)
  /\ UNCHANGED <<clock, req, crit, sendSeq>>

(***************************************************************************)
(* Process p enters the critical section.                                  *)
(***************************************************************************)
Enter(p) ==
  /\ ack[p] = Proc
  /\ \A q \in Proc \ {p} : beats(p, q)
  /\ crit' = [crit EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<clock, req, ack, network, sendSeq, recvSeq>>

(***************************************************************************)
(* Process p exits the critical section and notifies the others.           *)
(***************************************************************************)
Exit(p) ==
  /\ crit[p]
  /\ crit' = [crit EXCEPT ![p] = FALSE]
  /\ network' = network \cup BroadcastRel(p)
  /\ sendSeq' = AdvanceAll(p)
  /\ req' = [req EXCEPT ![p][p] = 0]
  /\ ack' = [ack EXCEPT ![p] = {}]
  /\ UNCHANGED <<clock, recvSeq>>

(***************************************************************************)
(* Process p receives a release notification.                              *)
(***************************************************************************)
ReceiveRelease(p, m) ==
  /\ Deliverable(p, m)
  /\ m.type = "rel"
  /\ req' = [req EXCEPT ![p][m.src] = 0]
  /\ network' = network \ {m}
  /\ recvSeq' = Accept(p, m)
  /\ UNCHANGED <<clock, ack, crit, sendSeq>>

(***************************************************************************)
(* Next-state relation: one node takes one step. The message a receive      *)
(* consumes is drawn from the network, which is the framework's job after   *)
(* projection.                                                             *)
(***************************************************************************)
Next ==
  \E p \in Proc :
      \/ Request(p)
      \/ Enter(p)
      \/ Exit(p)
      \/ \E m \in network :
            \/ ReceiveRequest(p, m)
            \/ ReceiveAck(p, m)
            \/ ReceiveRelease(p, m)

vars == <<req, network, clock, ack, crit, sendSeq, recvSeq>>

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety. Stated over per-node `crit` rather than over a global set.       *)
(***************************************************************************)
MutualExclusion == \A p, q \in Proc : (p # q) => ~ (crit[p] /\ crit[q])

(***************************************************************************)
(* State constraint for finite-state model checking, as in the original.   *)
(***************************************************************************)
ClockConstraint == \A p \in Proc : clock[p] <= maxClock

(***************************************************************************)
(* The sequence numbers are unbounded in principle; bound them for model    *)
(* checking exactly as the clocks are bounded.                              *)
(***************************************************************************)
SeqConstraint == \A p, q \in Proc : sendSeq[p][q] <= maxClock

==============================================================================
