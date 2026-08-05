------------------------------ MODULE PaxosClean ------------------------------
(***************************************************************************)
(* Paxos, rewritten into the clean subset (C1-C5) of                       *)
(* docs/clean_tla_subset.md. See rewrite.md for the reasoning; the two     *)
(* decisions that matter are:                                              *)
(*                                                                         *)
(*   1. the original's leader is anonymous -- `Phase1a(b)` is taken by no  *)
(*      node at all. Here every acceptor may lead a ballot, which is also  *)
(*      what the hand-written tla-rs Paxos does.                           *)
(*                                                                         *)
(*   2. the original's `Phase2a` scans the whole message set for a quorum  *)
(*      of 1b replies. A node cannot do that. Here a leader accumulates    *)
(*      replies in its own state and counts them -- the quorum-to-counting *)
(*      rewrite (P4).                                                      *)
(*                                                                         *)
(* Messages are never removed, exactly as in the original: receipt is      *)
(* re-reading, and a message may be received more than once. Consuming     *)
(* them would be a different protocol -- and would deadlock, since a state *)
(* with an empty network enables nothing.                                  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Value, Acceptor, MaxBallot

ASSUME AcceptorAssumption == IsFiniteSet(Acceptor) /\ Acceptor # {}
ASSUME MaxBallotAssumption == MaxBallot \in Nat

Ballot == 0 .. MaxBallot

None == -1

VARIABLES
  maxBal,      \* highest ballot this acceptor has promised in
  maxVBal,     \* ballot of the vote this acceptor last cast, -1 if none
  maxVal,      \* value of that vote
  leaderBal,   \* the ballot this node is currently leading, -1 if none
  promises,    \* acceptors that have answered this node's 1a, for leaderBal
  promiseBal,  \* highest mbal seen among those answers
  promiseVal,  \* the value that came with it
  proposed,    \* whether this node has already sent 2a for leaderBal
  msgs         \* messages sent but not yet received

Message ==
       [type: {"1a"}, src: Acceptor, dst: Acceptor, bal: Ballot,
        mbal: Ballot \cup {None}, mval: Value \cup {None}]
  \cup [type: {"1b"}, src: Acceptor, dst: Acceptor, bal: Ballot,
        mbal: Ballot \cup {None}, mval: Value \cup {None}]
  \cup [type: {"2a"}, src: Acceptor, dst: Acceptor, bal: Ballot,
        mbal: Ballot \cup {None}, mval: Value \cup {None}]
  \cup [type: {"2b"}, src: Acceptor, dst: Acceptor, bal: Ballot,
        mbal: Ballot \cup {None}, mval: Value \cup {None}]

Msg1a(s, d, b) ==
  [type |-> "1a", src |-> s, dst |-> d, bal |-> b, mbal |-> None, mval |-> None]
Msg1b(s, d, b, mb, mv) ==
  [type |-> "1b", src |-> s, dst |-> d, bal |-> b, mbal |-> mb, mval |-> mv]
Msg2a(s, d, b, v) ==
  [type |-> "2a", src |-> s, dst |-> d, bal |-> b, mbal |-> None, mval |-> v]
Msg2b(s, d, b, v) ==
  [type |-> "2b", src |-> s, dst |-> d, bal |-> b, mbal |-> None, mval |-> v]

Broadcast1a(s, b) == { Msg1a(s, d, b) : d \in Acceptor }
Broadcast2a(s, b, v) == { Msg2a(s, d, b, v) : d \in Acceptor }

TypeOK ==
  /\ maxBal \in [Acceptor -> Ballot \cup {None}]
  /\ maxVBal \in [Acceptor -> Ballot \cup {None}]
  /\ maxVal \in [Acceptor -> Value \cup {None}]
  /\ leaderBal \in [Acceptor -> Ballot \cup {None}]
  /\ promises \in [Acceptor -> SUBSET Acceptor]
  /\ promiseBal \in [Acceptor -> Ballot \cup {None}]
  /\ promiseVal \in [Acceptor -> Value \cup {None}]
  /\ proposed \in [Acceptor -> BOOLEAN]
  /\ msgs \subseteq Message

Init ==
  /\ maxBal = [a \in Acceptor |-> None]
  /\ maxVBal = [a \in Acceptor |-> None]
  /\ maxVal = [a \in Acceptor |-> None]
  /\ leaderBal = [a \in Acceptor |-> None]
  /\ promises = [a \in Acceptor |-> {}]
  /\ promiseBal = [a \in Acceptor |-> None]
  /\ promiseVal = [a \in Acceptor |-> None]
  /\ proposed = [a \in Acceptor |-> FALSE]
  /\ msgs = {}

(***************************************************************************)
(* A majority of the acceptors. The original quantified over an abstract   *)
(* set `Quorum`; a node counting its own replies needs a concrete test.    *)
(***************************************************************************)
IsMajority(s) == Cardinality(s) * 2 > Cardinality(Acceptor)

(***************************************************************************)
(* Phase 1a: node a begins ballot b. In the original this is the           *)
(* anonymous leader's action.                                              *)
(***************************************************************************)
Phase1a(a, b) ==
  /\ b > leaderBal[a]
  /\ leaderBal' = [leaderBal EXCEPT ![a] = b]
  /\ promises' = [promises EXCEPT ![a] = {}]
  /\ promiseBal' = [promiseBal EXCEPT ![a] = None]
  /\ promiseVal' = [promiseVal EXCEPT ![a] = None]
  /\ proposed' = [proposed EXCEPT ![a] = FALSE]
  /\ msgs' = msgs \cup Broadcast1a(a, b)
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 1b: acceptor a answers a 1a message, promising not to accept      *)
(* anything below m.bal and reporting its last vote.                       *)
(***************************************************************************)
Phase1b(a, m) ==
  /\ m.dst = a
  /\ m.type = "1a"
  /\ m.bal > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
  /\ msgs' = msgs \cup {Msg1b(a, m.src, m.bal, maxVBal[a], maxVal[a])}
  /\ UNCHANGED <<maxVBal, maxVal, leaderBal, promises, promiseBal,
                 promiseVal, proposed>>

(***************************************************************************)
(* Collecting a 1b reply. The original read every 1b message out of the    *)
(* global message set at once; a node accumulates them instead, keeping    *)
(* the highest-ballot vote it has been told about.                        *)
(***************************************************************************)
Phase1bReply(a, m) ==
  /\ m.dst = a
  /\ m.type = "1b"
  /\ m.bal = leaderBal[a]
  /\ promises' = [promises EXCEPT ![a] = promises[a] \cup {m.src}]
  /\ IF m.mbal > promiseBal[a]
       THEN /\ promiseBal' = [promiseBal EXCEPT ![a] = m.mbal]
            /\ promiseVal' = [promiseVal EXCEPT ![a] = m.mval]
       ELSE /\ promiseBal' = promiseBal
            /\ promiseVal' = promiseVal
  /\ msgs' = msgs
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, leaderBal, proposed>>

(***************************************************************************)
(* Phase 2a: having heard from a majority, the leader proposes. The value  *)
(* is the one reported with the highest ballot, or a free choice if no     *)
(* acceptor had voted.                                                     *)
(***************************************************************************)
Phase2a(a, v) ==
  /\ leaderBal[a] # None
  /\ ~proposed[a]
  /\ IsMajority(promises[a])
  /\ IF promiseBal[a] = None THEN TRUE ELSE v = promiseVal[a]
  /\ proposed' = [proposed EXCEPT ![a] = TRUE]
  /\ msgs' = msgs \cup Broadcast2a(a, leaderBal[a], v)
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, leaderBal, promises, promiseBal,
                 promiseVal>>

(***************************************************************************)
(* Phase 2b: acceptor a votes as a 2a message directs.                     *)
(***************************************************************************)
Phase2b(a, m) ==
  /\ m.dst = a
  /\ m.type = "2a"
  /\ m.bal >= maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
  /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
  /\ maxVal' = [maxVal EXCEPT ![a] = m.mval]
  /\ msgs' = msgs \cup {Msg2b(a, m.src, m.bal, m.mval)}
  /\ UNCHANGED <<leaderBal, promises, promiseBal, promiseVal, proposed>>

Next ==
  \E a \in Acceptor :
      \/ \E b \in Ballot : Phase1a(a, b)
      \/ \E v \in Value : Phase2a(a, v)
      \/ \E m \in msgs :
            \/ Phase1b(a, m)
            \/ Phase1bReply(a, m)
            \/ Phase2b(a, m)

vars == <<maxBal, maxVBal, maxVal, leaderBal, promises, promiseBal,
          promiseVal, proposed, msgs>>

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety. A value is chosen when a majority of acceptors have voted for   *)
(* it in the same ballot; at most one value may be chosen.                 *)
(*                                                                         *)
(* The original inherited its safety statement from the Voting refinement, *)
(* which is not part of the clean subset. This states the same property    *)
(* directly over the votes the acceptors have recorded.                    *)
(***************************************************************************)
VotedFor(a, b, v) == maxVBal[a] = b /\ maxVal[a] = v

ChosenAt(b, v) == IsMajority({a \in Acceptor : VotedFor(a, b, v)})

Consistency ==
  \A b1, b2 \in Ballot, v1, v2 \in Value :
      (ChosenAt(b1, v1) /\ ChosenAt(b2, v2)) => (v1 = v2)

==============================================================================
