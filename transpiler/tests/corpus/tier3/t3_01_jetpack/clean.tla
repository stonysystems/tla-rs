--------------------------- MODULE JetpackClean ---------------------------
(***************************************************************************)
(* Jetpack's recovery layer, rewritten into the clean subset (C1-C5) of    *)
(* docs/clean_tla_subset.md. See rewrite.md; this header states only the   *)
(* slice, because a reader has to know what is NOT here before reading     *)
(* what is.                                                                *)
(*                                                                         *)
(* The slice is Phase 51's R1: the recovery state machine                  *)
(*                                                                         *)
(*   Ready -> Recovery -> AfterBeginRecovery -> AfterPrepare               *)
(*         -> AfterAccept -> Ready                                         *)
(*                                                                         *)
(* run by one replica over fixed membership. Out of the slice, and each    *)
(* for a stated reason: the base protocol (a contract, not modelled), the  *)
(* client and execution layers, reconfiguration and the view machinery     *)
(* (Q2 puts membership change outside the subset), and `oepoch`, which     *)
(* exists only to order views.                                            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Server, CmdId, Key, MaxBallot

(***************************************************************************)
(* Recovery phases. The original's `AfterResubmit` is dropped with the     *)
(* client layer, so `AfterAccept` returns straight to `Ready`.             *)
(***************************************************************************)
Ready              == "ready"
Recovery           == "recovery"
AfterBeginRecovery == "afterBeginRecovery"
AfterPrepare       == "afterPrepare"
AfterAccept        == "afterAccept"

(***************************************************************************)
(* Message tags.                                                           *)
(***************************************************************************)
BeginRecoveryRequest  == "brq"
BeginRecoveryResponse == "brp"
PrepareRequest        == "pq"
PrepareResponse       == "pp"
AcceptRequest         == "aq"
AcceptResponse        == "ap"

VARIABLES
  jstate,            \* this replica's recovery phase
  jepoch,            \* the ballot this replica drives recovery with
  maxSeenBallot,     \* acceptor: highest ballot promised
  acceptedBallot,    \* acceptor: ballot of the last accept, 0 if none
  acceptedValue,     \* acceptor: value of the last accept
  recoverySet,       \* proposer: replicas that answered BeginRecovery
  prepRcvd,          \* proposer: replicas that promised
  acceptRcvd,        \* proposer: replicas that accepted
  chosenValue,       \* proposer: the value it will propose
  highestSeenBallot, \* proposer: highest accepted ballot any promise reported
  highestSeenValue,  \* proposer: the value reported with it
  msgs               \* messages sent

Command == [cmd_id: CmdId, key: Key]

(***************************************************************************)
(* A recovery value is a set of commands, exactly as in the original       *)
(* (`chosen_value` there is a set). `Value` is the type of those sets.     *)
(***************************************************************************)
Value == SUBSET Command

Ballot == 0 .. MaxBallot

Message ==
       [mtype: {BeginRecoveryRequest}, mjepoch: Ballot,
        msource: Server, mdest: Server]
  \cup [mtype: {BeginRecoveryResponse}, maccepted_ballot: Ballot,
        maccepted_value: Value, msource: Server, mdest: Server]
  \cup [mtype: {PrepareRequest}, mballot: Ballot,
        msource: Server, mdest: Server]
  \cup [mtype: {PrepareResponse}, mballot: Ballot,
        maccepted_ballot: Ballot, maccepted_value: Value,
        msource: Server, mdest: Server]
  \cup [mtype: {AcceptRequest}, mballot: Ballot, mvalue: Value,
        msource: Server, mdest: Server]
  \cup [mtype: {AcceptResponse}, mballot: Ballot,
        msource: Server, mdest: Server]

BeginRecoveryReq(s, d, e) ==
  [mtype |-> BeginRecoveryRequest, mjepoch |-> e, msource |-> s, mdest |-> d]

BeginRecoveryResp(s, d, ab, av) ==
  [mtype |-> BeginRecoveryResponse, maccepted_ballot |-> ab,
   maccepted_value |-> av, msource |-> s, mdest |-> d]

PrepareReq(s, d, b) ==
  [mtype |-> PrepareRequest, mballot |-> b, msource |-> s, mdest |-> d]

PrepareResp(s, d, b, ab, av) ==
  [mtype |-> PrepareResponse, mballot |-> b, maccepted_ballot |-> ab,
   maccepted_value |-> av, msource |-> s, mdest |-> d]

AcceptReq(s, d, b, v) ==
  [mtype |-> AcceptRequest, mballot |-> b, mvalue |-> v,
   msource |-> s, mdest |-> d]

AcceptResp(s, d, b) ==
  [mtype |-> AcceptResponse, mballot |-> b, msource |-> s, mdest |-> d]

BroadcastBeginRecovery(s, e) == { BeginRecoveryReq(s, d, e) : d \in Server }
BroadcastPrepare(s, b) == { PrepareReq(s, d, b) : d \in Server }
BroadcastAccept(s, b, v) == { AcceptReq(s, d, b, v) : d \in Server }

(***************************************************************************)
(* P4: the original quantifies over `JQuorum(new_view[i])`, a set of       *)
(* subsets. A replica cannot evaluate that; it can count what it has heard.*)
(***************************************************************************)
IsQuorum(s) == Cardinality(s) * 2 > Cardinality(Server)

TypeOK ==
  /\ jstate \in [Server -> {Ready, Recovery, AfterBeginRecovery,
                            AfterPrepare, AfterAccept}]
  /\ jepoch \in [Server -> Ballot]
  /\ maxSeenBallot \in [Server -> Ballot]
  /\ acceptedBallot \in [Server -> Ballot]
  /\ acceptedValue \in [Server -> Value]
  /\ recoverySet \in [Server -> SUBSET Server]
  /\ prepRcvd \in [Server -> SUBSET Server]
  /\ acceptRcvd \in [Server -> SUBSET Server]
  /\ chosenValue \in [Server -> Value]
  /\ highestSeenBallot \in [Server -> Ballot]
  /\ highestSeenValue \in [Server -> Value]
  /\ msgs \subseteq Message

Init ==
  /\ jstate = [i \in Server |-> Ready]
  /\ jepoch = [i \in Server |-> 0]
  /\ maxSeenBallot = [i \in Server |-> 0]
  /\ acceptedBallot = [i \in Server |-> 0]
  /\ acceptedValue = [i \in Server |-> {}]
  /\ recoverySet = [i \in Server |-> {}]
  /\ prepRcvd = [i \in Server |-> {}]
  /\ acceptRcvd = [i \in Server |-> {}]
  /\ chosenValue = [i \in Server |-> {}]
  /\ highestSeenBallot = [i \in Server |-> 0]
  /\ highestSeenValue = [i \in Server |-> {}]
  /\ msgs = {}

(***************************************************************************)
(* Phase 1: BeginRecovery. A replica decides to recover and asks everyone  *)
(* what they have accepted.                                                *)
(*                                                                         *)
(* The original guards this on `ostate[i] = ToBeLeader`, which is the base *)
(* protocol's business. With the base treated as a contract, the guard     *)
(* becomes "this replica is Ready" and the environment decides when.       *)
(***************************************************************************)
SendBeginRecovery(i, b) ==
  /\ jstate[i] = Ready
  /\ b > jepoch[i]
  /\ jepoch' = [jepoch EXCEPT ![i] = b]
  /\ jstate' = [jstate EXCEPT ![i] = Recovery]
  /\ recoverySet' = [recoverySet EXCEPT ![i] = {}]
  /\ highestSeenBallot' = [highestSeenBallot EXCEPT ![i] = 0]
  /\ highestSeenValue' = [highestSeenValue EXCEPT ![i] = {}]
  /\ msgs' = msgs \cup BroadcastBeginRecovery(i, b)
  /\ UNCHANGED <<maxSeenBallot, acceptedBallot, acceptedValue,
                 prepRcvd, acceptRcvd, chosenValue>>

(***************************************************************************)
(* An acceptor answers with what it has accepted. The original also copies *)
(* the requester's views into `old_view`/`new_view` and sets `oepoch`;     *)
(* those go with the view machinery.                                       *)
(***************************************************************************)
HandleBeginRecoveryReq(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = BeginRecoveryRequest
  /\ jstate' = [jstate EXCEPT ![i] = Recovery]
  /\ msgs' = (msgs \ {m}) \cup
       {BeginRecoveryResp(i, m.msource, acceptedBallot[i], acceptedValue[i])}
  /\ UNCHANGED <<jepoch, maxSeenBallot, acceptedBallot, acceptedValue,
                 recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue>>

(***************************************************************************)
(* The recovering replica records who answered, and keeps the              *)
(* highest-ballot value it has been told about.                            *)
(*                                                                         *)
(* The original stores every reply in `br_responses[i]` and scans them in  *)
(* `CompleteBeginRecovery`. Aggregating online is the same value once the  *)
(* quorum's replies are in, and it is what an implementation does.         *)
(***************************************************************************)
HandleBeginRecoveryResp(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = BeginRecoveryResponse
  /\ jstate[i] = Recovery
  /\ recoverySet' = [recoverySet EXCEPT ![i] = recoverySet[i] \cup {m.msource}]
  /\ highestSeenBallot' =
       IF m.maccepted_ballot > highestSeenBallot[i]
         THEN [highestSeenBallot EXCEPT ![i] = m.maccepted_ballot]
         ELSE highestSeenBallot
  /\ highestSeenValue' =
       IF m.maccepted_ballot > highestSeenBallot[i]
         THEN [highestSeenValue EXCEPT ![i] = m.maccepted_value]
         ELSE highestSeenValue
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<jstate, jepoch, maxSeenBallot, acceptedBallot, acceptedValue,
                 prepRcvd, acceptRcvd, chosenValue>>

(***************************************************************************)
(* With a quorum of answers in, the recovery value is settled: whatever    *)
(* the highest-ballot answer reported, or nothing if none had accepted.    *)
(***************************************************************************)
CompleteBeginRecovery(i) ==
  /\ jstate[i] = Recovery
  /\ IsQuorum(recoverySet[i])
  /\ chosenValue' = [chosenValue EXCEPT ![i] = highestSeenValue[i]]
  /\ jstate' = [jstate EXCEPT ![i] = AfterBeginRecovery]
  /\ prepRcvd' = [prepRcvd EXCEPT ![i] = {}]
  /\ msgs' = msgs
  /\ UNCHANGED <<jepoch, maxSeenBallot, acceptedBallot, acceptedValue,
                 recoverySet, acceptRcvd, highestSeenBallot, highestSeenValue>>

(***************************************************************************)
(* Phase 2: Prepare. Paxos phase 1 under another name.                     *)
(***************************************************************************)
SendPrepare(i) ==
  /\ jstate[i] = AfterBeginRecovery
  /\ msgs' = msgs \cup BroadcastPrepare(i, jepoch[i])
  /\ UNCHANGED <<jstate, jepoch, maxSeenBallot, acceptedBallot, acceptedValue,
                 recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue>>

(***************************************************************************)
(* An acceptor promises. The original replies on rejection too, with       *)
(* `mok = FALSE` and its own ballot, so the proposer can catch up; that    *)
(* reply carries no promise, and the slice drops it along with the         *)
(* proposer-side catch-up. Modelling only the accepting branch is what     *)
(* Phase 51's hand-written spec does, and is stated there too.             *)
(***************************************************************************)
HandlePrepareReq(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = PrepareRequest
  /\ m.mballot >= maxSeenBallot[i]
  /\ maxSeenBallot' = [maxSeenBallot EXCEPT ![i] = m.mballot]
  /\ msgs' = (msgs \ {m}) \cup
       {PrepareResp(i, m.msource, m.mballot,
                    acceptedBallot[i], acceptedValue[i])}
  /\ UNCHANGED <<jstate, jepoch, acceptedBallot, acceptedValue,
                 recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue>>

(***************************************************************************)
(* The proposer records a promise, keeping the highest-ballot value it has *)
(* been told about -- the same online aggregation as BeginRecovery, and    *)
(* the same reason.                                                        *)
(***************************************************************************)
HandlePrepareResp(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = PrepareResponse
  /\ m.mballot = jepoch[i]
  /\ prepRcvd' = [prepRcvd EXCEPT ![i] = prepRcvd[i] \cup {m.msource}]
  /\ highestSeenBallot' =
       IF m.maccepted_ballot > highestSeenBallot[i]
         THEN [highestSeenBallot EXCEPT ![i] = m.maccepted_ballot]
         ELSE highestSeenBallot
  /\ highestSeenValue' =
       IF m.maccepted_ballot > highestSeenBallot[i]
         THEN [highestSeenValue EXCEPT ![i] = m.maccepted_value]
         ELSE highestSeenValue
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<jstate, jepoch, maxSeenBallot, acceptedBallot, acceptedValue,
                 recoverySet, acceptRcvd, chosenValue>>

(***************************************************************************)
(* Paxos's safety core, and the one conjunct in this file that must not be *)
(* weakened: if any promise reported an accepted value, the proposer must  *)
(* propose that value. It may choose freely only when none had.            *)
(***************************************************************************)
CompletePrepare(i) ==
  /\ jstate[i] = AfterBeginRecovery
  /\ IsQuorum(prepRcvd[i])
  /\ chosenValue' =
       IF highestSeenBallot[i] > 0
         THEN [chosenValue EXCEPT ![i] = highestSeenValue[i]]
         ELSE chosenValue
  /\ jstate' = [jstate EXCEPT ![i] = AfterPrepare]
  /\ acceptRcvd' = [acceptRcvd EXCEPT ![i] = {}]
  /\ msgs' = msgs
  /\ UNCHANGED <<jepoch, maxSeenBallot, acceptedBallot, acceptedValue,
                 recoverySet, prepRcvd, highestSeenBallot, highestSeenValue>>

(***************************************************************************)
(* Phase 3: Accept. Paxos phase 2.                                         *)
(***************************************************************************)
SendAccept(i) ==
  /\ jstate[i] = AfterPrepare
  /\ msgs' = msgs \cup BroadcastAccept(i, jepoch[i], chosenValue[i])
  /\ UNCHANGED <<jstate, jepoch, maxSeenBallot, acceptedBallot, acceptedValue,
                 recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue>>

HandleAcceptReq(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = AcceptRequest
  /\ m.mballot >= maxSeenBallot[i]
  /\ maxSeenBallot' = [maxSeenBallot EXCEPT ![i] = m.mballot]
  /\ acceptedBallot' = [acceptedBallot EXCEPT ![i] = m.mballot]
  /\ acceptedValue' = [acceptedValue EXCEPT ![i] = m.mvalue]
  /\ msgs' = (msgs \ {m}) \cup {AcceptResp(i, m.msource, m.mballot)}
  /\ UNCHANGED <<jstate, jepoch, recoverySet, prepRcvd, acceptRcvd,
                 chosenValue, highestSeenBallot, highestSeenValue>>

HandleAcceptResp(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = AcceptResponse
  /\ m.mballot = jepoch[i]
  /\ acceptRcvd' = [acceptRcvd EXCEPT ![i] = acceptRcvd[i] \cup {m.msource}]
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<jstate, jepoch, maxSeenBallot, acceptedBallot, acceptedValue,
                 recoverySet, prepRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue>>

(***************************************************************************)
(* A quorum has accepted, so the value is chosen.                          *)
(***************************************************************************)
CompleteAccept(i) ==
  /\ jstate[i] = AfterPrepare
  /\ IsQuorum(acceptRcvd[i])
  /\ jstate' = [jstate EXCEPT ![i] = AfterAccept]
  /\ msgs' = msgs
  /\ UNCHANGED <<jepoch, maxSeenBallot, acceptedBallot, acceptedValue,
                 recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue>>

(***************************************************************************)
(* Recovery is over. The original resubmits `chosen_value` through the     *)
(* client path first; that path is out of the slice, so this returns       *)
(* straight to Ready.                                                      *)
(***************************************************************************)
FinishRecovery(i) ==
  /\ jstate[i] = AfterAccept
  /\ jstate' = [jstate EXCEPT ![i] = Ready]
  /\ recoverySet' = [recoverySet EXCEPT ![i] = {}]
  /\ prepRcvd' = [prepRcvd EXCEPT ![i] = {}]
  /\ acceptRcvd' = [acceptRcvd EXCEPT ![i] = {}]
  /\ msgs' = msgs
  /\ UNCHANGED <<jepoch, maxSeenBallot, acceptedBallot, acceptedValue,
                 chosenValue, highestSeenBallot, highestSeenValue>>

Next ==
  \E i \in Server :
      \/ \E b \in Ballot : SendBeginRecovery(i, b)
      \/ CompleteBeginRecovery(i)
      \/ SendPrepare(i)
      \/ CompletePrepare(i)
      \/ SendAccept(i)
      \/ CompleteAccept(i)
      \/ FinishRecovery(i)
      \/ \E m \in msgs :
            \/ HandleBeginRecoveryReq(i, m)
            \/ HandleBeginRecoveryResp(i, m)
            \/ HandlePrepareReq(i, m)
            \/ HandlePrepareResp(i, m)
            \/ HandleAcceptReq(i, m)
            \/ HandleAcceptResp(i, m)

vars == <<jstate, jepoch, maxSeenBallot, acceptedBallot, acceptedValue,
          recoverySet, prepRcvd, acceptRcvd, chosenValue,
          highestSeenBallot, highestSeenValue, msgs>>

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety. Recovery is Paxos, so its safety property is Paxos's: two       *)
(* replicas cannot have a quorum accept different values.                  *)
(***************************************************************************)
ChosenAt(b, v) ==
  IsQuorum({i \in Server : acceptedBallot[i] = b /\ acceptedValue[i] = v})

Consistency ==
  \A b1, b2 \in Ballot, v1, v2 \in Value :
      (ChosenAt(b1, v1) /\ ChosenAt(b2, v2)) => v1 = v2

(***************************************************************************)
(* Model-checking bound. Every send is a broadcast and receipt consumes,   *)
(* so the message set is what grows; bounding it is what makes the check   *)
(* finish. See rewrite.md for what the completed runs cover.               *)
(***************************************************************************)
SmallState == Cardinality(msgs) <= 4

=============================================================================
