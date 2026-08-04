---------------------------- MODULE TwoPhaseClean ----------------------------
(***************************************************************************)
(* Two-phase commit, rewritten into the clean subset (C1-C5) of            *)
(* docs/clean_tla_subset.md. See rewrite.md; the decision that matters is  *)
(* what to do with the transaction manager.                                *)
(*                                                                         *)
(* 2PC has two roles, and the original models the TM as *global* state --   *)
(* `tmState` and `tmPrepared` belong to no node. The rewrite makes the TM   *)
(* a designated node: `TM` is a constant drawn from `RM`, every node        *)
(* carries the coordinator fields, and the TM actions are guarded by        *)
(* `a = TM`. Folding the role into every node, the way Paxos's leader was   *)
(* folded, would be wrong here: 2PC needs exactly one coordinator, and two  *)
(* of them could decide differently.                                       *)
(***************************************************************************)
EXTENDS Integers

CONSTANT RM, TM

ASSUME TMAssumption == TM \in RM

VARIABLES
  rmState,     \* this resource manager's own state
  tmState,     \* the coordinator's state; meaningful only at TM
  tmPrepared,  \* RMs the coordinator has heard "Prepared" from
  msgs         \* messages sent

Message ==
       [type: {"Prepared"}, src: RM, dst: RM]
  \cup [type: {"Commit"}, src: RM, dst: RM]
  \cup [type: {"Abort"}, src: RM, dst: RM]

Prepared(s, d) == [type |-> "Prepared", src |-> s, dst |-> d]
CommitMsg(s, d) == [type |-> "Commit", src |-> s, dst |-> d]
AbortMsg(s, d) == [type |-> "Abort", src |-> s, dst |-> d]

BroadcastCommit(s) == { CommitMsg(s, d) : d \in RM }
BroadcastAbort(s) == { AbortMsg(s, d) : d \in RM }

TypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in [RM -> {"init", "committed", "aborted"}]
  /\ tmPrepared \in [RM -> SUBSET RM]
  /\ msgs \subseteq Message

Init ==
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = [rm \in RM |-> "init"]
  /\ tmPrepared = [rm \in RM |-> {}]
  /\ msgs = {}

(***************************************************************************)
(* The coordinator records a "Prepared" it has been sent.                  *)
(***************************************************************************)
TMRcvPrepared(a, m) ==
  /\ a = TM
  /\ m.dst = a
  /\ m.type = "Prepared"
  /\ tmState[a] = "init"
  /\ tmPrepared' = [tmPrepared EXCEPT ![a] = tmPrepared[a] \cup {m.src}]
  /\ msgs' = msgs
  /\ UNCHANGED <<rmState, tmState>>

(***************************************************************************)
(* The coordinator commits, having heard from every resource manager. 2PC  *)
(* needs unanimity rather than a majority, so this stays a comparison      *)
(* against the whole node set and not a count.                             *)
(***************************************************************************)
TMCommit(a) ==
  /\ a = TM
  /\ tmState[a] = "init"
  /\ tmPrepared[a] = RM
  /\ tmState' = [tmState EXCEPT ![a] = "committed"]
  /\ msgs' = msgs \cup BroadcastCommit(a)
  /\ UNCHANGED <<rmState, tmPrepared>>

(***************************************************************************)
(* The coordinator spontaneously aborts.                                   *)
(***************************************************************************)
TMAbort(a) ==
  /\ a = TM
  /\ tmState[a] = "init"
  /\ tmState' = [tmState EXCEPT ![a] = "aborted"]
  /\ msgs' = msgs \cup BroadcastAbort(a)
  /\ UNCHANGED <<rmState, tmPrepared>>

(***************************************************************************)
(* A resource manager prepares, telling the coordinator.                   *)
(***************************************************************************)
RMPrepare(a) ==
  /\ rmState[a] = "working"
  /\ rmState' = [rmState EXCEPT ![a] = "prepared"]
  /\ msgs' = msgs \cup {Prepared(a, TM)}
  /\ UNCHANGED <<tmState, tmPrepared>>

(***************************************************************************)
(* A resource manager spontaneously aborts. It sends nothing, exactly as   *)
(* in the original.                                                        *)
(***************************************************************************)
RMChooseToAbort(a) ==
  /\ rmState[a] = "working"
  /\ rmState' = [rmState EXCEPT ![a] = "aborted"]
  /\ msgs' = msgs
  /\ UNCHANGED <<tmState, tmPrepared>>

(***************************************************************************)
(* A resource manager is told to commit.                                   *)
(***************************************************************************)
RMRcvCommitMsg(a, m) ==
  /\ m.dst = a
  /\ m.type = "Commit"
  /\ rmState' = [rmState EXCEPT ![a] = "committed"]
  /\ msgs' = msgs
  /\ UNCHANGED <<tmState, tmPrepared>>

(***************************************************************************)
(* A resource manager is told to abort.                                    *)
(***************************************************************************)
RMRcvAbortMsg(a, m) ==
  /\ m.dst = a
  /\ m.type = "Abort"
  /\ rmState' = [rmState EXCEPT ![a] = "aborted"]
  /\ msgs' = msgs
  /\ UNCHANGED <<tmState, tmPrepared>>

Next ==
  \E a \in RM :
      \/ TMCommit(a)
      \/ TMAbort(a)
      \/ RMPrepare(a)
      \/ RMChooseToAbort(a)
      \/ \E m \in msgs :
            \/ TMRcvPrepared(a, m)
            \/ RMRcvCommitMsg(a, m)
            \/ RMRcvAbortMsg(a, m)

vars == <<rmState, tmState, tmPrepared, msgs>>

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety, from module TCommit: no resource manager commits while another  *)
(* has aborted.                                                            *)
(***************************************************************************)
Consistent ==
  \A rm1, rm2 \in RM :
      ~ (rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

==============================================================================
