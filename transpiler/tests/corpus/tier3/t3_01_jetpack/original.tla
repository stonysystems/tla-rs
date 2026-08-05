-------------------------- MODULE jetpack_raft_composition --------------------------
\* Composition of Jetpack with Raft (with add/remove reconfiguration).
\*
\* This wrapper:
\*   1. Declares the union of all variables (base + Jetpack + client + execution).
\*   2. INSTANCEs base_raft.tla and jetpack.tla, mapping variables.
\*   3. Wraps base_raft actions with UNCHANGED <<jetpackVars, clientVars,
\*      executionVars>>.
\*   4. Wraps jetpack actions with UNCHANGED raftOnlyVars.
\*   5. Defines WRequestReconfig — the only place where Jetpack's view is
\*      updated to reflect a membership change. Composes B!RequestReconfig
\*      (which puts the leader into ToBeLeader) with a wrapper-side update
\*      to old_view / new_view / jepoch. Standard Jetpack recovery then
\*      fires (because ostate=ToBeLeader and jstate=Ready), and after
\*      FinishRecovery puts ostate back to Leader, AppendPendingReconfigToLog
\*      emits the actual config-log entry.
\*   6. Defines ApplyCommitted that filters config-log entries (they are
\*      protocol bookkeeping and don't enter the user-facing execution trace).
\*
\* Raft uses a single proposer "sole" — all entries belong to one sequence.

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC

\* Basic universe sets and reconfig parameters.
CONSTANTS Server, Client, CmdId, Key, InitialMembers,
          MinClusterSize, MaxClusterSize,
          MaxElections, MaxRestarts,
          MaxAddReconfigs, MaxRemoveReconfigs,
          IncludeThesisBug

(****************************************************************************)
(* Variables                                                                *)
(****************************************************************************)

VARIABLES
    messages,

    \* Base protocol interface (shared with Jetpack).
    currentTerm,
    ostate,
    log,
    commitIndex,

    \* Raft-specific variables.
    votedFor,
    votesGranted,
    nextIndex,
    matchIndex,
    config,
    pending_reconfig,
    electionCtr, restartCtr, addReconfigCtr, removeReconfigCtr,

    \* Jetpack per-server variables.
    jstate, jepoch, oepoch, old_view, new_view, jpool,
    recovery_set, chosen_value, br_responses, prep_responses, accept_responses,

    \* Client-side variables.
    client_view, client_pending, client_successes, client_heard_from,

    \* Execution tracking.
    original_execution_cmds, execution_cmds

\* Variable groups for UNCHANGED clauses.
raftOnlyVars  == <<votedFor, votesGranted, nextIndex, matchIndex,
                   config, pending_reconfig,
                   electionCtr, restartCtr, addReconfigCtr, removeReconfigCtr>>
serverVars    == <<config, currentTerm, ostate, votedFor>>
candidateVars == <<votesGranted>>
leaderVars    == <<nextIndex, matchIndex>>
logVars       == <<log, commitIndex>>
auxVars       == <<electionCtr, restartCtr, addReconfigCtr, removeReconfigCtr>>
jetpackVars   == <<jstate, jepoch, oepoch, old_view, new_view, jpool,
                   recovery_set, chosen_value, br_responses,
                   prep_responses, accept_responses>>
clientVars    == <<client_view, client_pending, client_successes, client_heard_from>>
executionVars == <<original_execution_cmds, execution_cmds>>

vars == <<messages, serverVars, candidateVars, leaderVars, logVars,
          pending_reconfig, auxVars,
          jetpackVars, clientVars, executionVars>>

(****************************************************************************)
(* INSTANCE base protocol and Jetpack modules                               *)
(****************************************************************************)

B == INSTANCE base_raft

\* Raft: single proposer "sole".
J == INSTANCE jetpack WITH NoOpCmd <- [tag |-> "RaftNoOp"],
                          Proposer <- {"sole"},
                          ProposerOf <- LAMBDA i : "sole"

(****************************************************************************)
(* Re-exported constants / sentinels                                        *)
(****************************************************************************)

Follower     == B!Follower
Candidate    == B!Candidate
ToBeLeader   == B!ToBeLeader
Leader       == B!Leader
NotMember    == B!NotMember

ReconfigAdd    == B!ReconfigAdd
ReconfigRemove == B!ReconfigRemove

(****************************************************************************)
(* Initialization                                                           *)
(****************************************************************************)

Init ==
    /\ B!InitBaseVars
    /\ J!InitJetpackVars
    /\ J!InitClientVars
    /\ J!InitExecutionVars

(****************************************************************************)
(* Wrapped base_raft transitions                                            *)
(* Each adds UNCHANGED <<jetpackVars, clientVars, executionVars>>.          *)
(****************************************************************************)

Restart(i) ==
    /\ B!Restart(i)
    /\ UNCHANGED <<jetpackVars, clientVars, executionVars>>

UpdateTerm ==
    /\ B!UpdateTerm
    /\ UNCHANGED <<jetpackVars, clientVars, executionVars>>

RequestVote(i) ==
    /\ B!RequestVote(i)
    /\ UNCHANGED <<jetpackVars, clientVars, executionVars>>

HandleRequestVoteRequest ==
    /\ B!HandleRequestVoteRequest
    /\ UNCHANGED <<jetpackVars, clientVars, executionVars>>

HandleRequestVoteResponse ==
    /\ B!HandleRequestVoteResponse
    /\ UNCHANGED <<jetpackVars, clientVars, executionVars>>

BecomeToBeLeader(i) ==
    /\ B!BecomeToBeLeader(i)
    /\ UNCHANGED <<jetpackVars, clientVars, executionVars>>

ClientRequest(i, v) ==
    /\ B!ClientRequest(i, v)
    /\ UNCHANGED <<jetpackVars, clientVars, executionVars>>

AppendEntries(i, j) ==
    /\ B!AppendEntries(i, j)
    /\ UNCHANGED <<jetpackVars, clientVars, executionVars>>

RejectAppendEntriesRequest ==
    /\ B!RejectAppendEntriesRequest
    /\ UNCHANGED <<jetpackVars, clientVars, executionVars>>

AcceptAppendEntriesRequest ==
    /\ B!AcceptAppendEntriesRequest
    /\ UNCHANGED <<jetpackVars, clientVars, executionVars>>

HandleAppendEntriesResponse ==
    /\ B!HandleAppendEntriesResponse
    /\ UNCHANGED <<jetpackVars, clientVars, executionVars>>

AdvanceCommitIndex(i) ==
    /\ B!AdvanceCommitIndex(i)
    /\ UNCHANGED <<jetpackVars, clientVars, executionVars>>

\* ---- The composite reconfig action ----
\* B!RequestReconfig drops Leader -> ToBeLeader and stashes pending_reconfig.
\* The wrapper additionally bumps Jetpack's view to the proposed member set,
\* so the recovery quorums use the new cluster.
WRequestReconfig(i, op, target) ==
    /\ B!RequestReconfig(i, op, target)
    /\ LET newMembers == IF op = ReconfigAdd
                         THEN config[i].members \cup {target}
                         ELSE config[i].members \ {target}
           proposedView == [epoch                 |-> jepoch[i] + 1,
                            proposing_replica_ids |-> newMembers,
                            replica_ids           |-> newMembers]
       IN /\ old_view' = [old_view EXCEPT ![i] = new_view[i]]
          /\ new_view' = [new_view EXCEPT ![i] = proposedView]
          /\ jepoch'   = [jepoch EXCEPT ![i] = jepoch[i] + 1]
    /\ UNCHANGED <<jstate, oepoch, jpool, recovery_set, chosen_value,
                   br_responses, prep_responses, accept_responses,
                   clientVars, executionVars>>

WAppendPendingReconfigToLog(i) ==
    /\ B!AppendPendingReconfigToLog(i)
    /\ UNCHANGED <<jetpackVars, clientVars, executionVars>>

\* Raft ApplyCommitted: emit the next committed *AppendCommand* entry to
\* execution_cmds. Config entries (InitClusterCommand, AddServerCommand,
\* RemoveServerCommand) are protocol bookkeeping and do not participate in
\* the client-facing execution trace.
ApplyCommitted(i) ==
    /\ ostate[i] = Leader
    /\ LET ci      == commitIndex[i]["sole"]
           soleLog == log[i]["sole"]
           appendOnly == SelectSeq([k \in 1..ci |-> soleLog[k]],
                                    LAMBDA e : e.command = B!AppendCommand)
           appliedSoFar == Len(original_execution_cmds)
       IN /\ appliedSoFar < Len(appendOnly)
          /\ LET nextEntry == appendOnly[appliedSoFar + 1]
             IN /\ original_execution_cmds' = Append(original_execution_cmds, nextEntry.value)
                /\ execution_cmds' = Append(execution_cmds, nextEntry.value)
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars,
                   pending_reconfig, auxVars, jetpackVars, clientVars>>

(****************************************************************************)
(* Wrapped Jetpack transitions (each adds UNCHANGED raftOnlyVars)           *)
(****************************************************************************)

WClientSendPreaccept(c) ==
    /\ J!ClientSendPreaccept(c)
    /\ UNCHANGED raftOnlyVars

WHandlePreacceptRequest(i, m) ==
    /\ J!HandlePreacceptRequest(i, m)
    /\ UNCHANGED raftOnlyVars

WHandlePreacceptResponse(c, m) ==
    /\ J!HandlePreacceptResponse(c, m)
    /\ UNCHANGED raftOnlyVars

WSendBeginRecovery(i) ==
    /\ J!SendBeginRecovery(i)
    /\ UNCHANGED raftOnlyVars

WHandleBeginRecoveryRequest(i, m) ==
    /\ J!HandleBeginRecoveryRequest(i, m)
    /\ UNCHANGED raftOnlyVars

WHandleBeginRecoveryResponse(i, m) ==
    /\ J!HandleBeginRecoveryResponse(i, m)
    /\ UNCHANGED raftOnlyVars

WCompleteBeginRecovery(i) ==
    /\ J!CompleteBeginRecovery(i)
    /\ UNCHANGED raftOnlyVars

WSendPrepare(i) ==
    /\ J!SendPrepare(i)
    /\ UNCHANGED raftOnlyVars

WHandlePrepareRequest(i, m) ==
    /\ J!HandlePrepareRequest(i, m)
    /\ UNCHANGED raftOnlyVars

WHandlePrepareResponse(i, m) ==
    /\ J!HandlePrepareResponse(i, m)
    /\ UNCHANGED raftOnlyVars

WCompletePrepare(i) ==
    /\ J!CompletePrepare(i)
    /\ UNCHANGED raftOnlyVars

WSendAccept(i) ==
    /\ J!SendAccept(i)
    /\ UNCHANGED raftOnlyVars

WHandleAcceptRequest(i, m) ==
    /\ J!HandleAcceptRequest(i, m)
    /\ UNCHANGED raftOnlyVars

WHandleAcceptResponse(i, m) ==
    /\ J!HandleAcceptResponse(i, m)
    /\ UNCHANGED raftOnlyVars

WCompleteAccept(i) ==
    /\ J!CompleteAccept(i)
    /\ UNCHANGED raftOnlyVars

WResubmit(i) ==
    /\ J!Resubmit(i)
    /\ UNCHANGED raftOnlyVars

WCompleteResubmit(i) ==
    /\ J!CompleteResubmit(i)
    /\ UNCHANGED raftOnlyVars

WFinishRecovery(i) ==
    /\ J!FinishRecovery(i)
    /\ UNCHANGED raftOnlyVars

WHandleFinishRecovery(i, m) ==
    /\ J!HandleFinishRecovery(i, m)
    /\ UNCHANGED raftOnlyVars

(****************************************************************************)
(* Message receive plumbing                                                 *)
(****************************************************************************)

RaftReceive ==
    /\ B!RaftReceive
    /\ UNCHANGED <<jetpackVars, clientVars, executionVars>>

ServerReceive(m) ==
    /\ m.mdest \in Server
    /\ \/ /\ m.mtype = J!PreacceptRequest
          /\ WHandlePreacceptRequest(m.mdest, m)
       \/ /\ m.mtype = J!BeginRecoveryRequest
          /\ WHandleBeginRecoveryRequest(m.mdest, m)
       \/ /\ m.mtype = J!BeginRecoveryResponse
          /\ WHandleBeginRecoveryResponse(m.mdest, m)
       \/ /\ m.mtype = J!JetpackPrepareRequest
          /\ WHandlePrepareRequest(m.mdest, m)
       \/ /\ m.mtype = J!JetpackPrepareResponse
          /\ WHandlePrepareResponse(m.mdest, m)
       \/ /\ m.mtype = J!JetpackAcceptRequest
          /\ WHandleAcceptRequest(m.mdest, m)
       \/ /\ m.mtype = J!JetpackAcceptResponse
          /\ WHandleAcceptResponse(m.mdest, m)
       \/ /\ m.mtype = J!FinishRecoveryRequest
          /\ WHandleFinishRecovery(m.mdest, m)

ClientReceive(m) ==
    /\ m.mdest \in Client
    /\ m.mtype = J!PreacceptResponse
    /\ WHandlePreacceptResponse(m.mdest, m)

(****************************************************************************)
(* Next-state relation                                                      *)
(****************************************************************************)

Next ==
    \/ \E i \in Server : Restart(i)
    \/ UpdateTerm
    \/ \E i \in Server : RequestVote(i)
    \/ \E i \in Server : BecomeToBeLeader(i)
    \/ \E i \in Server : AdvanceCommitIndex(i)
    \/ \E i \in Server : ApplyCommitted(i)
    \/ \E i, j \in Server : AppendEntries(i, j)
    \/ \E i \in Server, v \in J!Commands : ClientRequest(i, v)
    \/ RaftReceive

    \* Reconfig (two-step, gated by Jetpack recovery)
    \/ \E i \in Server, op \in {ReconfigAdd, ReconfigRemove}, t \in Server :
            WRequestReconfig(i, op, t)
    \/ \E i \in Server : WAppendPendingReconfigToLog(i)

    \* Jetpack recovery flow
    \/ \E c \in Client : WClientSendPreaccept(c)
    \/ \E i \in Server : WSendBeginRecovery(i)
    \/ \E i \in Server : WCompleteBeginRecovery(i)
    \/ \E i \in Server : WSendPrepare(i)
    \/ \E i \in Server : WCompletePrepare(i)
    \/ \E i \in Server : WSendAccept(i)
    \/ \E i \in Server : WCompleteAccept(i)
    \/ \E i \in Server : WResubmit(i)
    \/ \E i \in Server : WCompleteResubmit(i)
    \/ \E i \in Server : WFinishRecovery(i)

    \/ \E m \in DOMAIN messages : ServerReceive(m)
    \/ \E m \in DOMAIN messages : ClientReceive(m)

Spec == Init /\ [][Next]_vars

(****************************************************************************)
(* State constraint                                                         *)
(****************************************************************************)

StateConstraint ==
    /\ \A i \in Server : currentTerm[i] <= 3
    /\ \A m \in DOMAIN messages : messages[m] <= 1
    /\ Cardinality(DOMAIN messages) <= 6
    /\ \A i \in Server : Len(log[i]["sole"]) <= 5
    /\ Len(original_execution_cmds) <= 4
    /\ Len(execution_cmds) <= 4

\* Tighter constraint for quick exhaustive checking.
\* Tuned (2026-05-01) to bound the reconfig+recovery state space; with
\* MaxRemoveReconfigs=1 even N=3 explores ~1M+ distinct states without
\* tight bounds because the recovery flow (BeginRecovery → Prepare →
\* Accept → Resubmit → FinishRecovery) introduces 9 sequential phases.
SmallStateConstraint ==
    /\ \A i \in Server : currentTerm[i] <= 2
    /\ \A m \in DOMAIN messages : messages[m] <= 1
    /\ Cardinality(DOMAIN messages) <= 3
    /\ \A i \in Server : Len(log[i]["sole"]) <= 2
    /\ Len(original_execution_cmds) <= 1
    /\ Len(execution_cmds) <= 1

(****************************************************************************)
(* Properties / invariants                                                  *)
(****************************************************************************)

\* Inherited from Jetpack: per-proposer committed log agreement.
CommittedLogAgreement == J!CommittedLogAgreement

\* Override Jetpack's LogOrderMatchesExecution to filter out config entries
\* (config-log entries don't carry .key/.cmd_id, so they shouldn't be fed
\* through ConflictOrderPreserved).
LogOrderMatchesExecution ==
    \A i \in Server :
        \A p \in {"sole"} :
            LET ci         == commitIndex[i][p]
                appendOnly == SelectSeq([k \in 1..ci |-> log[i][p][k]],
                                          LAMBDA e : e.command = B!AppendCommand)
                cmdValues  == [k \in 1..Len(appendOnly) |-> appendOnly[k].value]
            IN J!ConflictOrderPreserved(cmdValues, J!FilterNoOps(execution_cmds))

ExecutionDedupMatches == J!ExecutionDedupMatches

\* Raft-protocol invariants ported from upstream raft.tla.
NoLogDivergence ==
    \A s1, s2 \in Server :
        IF s1 = s2 THEN TRUE
        ELSE
            LET lowestCommonCI == IF commitIndex[s1]["sole"] < commitIndex[s2]["sole"]
                                  THEN commitIndex[s1]["sole"]
                                  ELSE commitIndex[s2]["sole"]
            IN IF lowestCommonCI > 0
               THEN \A index \in 1..lowestCommonCI :
                        log[s1]["sole"][index] = log[s2]["sole"][index]
               ELSE TRUE

MaxOneReconfigurationAtATime ==
    ~\E i \in Server :
        /\ ostate[i] = Leader
        /\ \E ind1, ind2 \in DOMAIN log[i]["sole"] :
            /\ ind1 # ind2
            /\ B!IsConfigCommand(log[i]["sole"], ind1)
            /\ B!IsConfigCommand(log[i]["sole"], ind2)
            /\ commitIndex[i]["sole"] < ind1
            /\ commitIndex[i]["sole"] < ind2

Safety ==
    [](CommittedLogAgreement
       /\ LogOrderMatchesExecution
       /\ ExecutionDedupMatches
       /\ NoLogDivergence
       /\ MaxOneReconfigurationAtATime)

SpecSafety == Spec => Safety

=============================================================================
