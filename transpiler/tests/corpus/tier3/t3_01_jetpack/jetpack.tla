------------------------------ MODULE jetpack ------------------------------
\* Jetpack plugin consensus protocol — reusable module.
\*
\* This module defines Jetpack's own variables and transitions. It is designed
\* to be INSTANCE'd by a wrapper module that composes it with a base protocol.
\*
\* Variables declared here (the "Jetpack interface"):
\*   Base protocol interface: messages, currentTerm, ostate, log, commitIndex
\*   Jetpack-own: jstate, jepoch, oepoch, old_view, new_view, jpool,
\*                recovery_set, chosen_value, br_responses, prep_responses,
\*                accept_responses
\*   Client: client_view, client_pending, client_successes, client_heard_from
\*   Execution: original_execution_cmds, execution_cmds
\*
\* The wrapper must:
\*   1. Declare all variables (shared + protocol-specific)
\*   2. INSTANCE jetpack WITH <variable mappings>
\*   3. Define protocol-specific actions: BecomeToBeLeader, ApplyCommitted,
\*      Restart, etc.
\*   4. Wrap each J!<action> with UNCHANGED <protocolSpecificVars>
\*   5. Wire Init, Next, Spec
\*
\* Protocol-specific actions NOT defined here (wrapper provides them):
\*   - BecomeToBeLeader(i): intercepts base protocol leader promotion
\*   - ApplyCommitted(i): applies next committed log entry to execution_cmds
\*     (execution order across proposers is protocol-specific)
\*
\* ---- True 3-D Log Architecture ----
\*
\* The base protocol maintains a genuine 3-D log as TLA+ state:
\*
\*   log[i][j][k]
\*     i: where the copy is stored (server)
\*     j: which logical proposer/sequence (element of Proposer)
\*     k: position within that sequence
\*
\*   commitIndex[i][j]
\*     Per-proposer commit progress on server i for proposer j's sequence.
\*
\* Jetpack reads and writes this 3-D log directly. There are no projection
\* or refinement operators. The base protocol owns and maintains the 3-D
\* structure; Jetpack consumes it.
\*
\* Protocol-specific log shapes:
\*   - Raft: Proposer = {"sole"}, one active sequence
\*   - CoPilot: Proposer = Server, two active sequences (pilot + copilot)
\*   - Mencius: Proposer = Server, N sequences (round-robin)
\*
\* Abstract interface each base protocol wrapper must provide:
\*
\*   Variables (mapped via INSTANCE):
\*     log[i][j]       - per-server, per-proposer replicated log
\*     commitIndex[i][j] - per-server, per-proposer commit progress
\*     ostate[i]       - per-server role (must include Follower, Leader)
\*     currentTerm[i]  - per-server epoch/term
\*     messages        - shared message bag
\*
\*   Constants:
\*     Proposer        - set of proposer IDs
\*     ProposerOf(_)   - maps server to its active proposer ID when leading

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ---- Constants shared with base protocol (supplied at instantiation) ----
CONSTANTS Server, Client, CmdId, Key, NoOpCmd,
          InitialMembers,    \* Initial cluster member set (subset of Server).
                             \* Bases without reconfig pass InitialMembers <- Server.
          Proposer,          \* Set of proposer IDs (protocol-specific)
          ProposerOf(_)      \* Server -> Proposer (which proposer a server uses)

Nil == "Nil"
NilCmd == [tag |-> "NilCmd"]
NilJPool == [tag |-> "NilJPool"]
NilPrepResp == [tag |-> "NilPrepResp"]

\* Jetpack protocol states.
Ready            == "Ready"
Recovery         == "Recovery"
AfterBeginRecovery == "AfterBeginRecovery"
AfterPrepare     == "AfterPrepare"
AfterAccept      == "AfterAccept"
AfterResubmit    == "AfterResubmit"

\* Additional server state for Jetpack recovery (inserted between Candidate and Leader).
ToBeLeader == "ToBeLeader"
\* Base protocol states (re-declared for use in guards).
Follower   == "Follower"
Candidate  == "Candidate"
Leader     == "Leader"

\* Jetpack message types.
PreacceptRequest      == "PreacceptRequest"
PreacceptResponse     == "PreacceptResponse"
BeginRecoveryRequest  == "BeginRecoveryRequest"
BeginRecoveryResponse == "BeginRecoveryResponse"
JetpackPrepareRequest == "JetpackPrepareRequest"
JetpackPrepareResponse == "JetpackPrepareResponse"
JetpackAcceptRequest  == "JetpackAcceptRequest"
JetpackAcceptResponse == "JetpackAcceptResponse"
FinishRecoveryRequest == "FinishRecoveryRequest"

(***************************************************************************)
(* Shared data types                                                       *)
(***************************************************************************)

Commands == { [cmd_id |-> id, key |-> k] : id \in CmdId, k \in Key }

View == [epoch: Nat,
         proposing_replica_ids: SUBSET Server,
         replica_ids: SUBSET Server]

DefaultView ==
    [epoch |-> 1,
     proposing_replica_ids |-> InitialMembers,
     replica_ids |-> InitialMembers]

JPool == [max_seen_ballot: Nat,
          accepted_ballot: Nat,
          accepted_value: SUBSET Commands,
          pool: [Key -> Commands \cup {NilCmd}]]

EmptyJPool ==
    [max_seen_ballot |-> 0,
     accepted_ballot |-> 0,
     accepted_value |-> {},
     pool |-> [k \in Key |-> NilCmd]]

JPoolCommands(p) == {p.pool[k] : k \in Key} \ {NilCmd}

PrepResp == [accepted_ballot: Nat, accepted_value: SUBSET Commands]

(***************************************************************************)
(* Variables                                                               *)
(* Only the variables Jetpack reads/writes are declared here.              *)
(* Protocol-specific variables (votedFor, votesGranted, nextIndex, etc.)   *)
(* are declared by the wrapper and handled via UNCHANGED there.            *)
(***************************************************************************)

VARIABLES
    messages,

    \* Base protocol variables (Jetpack reads/writes these).
    \* log[i][j] = sequence of entries for proposer j on server i
    \* commitIndex[i][j] = commit progress for proposer j on server i
    currentTerm,
    ostate,
    log,
    commitIndex,

    \* Jetpack per-server variables.
    jstate,
    jepoch,
    oepoch,
    old_view,
    new_view,
    jpool,
    recovery_set,
    chosen_value,
    br_responses,
    prep_responses,
    accept_responses,

    \* Client-side variables.
    client_view,
    client_pending,
    client_successes,
    client_heard_from,

    \* Execution tracking.
    original_execution_cmds,
    execution_cmds

baseVars == <<currentTerm, ostate, log, commitIndex>>
jetpackVars == <<jstate, jepoch, oepoch, old_view, new_view, jpool,
                 recovery_set, chosen_value, br_responses,
                 prep_responses, accept_responses>>
clientVars == <<client_view, client_pending, client_successes, client_heard_from>>
executionVars == <<original_execution_cmds, execution_cmds>>

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)

Quorum == {q \in SUBSET(Server) : Cardinality(q) * 2 > Cardinality(Server)}

JQuorum(v) == {q \in SUBSET(v.replica_ids) :
                   Cardinality(q) * 2 > Cardinality(v.replica_ids)}

FastpathQuorum(v) ==
    {q \in JQuorum(v) :
        /\ v.proposing_replica_ids \subseteq q
        /\ \A q2 \in JQuorum(v) :
             v.proposing_replica_ids \subseteq q2 => (q \cap q2) \in JQuorum(v)}

Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

SeqToSet(s) == {s[i] : i \in 1..Len(s)}

\* Message bag helpers.
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@ (m :> 1)

WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        IF msgs[m] <= 1 THEN [i \in DOMAIN msgs \ {m} |-> msgs[i]]
        ELSE [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

Send(m) == messages' = WithMessage(m, messages)
Discard(m) == messages' = WithoutMessage(m, messages)
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

RECURSIVE AddMessages(_,_)
AddMessages(ms, msgs) ==
    IF ms = {} THEN msgs
    ELSE LET m == CHOOSE x \in ms : TRUE
         IN AddMessages(ms \ {m}, WithMessage(m, msgs))

RECURSIVE RemoveCmd(_,_)
RemoveCmd(seq, cmd) ==
    IF seq = <<>> THEN <<>>
    ELSE LET head == seq[1]
             tail == SubSeq(seq, 2, Len(seq))
         IN IF head = cmd
            THEN RemoveCmd(tail, cmd)
            ELSE <<head>> \o RemoveCmd(tail, cmd)

RECURSIVE Dedup(_)
Dedup(seq) ==
    IF seq = <<>> THEN <<>>
    ELSE LET head == seq[1]
             tail == SubSeq(seq, 2, Len(seq))
         IN <<head>> \o Dedup(RemoveCmd(tail, head))

\* Filter out NoOp entries (protocol-internal bookkeeping, e.g. Mencius skipped slots).
\* For protocols without NoOps, NoOpCmd is a sentinel that never matches, so this is a no-op.
FilterNoOps(seq) == SelectSeq(seq, LAMBDA x : x # NoOpCmd)

\* Two commands conflict if they access the same key (but are different commands).
CmdConflicts(a, b) == a.key = b.key /\ a # b

\* Position of element e in sequence s (0 if not found).
\* After Dedup, each element appears at most once, so position is unique.
RECURSIVE IndexOf(_, _)
IndexOf(s, e) ==
    IF s = <<>> THEN 0
    ELSE IF Head(s) = e THEN 1
    ELSE LET rest == IndexOf(Tail(s), e)
         IN IF rest = 0 THEN 0 ELSE rest + 1

\* Conflict order preserved: for any conflicting pair (a before b) in s1,
\* if both appear in s2, then a must also appear before b in s2.
ConflictOrderPreserved(s1, s2) ==
    \A k1 \in 1..Len(s1) : \A k2 \in 1..Len(s1) :
        (/\ k1 < k2
         /\ CmdConflicts(s1[k1], s1[k2])
         /\ IndexOf(s2, s1[k1]) > 0
         /\ IndexOf(s2, s1[k2]) > 0)
        => IndexOf(s2, s1[k1]) < IndexOf(s2, s1[k2])

\* Collect all command IDs across all proposer sequences on all servers.
LogCmdIds ==
    UNION { {log[i][j][k].value.cmd_id : k \in 1..Len(log[i][j])}
            : i \in Server, j \in Proposer }

ExecCmdIds ==
    {cmd.cmd_id : cmd \in SeqToSet(execution_cmds)}

OriginalExecCmdIds ==
    {cmd.cmd_id : cmd \in SeqToSet(original_execution_cmds)}

UsedCmdIds ==
    LogCmdIds \cup ExecCmdIds \cup OriginalExecCmdIds

AvailableCommands == {cmd \in Commands : cmd.cmd_id \notin UsedCmdIds}

HasConflict(pool, cmd) ==
    /\ pool[cmd.key] /= NilCmd
    /\ pool[cmd.key] /= cmd

RecoveryCommands(i, qs) ==
    {cmd \in Commands :
        Cardinality({s \in qs : cmd \in JPoolCommands(br_responses[i][s])}) * 2
            > Cardinality(qs)}

\* Committed commands for proposer j on server i.
CommittedCmds(i, j) ==
    IF commitIndex[i][j] = 0 THEN <<>>
    ELSE [k \in 1..commitIndex[i][j] |-> log[i][j][k].value]

\* All committed commands across all proposers on server i.
AllCommittedCmds(i) ==
    UNION { SeqToSet(CommittedCmds(i, j)) : j \in Proposer }

ChosenExecutedInView(i) ==
    \A cmd \in chosen_value[i] :
        \A s \in new_view[i].replica_ids :
            cmd \in AllCommittedCmds(s)

(***************************************************************************)
(* Jetpack initialization                                                  *)
(***************************************************************************)

InitJetpackVars ==
    /\ jstate = [i \in Server |-> Ready]
    /\ jepoch = [i \in Server |-> DefaultView.epoch]
    /\ oepoch = [i \in Server |-> DefaultView.epoch]
    /\ old_view = [i \in Server |-> DefaultView]
    /\ new_view = [i \in Server |-> DefaultView]
    /\ jpool = [i \in Server |-> EmptyJPool]
    /\ recovery_set = [i \in Server |-> {}]
    /\ chosen_value = [i \in Server |-> {}]
    /\ br_responses = [i \in Server |-> [j \in Server |-> NilJPool]]
    /\ prep_responses = [i \in Server |-> [j \in Server |-> NilPrepResp]]
    /\ accept_responses = [i \in Server |-> [j \in Server |-> FALSE]]

InitClientVars ==
    /\ client_view = [c \in Client |-> DefaultView]
    /\ client_pending = [c \in Client |-> NilCmd]
    /\ client_successes = [c \in Client |-> {}]
    /\ client_heard_from = [c \in Client |-> {}]

InitExecutionVars ==
    /\ original_execution_cmds = <<>>
    /\ execution_cmds = <<>>

(***************************************************************************)
(* Jetpack transitions                                                     *)
(* NOTE: These actions only specify UNCHANGED for variables declared in    *)
(* this module. The wrapper must add UNCHANGED for protocol-specific       *)
(* variables (e.g., copilotVars, menciusVars) when using these actions.    *)
(***************************************************************************)

\* Client sends a Preaccept to all replicas in its view.
ClientSendPreaccept(c) ==
    /\ client_pending[c] = NilCmd
    /\ AvailableCommands /= {}
    /\ \E cmd \in AvailableCommands :
          LET view == client_view[c]
              msgSet == { [mtype  |-> PreacceptRequest,
                            msource |-> c,
                            mdest |-> s,
                            mepoch |-> view.epoch,
                            mview |-> view,
                            mcmd |-> cmd] : s \in view.replica_ids }
          IN /\ messages' = AddMessages(msgSet, messages)
             /\ client_pending' = [client_pending EXCEPT ![c] = cmd]
             /\ client_successes' = [client_successes EXCEPT ![c] = {}]
             /\ client_heard_from' = [client_heard_from EXCEPT ![c] = {}]
             /\ UNCHANGED <<baseVars, jetpackVars, client_view, executionVars>>

\* Server handles Preaccept from client.
\* When the leader accepts, it appends to its own proposer's sequence in the 3-D log.
HandlePreacceptRequest(i, m) ==
    /\ m.mtype = PreacceptRequest
    /\ i = m.mdest
    /\ LET cmd == m.mcmd
           epochOk == m.mepoch = jepoch[i]
           readyOk == jstate[i] = Ready
           noConflict == \lnot HasConflict(jpool[i].pool, cmd)
           accept == epochOk /\ readyOk /\ noConflict
           reply == [mtype   |-> PreacceptResponse,
                     msuccess |-> accept,
                     mjepoch |-> jepoch[i],
                     mview   |-> new_view[i],
                     mcmd    |-> cmd,
                     msource |-> i,
                     mdest   |-> m.msource]
           j == ProposerOf(i)
           \* Tag with command="AppendCommand" so bases that distinguish
           \* entry types (e.g. Raft's reconfig variant) can filter on it.
           \* Bases that don't care simply ignore the field.
           newLog == Append(log[i][j], [command |-> "AppendCommand",
                                        term    |-> currentTerm[i],
                                        value   |-> cmd])
       IN /\ jpool' = IF accept THEN
                          [jpool EXCEPT ![i].pool[cmd.key] = cmd]
                      ELSE
                          jpool
          /\ log' = IF epochOk /\ readyOk /\ ostate[i] = Leader
                    THEN [log EXCEPT ![i][j] = newLog]
                    ELSE log
          /\ Reply(reply, m)
          /\ UNCHANGED <<currentTerm, ostate, commitIndex,
                         jstate, jepoch, oepoch, old_view, new_view,
                         recovery_set, chosen_value, br_responses,
                         prep_responses, accept_responses,
                         clientVars, executionVars>>

\* Client handles Preaccept responses.
\*
\* Quorum-based fast-path: the client accumulates successful responders and
\* declares fast-path success once they form a FastpathQuorum. A reject does
\* NOT immediately kill the attempt — fast-path failure is declared only when
\* the remaining unheard servers plus current successes can no longer form any
\* FastpathQuorum.
\*
\* client_view update: only adopt a newer view from a reject when the response
\* carries a strictly higher epoch than the client's current view.
\*
\* Completion events that clear client_pending[c]:
\*   - Fast-path success: newSuccesses \in FastpathQuorum(view)
\*   - Fast-path abandoned: no remaining possibility to reach a FastpathQuorum
HandlePreacceptResponse(c, m) ==
    /\ m.mtype = PreacceptResponse
    /\ m.mdest = c
    /\ client_pending[c] = m.mcmd
    /\ LET view == client_view[c]
           newHeard == client_heard_from[c] \cup {m.msource}
           newSuccesses == IF m.msuccess
                           THEN client_successes[c] \cup {m.msource}
                           ELSE client_successes[c]
           fastOk == newSuccesses \in FastpathQuorum(view)
           \* Fast-path is still achievable if the current successes plus all
           \* remaining unheard replicas could form some FastpathQuorum.
           remaining == view.replica_ids \ newHeard
           canStillSucceed ==
               \E q \in FastpathQuorum(view) : q \subseteq (newSuccesses \cup remaining)
           abandon == \lnot fastOk /\ \lnot canStillSucceed
       IN /\ client_successes' =
              IF fastOk \/ abandon
              THEN [client_successes EXCEPT ![c] = {}]
              ELSE [client_successes EXCEPT ![c] = newSuccesses]
          /\ client_heard_from' =
              IF fastOk \/ abandon
              THEN [client_heard_from EXCEPT ![c] = {}]
              ELSE [client_heard_from EXCEPT ![c] = newHeard]
          /\ client_pending' =
              IF fastOk \/ abandon
              THEN [client_pending EXCEPT ![c] = NilCmd]
              ELSE client_pending
          /\ client_view' =
              IF /\ \lnot m.msuccess
                 /\ m.mview.epoch > client_view[c].epoch
              THEN [client_view EXCEPT ![c] = m.mview]
              ELSE client_view
          /\ execution_cmds' =
              IF fastOk
              THEN Append(execution_cmds, m.mcmd)
              ELSE execution_cmds
          /\ original_execution_cmds' = original_execution_cmds
          /\ Discard(m)
          /\ UNCHANGED <<baseVars, jetpackVars>>

\* Recovery Phase 1: BeginRecovery.
SendBeginRecovery(i) ==
    /\ ostate[i] = ToBeLeader
    /\ jstate[i] = Ready
    /\ LET view == new_view[i]
           msgSet == { [mtype |-> BeginRecoveryRequest,
                        msource |-> i,
                        mdest |-> s,
                        mold_view |-> old_view[i],
                        mnew_view |-> new_view[i]] : s \in view.replica_ids }
       IN /\ messages' = AddMessages(msgSet, messages)
          /\ jstate' = [jstate EXCEPT ![i] = Recovery]
          /\ br_responses' = [br_responses EXCEPT ![i] = [s \in Server |-> NilJPool]]
          /\ UNCHANGED <<baseVars,
                         jepoch, oepoch, old_view, new_view, jpool,
                         recovery_set, chosen_value, prep_responses,
                         accept_responses, clientVars, executionVars>>

HandleBeginRecoveryRequest(i, m) ==
    /\ m.mtype = BeginRecoveryRequest
    /\ i = m.mdest
    /\ old_view' = [old_view EXCEPT ![i] = m.mold_view]
    /\ new_view' = [new_view EXCEPT ![i] = m.mnew_view]
    /\ oepoch' = [oepoch EXCEPT ![i] = m.mnew_view.epoch]
    /\ jstate' = [jstate EXCEPT ![i] = Recovery]
    /\ Reply([mtype |-> BeginRecoveryResponse,
              mjpool |-> jpool[i],
              msource |-> i,
              mdest |-> m.msource],
              m)
    /\ UNCHANGED <<baseVars,
                   jepoch, jpool, recovery_set, chosen_value,
                   br_responses, prep_responses, accept_responses,
                   clientVars, executionVars>>

HandleBeginRecoveryResponse(i, m) ==
    /\ m.mtype = BeginRecoveryResponse
    /\ i = m.mdest
    /\ jstate[i] = Recovery
    /\ br_responses' = [br_responses EXCEPT ![i][m.msource] = m.mjpool]
    /\ Discard(m)
    /\ UNCHANGED <<baseVars,
                   jstate, jepoch, oepoch, old_view, new_view, jpool,
                   recovery_set, chosen_value, prep_responses, accept_responses,
                   clientVars, executionVars>>

CompleteBeginRecovery(i) ==
    /\ jstate[i] = Recovery
    /\ \E qs \in JQuorum(new_view[i]) :
         /\ \A s \in qs : br_responses[i][s] /= NilJPool
         /\ LET rec == RecoveryCommands(i, qs)
            IN /\ recovery_set' = [recovery_set EXCEPT ![i] = rec]
               /\ chosen_value' = [chosen_value EXCEPT ![i] = rec]
               /\ jstate' = [jstate EXCEPT ![i] = AfterBeginRecovery]
    /\ UNCHANGED <<messages, baseVars,
                   jepoch, oepoch, old_view, new_view, jpool,
                   br_responses, prep_responses, accept_responses,
                   clientVars, executionVars>>

\* Recovery Phase 2: Prepare.
SendPrepare(i) ==
    /\ jstate[i] = AfterBeginRecovery
    /\ LET view == new_view[i]
           msgSet == { [mtype |-> JetpackPrepareRequest,
                        moepoch |-> oepoch[i],
                        mjepoch |-> jepoch[i],
                        mmax_seen_ballot |-> jpool[i].max_seen_ballot,
                        msource |-> i,
                        mdest |-> s] : s \in view.replica_ids }
       IN /\ messages' = AddMessages(msgSet, messages)
          /\ prep_responses' = [prep_responses EXCEPT ![i] = [s \in Server |-> NilPrepResp]]
          /\ UNCHANGED <<baseVars,
                         jstate, jepoch, oepoch, old_view, new_view, jpool,
                         recovery_set, chosen_value, br_responses,
                         accept_responses, clientVars, executionVars>>

HandlePrepareRequest(i, m) ==
    /\ m.mtype = JetpackPrepareRequest
    /\ i = m.mdest
    /\ LET ok == /\ m.moepoch >= oepoch[i]
                 /\ m.mjepoch >= jepoch[i]
                 /\ m.mmax_seen_ballot >= jpool[i].max_seen_ballot
           reply == IF ok THEN
                       [mtype |-> JetpackPrepareResponse,
                        mok |-> TRUE,
                        maccepted_ballot |-> jpool[i].accepted_ballot,
                        maccepted_value |-> jpool[i].accepted_value,
                        moepoch |-> oepoch[i],
                        mjepoch |-> jepoch[i],
                        mmax_seen_ballot |-> m.mmax_seen_ballot,
                        msource |-> i,
                        mdest |-> m.msource]
                   ELSE
                       [mtype |-> JetpackPrepareResponse,
                        mok |-> FALSE,
                        maccepted_ballot |-> jpool[i].accepted_ballot,
                        maccepted_value |-> jpool[i].accepted_value,
                        moepoch |-> oepoch[i],
                        mjepoch |-> jepoch[i],
                        mmax_seen_ballot |-> jpool[i].max_seen_ballot,
                        msource |-> i,
                        mdest |-> m.msource]
       IN /\ oepoch' = IF ok THEN [oepoch EXCEPT ![i] = Max({oepoch[i], m.moepoch})]
                       ELSE oepoch
          /\ jepoch' = IF ok THEN [jepoch EXCEPT ![i] = Max({jepoch[i], m.mjepoch})]
                       ELSE jepoch
          /\ jpool' = IF ok THEN
                        [jpool EXCEPT ![i].max_seen_ballot = m.mmax_seen_ballot]
                      ELSE jpool
          /\ Reply(reply, m)
          /\ UNCHANGED <<baseVars,
                         jstate, old_view, new_view, recovery_set, chosen_value,
                         br_responses, prep_responses, accept_responses,
                         clientVars, executionVars>>

HandlePrepareResponse(i, m) ==
    /\ m.mtype = JetpackPrepareResponse
    /\ i = m.mdest
    /\ IF m.mok THEN
          /\ prep_responses' =
                 [prep_responses EXCEPT ![i][m.msource] =
                     [accepted_ballot |-> m.maccepted_ballot,
                      accepted_value |-> m.maccepted_value]]
          /\ UNCHANGED <<oepoch, jepoch, jpool>>
       ELSE
          /\ prep_responses' = prep_responses
          /\ oepoch' = [oepoch EXCEPT ![i] = Max({oepoch[i], m.moepoch})]
          /\ jepoch' = [jepoch EXCEPT ![i] = Max({jepoch[i], m.mjepoch})]
          /\ jpool' = [jpool EXCEPT ![i].max_seen_ballot =
                           Max({jpool[i].max_seen_ballot, m.mmax_seen_ballot})]
    /\ Discard(m)
    /\ UNCHANGED <<baseVars,
                   jstate, old_view, new_view, recovery_set, chosen_value,
                   br_responses, accept_responses, clientVars, executionVars>>

CompletePrepare(i) ==
    /\ jstate[i] = AfterBeginRecovery
    /\ \E qs \in JQuorum(new_view[i]) :
         /\ \A s \in qs : prep_responses[i][s] /= NilPrepResp
         /\ LET respVals == {prep_responses[i][s] : s \in qs}
                ballots == {r.accepted_ballot : r \in respVals}
                maxb == IF ballots = {} THEN 0 ELSE Max(ballots)
                topVals == {r \in respVals : r.accepted_ballot = maxb}
                bestVals == {r.accepted_value : r \in topVals}
                pick == IF maxb = 0 \/ bestVals = {}
                        THEN chosen_value[i]
                        ELSE CHOOSE v \in bestVals : TRUE
            IN /\ chosen_value' = [chosen_value EXCEPT ![i] = pick]
               /\ jstate' = [jstate EXCEPT ![i] = AfterPrepare]
    /\ UNCHANGED <<messages, baseVars,
                   jepoch, oepoch, old_view, new_view, jpool,
                   recovery_set, br_responses, prep_responses,
                   accept_responses, clientVars, executionVars>>

\* Recovery Phase 3: Accept.
SendAccept(i) ==
    /\ jstate[i] = AfterPrepare
    /\ LET view == new_view[i]
           msgSet == { [mtype |-> JetpackAcceptRequest,
                        moepoch |-> oepoch[i],
                        mjepoch |-> jepoch[i],
                        mmax_seen_ballot |-> jpool[i].max_seen_ballot,
                        mvalue |-> chosen_value[i],
                        msource |-> i,
                        mdest |-> s] : s \in view.replica_ids }
       IN /\ messages' = AddMessages(msgSet, messages)
          /\ accept_responses' = [accept_responses EXCEPT ![i] = [s \in Server |-> FALSE]]
          /\ UNCHANGED <<baseVars,
                         jstate, jepoch, oepoch, old_view, new_view, jpool,
                         recovery_set, chosen_value, br_responses,
                         prep_responses, clientVars, executionVars>>

HandleAcceptRequest(i, m) ==
    /\ m.mtype = JetpackAcceptRequest
    /\ i = m.mdest
    /\ LET ok == /\ m.moepoch >= oepoch[i]
                 /\ m.mjepoch >= jepoch[i]
                 /\ m.mmax_seen_ballot >= jpool[i].max_seen_ballot
           reply == IF ok THEN
                       [mtype |-> JetpackAcceptResponse,
                        mok |-> TRUE,
                        mmax_seen_ballot |-> m.mmax_seen_ballot,
                        msource |-> i,
                        mdest |-> m.msource]
                   ELSE
                       [mtype |-> JetpackAcceptResponse,
                        mok |-> FALSE,
                        mmax_seen_ballot |-> jpool[i].max_seen_ballot,
                        msource |-> i,
                        mdest |-> m.msource]
       IN /\ oepoch' = IF ok THEN [oepoch EXCEPT ![i] = Max({oepoch[i], m.moepoch})]
                       ELSE oepoch
          /\ jepoch' = IF ok THEN [jepoch EXCEPT ![i] = Max({jepoch[i], m.mjepoch})]
                       ELSE jepoch
          /\ jpool' = IF ok THEN
                        [jpool EXCEPT ![i].max_seen_ballot = m.mmax_seen_ballot,
                                         ![i].accepted_ballot = m.mmax_seen_ballot,
                                         ![i].accepted_value = m.mvalue]
                      ELSE jpool
          /\ Reply(reply, m)
          /\ UNCHANGED <<baseVars,
                         jstate, old_view, new_view, recovery_set, chosen_value,
                         br_responses, prep_responses, accept_responses,
                         clientVars, executionVars>>

HandleAcceptResponse(i, m) ==
    /\ m.mtype = JetpackAcceptResponse
    /\ i = m.mdest
    /\ IF m.mok THEN
          /\ accept_responses' =
                 [accept_responses EXCEPT ![i][m.msource] = TRUE]
          /\ UNCHANGED <<oepoch, jepoch, jpool>>
       ELSE
          /\ accept_responses' = accept_responses
          /\ jpool' = [jpool EXCEPT ![i].max_seen_ballot =
                          Max({jpool[i].max_seen_ballot, m.mmax_seen_ballot})]
          /\ UNCHANGED <<oepoch, jepoch>>
    /\ Discard(m)
    /\ UNCHANGED <<baseVars,
                   jstate, old_view, new_view, recovery_set, chosen_value,
                   br_responses, prep_responses, clientVars, executionVars>>

CompleteAccept(i) ==
    /\ jstate[i] = AfterPrepare
    /\ \E qs \in JQuorum(new_view[i]) :
         /\ \A s \in qs : accept_responses[i][s] = TRUE
         /\ jstate' = [jstate EXCEPT ![i] = AfterAccept]
    /\ UNCHANGED <<messages, baseVars,
                   jepoch, oepoch, old_view, new_view, jpool,
                   recovery_set, chosen_value, br_responses,
                   prep_responses, accept_responses, clientVars, executionVars>>

\* Resubmit chosen_value via Preaccept.
Resubmit(i) ==
    /\ jstate[i] = AfterAccept
    /\ LET proposers == new_view[i].proposing_replica_ids
           msgSet == { [mtype |-> PreacceptRequest,
                        msource |-> i,
                        mdest |-> s,
                        mepoch |-> jepoch[i],
                        mview |-> new_view[i],
                        mcmd |-> cmd] :
                        s \in proposers, cmd \in chosen_value[i] }
       IN /\ messages' = AddMessages(msgSet, messages)
          /\ UNCHANGED <<baseVars,
                         jstate, jepoch, oepoch, old_view, new_view, jpool,
                         recovery_set, chosen_value, br_responses,
                         prep_responses, accept_responses, clientVars, executionVars>>

CompleteResubmit(i) ==
    /\ jstate[i] = AfterAccept
    /\ ChosenExecutedInView(i)
    /\ jstate' = [jstate EXCEPT ![i] = AfterResubmit]
    /\ UNCHANGED <<messages, baseVars,
                   jepoch, oepoch, old_view, new_view, jpool,
                   recovery_set, chosen_value, br_responses,
                   prep_responses, accept_responses, clientVars, executionVars>>

FinishRecovery(i) ==
    /\ jstate[i] = AfterResubmit
    /\ LET view == new_view[i]
           msgSet == { [mtype |-> FinishRecoveryRequest,
                        moepoch |-> oepoch[i],
                        mnew_view |-> view,
                        msource |-> i,
                        mdest |-> s] : s \in view.replica_ids }
       IN /\ messages' = AddMessages(msgSet, messages)
          /\ jepoch' = [jepoch EXCEPT ![i] = oepoch[i]]
          /\ oepoch' = [oepoch EXCEPT ![i] = oepoch[i]]
          /\ old_view' = [old_view EXCEPT ![i] = view]
          /\ new_view' = [new_view EXCEPT ![i] = view]
          /\ jpool' = [jpool EXCEPT ![i] = EmptyJPool]
          /\ jstate' = [jstate EXCEPT ![i] = Ready]
          /\ recovery_set' = [recovery_set EXCEPT ![i] = {}]
          /\ chosen_value' = [chosen_value EXCEPT ![i] = {}]
          /\ br_responses' = [br_responses EXCEPT ![i] = [s \in Server |-> NilJPool]]
          /\ prep_responses' = [prep_responses EXCEPT ![i] = [s \in Server |-> NilPrepResp]]
          /\ accept_responses' = [accept_responses EXCEPT ![i] = [s \in Server |-> FALSE]]
          /\ ostate' = [ostate EXCEPT ![i] = Leader]
    /\ UNCHANGED <<currentTerm, log, commitIndex,
                   clientVars, executionVars>>

HandleFinishRecovery(i, m) ==
    /\ m.mtype = FinishRecoveryRequest
    /\ i = m.mdest
    /\ jepoch' = [jepoch EXCEPT ![i] = m.moepoch]
    /\ oepoch' = [oepoch EXCEPT ![i] = m.moepoch]
    /\ old_view' = [old_view EXCEPT ![i] = m.mnew_view]
    /\ new_view' = [new_view EXCEPT ![i] = m.mnew_view]
    /\ jpool' = [jpool EXCEPT ![i] = EmptyJPool]
    /\ jstate' = [jstate EXCEPT ![i] = Ready]
    /\ recovery_set' = [recovery_set EXCEPT ![i] = {}]
    /\ chosen_value' = [chosen_value EXCEPT ![i] = {}]
    /\ ostate' = [ostate EXCEPT ![i] = IF ostate[i] = ToBeLeader THEN Leader ELSE ostate[i]]
    /\ Discard(m)
    /\ UNCHANGED <<currentTerm, log, commitIndex,
                   br_responses, prep_responses,
                   accept_responses, clientVars, executionVars>>

(***************************************************************************)
(* Jetpack-only Next (to be composed with base protocol Next)              *)
(***************************************************************************)

JetpackNext ==
    \/ \E c \in Client : ClientSendPreaccept(c)
    \/ \E i \in Server : SendBeginRecovery(i)
    \/ \E i \in Server : CompleteBeginRecovery(i)
    \/ \E i \in Server : SendPrepare(i)
    \/ \E i \in Server : CompletePrepare(i)
    \/ \E i \in Server : SendAccept(i)
    \/ \E i \in Server : CompleteAccept(i)
    \/ \E i \in Server : Resubmit(i)
    \/ \E i \in Server : CompleteResubmit(i)
    \/ \E i \in Server : FinishRecovery(i)

(***************************************************************************)
(* Properties                                                              *)
(* These quantify directly over the genuine 3-D log maintained by the      *)
(* base protocol. No projection operators are used.                        *)
(***************************************************************************)

\* Per-proposer committed log entries agree across servers.
\* For each proposer j, the committed prefix on server i must match server i2.
CommittedLogAgreement ==
    \A i, i2 \in Server :
        \A p \in Proposer :
            LET ci == commitIndex[i][p]
                ci2 == commitIndex[i2][p]
                limit == Min({ci, ci2} \cup {0})
            IN \A k \in 1..limit :
                /\ log[i][p][k].term = log[i2][p][k].term
                /\ log[i][p][k].value = log[i2][p][k].value

\* Per-proposer committed log agreement (same as CommittedLogAgreement
\* when commitIndex is per-proposer). Kept for backward compatibility
\* with the big-picture doc's naming.
MultiSequenceLogAgreement == CommittedLogAgreement

\* Per-sequence committed log order matches execution order for conflicting commands.
\* For each server i and each proposer p, the committed entries in proposer p's
\* sequence must preserve conflict order in the execution trace.
LogOrderMatchesExecution ==
    \A i \in Server :
        \A p \in Proposer :
            LET ci == commitIndex[i][p]
                cmdSeq == FilterNoOps([k \in 1..ci |-> log[i][p][k].value])
            IN ConflictOrderPreserved(cmdSeq, FilterNoOps(execution_cmds))

\* Conflict order between deduplicated original and replicated execution traces.
\* NoOp entries are filtered out as they are protocol-internal bookkeeping.
\* The relative order of any conflicting pair must be consistent across both traces.
ExecutionDedupMatches ==
    LET origDedup == Dedup(FilterNoOps(original_execution_cmds))
        execDedup == Dedup(FilterNoOps(execution_cmds))
    IN /\ ConflictOrderPreserved(origDedup, execDedup)
       /\ ConflictOrderPreserved(execDedup, origDedup)

=============================================================================
