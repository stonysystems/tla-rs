------------------------------ MODULE base_raft --------------------------------
\* Raft consensus protocol with add/remove reconfiguration, adapted for
\* Jetpack composition.
\*
\* This module is a port of Vanlightly's RaftWithReconfigAddRemove.tla
\* (now vendored verbatim at tla/raft.tla) to the Jetpack base-protocol
\* interface. Key changes from upstream:
\*
\*   1. ToBeLeader interception
\*      Upstream: Candidate -> Leader (BecomeLeader)
\*      Here:     Candidate -> ToBeLeader (BecomeToBeLeader);
\*                Jetpack's FinishRecovery transitions ToBeLeader -> Leader.
\*
\*   2. Two-step reconfig
\*      Upstream: AppendAddServerCommandToLog / AppendRemoveServerCommandToLog
\*                directly append a config entry from Leader.
\*      Here:     RequestReconfig(i, op, target) drops Leader to ToBeLeader,
\*                stashes the intent in pending_reconfig[i]. Jetpack recovery
\*                runs (the wrapper concurrently bumps new_view[i] / jepoch[i]).
\*                After FinishRecovery returns the server to Leader,
\*                AppendPendingReconfigToLog(i) emits the actual log entry.
\*
\*   3. 3-D log (log[i]["sole"][k], commitIndex[i]["sole"])
\*      Single proposer "sole" because Raft is a single-proposer protocol.
\*
\*   4. Snapshot machinery dropped
\*      Upstream's SendSnapshot / HandleSnapshotRequest / HandleSnapshotResponse
\*      and the pendingResponse variable are removed. New members catch up via
\*      plain AppendEntries from index 1 (less efficient for TLC, but smaller
\*      vocabulary; revisit if state space bites).
\*
\*   5. acked / valueCtr / Value dropped
\*      Replaced by Jetpack's Commands ([cmd_id, key]) at composition time.
\*      The LeaderHasAllAckedValues invariant is dropped; Jetpack's
\*      CommittedLogAgreement / LogOrderMatchesExecution provide stronger
\*      end-to-end guarantees.
\*
\*   6. ResetWithSameIdentity dropped (thesis-bug demo, not needed for first cut).

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC

\* Cluster members initially seeded into the protocol. The Init action puts
\* exactly these servers into the initial config (id=1, committed=TRUE);
\* every other server in Server starts as NotMember with empty log/term=0.
CONSTANTS Server, CmdId, Key, InitialMembers,
          MinClusterSize, MaxClusterSize,
          MaxElections, MaxRestarts,
          MaxAddReconfigs, MaxRemoveReconfigs,
          IncludeThesisBug

ASSUME InitialMembers \subseteq Server
ASSUME IncludeThesisBug \in BOOLEAN

\* ---- Server states ----
Follower   == "Follower"
Candidate  == "Candidate"
ToBeLeader == "ToBeLeader"
Leader     == "Leader"
NotMember  == "NotMember"

\* ---- Log entry command tags ----
AppendCommand       == "AppendCommand"
InitClusterCommand  == "InitClusterCommand"
AddServerCommand    == "AddServerCommand"
RemoveServerCommand == "RemoveServerCommand"

\* ---- Reserved sentinels ----
Nil    == "Nil"
NilCmd == [tag |-> "NilCmd"]

\* ---- AE response codes ----
Ok            == "Ok"
StaleTerm     == "StaleTerm"
EntryMismatch == "EntryMismatch"

\* ---- Reconfig op tags / pending-reconfig sentinel ----
ReconfigAdd    == "Add"
ReconfigRemove == "Remove"
NoReconfig     == [op |-> "None", target |-> Nil]

\* ---- Message types ----
RequestVoteRequest    == "RequestVoteRequest"
RequestVoteResponse   == "RequestVoteResponse"
AppendEntriesRequest  == "AppendEntriesRequest"
AppendEntriesResponse == "AppendEntriesResponse"

RaftMessageTypes == {RequestVoteRequest, RequestVoteResponse,
                     AppendEntriesRequest, AppendEntriesResponse}

EqualTerm        == "EqualTerm"
LessOrEqualTerm  == "LessOrEqualTerm"

(***************************************************************************)
(* Variables                                                               *)
(***************************************************************************)

VARIABLES
    messages,
    currentTerm,
    ostate,
    votedFor,
    log,                 \* log[i]["sole"][k]
    commitIndex,         \* commitIndex[i]["sole"]
    votesGranted,
    nextIndex,
    matchIndex,
    config,              \* config[i] = [id, members, committed]
    pending_reconfig,    \* pending_reconfig[i] = [op, target] or NoReconfig
    electionCtr, restartCtr, addReconfigCtr, removeReconfigCtr

serverVars    == <<config, currentTerm, ostate, votedFor>>
candidateVars == <<votesGranted>>
leaderVars    == <<nextIndex, matchIndex>>
logVars       == <<log, commitIndex>>
auxVars       == <<electionCtr, restartCtr, addReconfigCtr, removeReconfigCtr>>

\* Variables Jetpack reads/writes (the "base interface"):
\*   messages, currentTerm, ostate, log, commitIndex
\* Everything else is base_raft-only and the wrapper threads UNCHANGED for them
\* when Jetpack actions fire.
raftOnlyVars == <<votedFor, votesGranted, nextIndex, matchIndex,
                  config, pending_reconfig, electionCtr, restartCtr,
                  addReconfigCtr, removeReconfigCtr>>

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)

Commands == { [cmd_id |-> id, key |-> k] : id \in CmdId, k \in Key }

\* Quorum is over the (possibly time-varying) cluster member set.
Quorum(cluster) == {q \in SUBSET cluster : Cardinality(q) * 2 > Cardinality(cluster)}

Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* 3-D log accessors (read-only convenience).
ServerLog(i)    == log[i]["sole"]
ServerCommit(i) == commitIndex[i]["sole"]

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

(* ---- Message-bag plumbing (mirrors Vanlightly verbatim) ---- *)
_SendNoRestriction(m) ==
    IF m \in DOMAIN messages
    THEN messages' = [messages EXCEPT ![m] = @ + 1]
    ELSE messages' = messages @@ (m :> 1)

_SendOnce(m) ==
    /\ m \notin DOMAIN messages
    /\ messages' = messages @@ (m :> 1)

\* Empty AE requests can only be sent once (prevents infinite cycles).
Send(m) ==
    IF /\ m.mtype = AppendEntriesRequest
       /\ m.mentries = <<>>
    THEN _SendOnce(m)
    ELSE _SendNoRestriction(m)

SendMultipleOnce(msgs) ==
    /\ \A m \in msgs : m \notin DOMAIN messages
    /\ messages' = messages @@ [msg \in msgs |-> 1]

Discard(m) ==
    /\ m \in DOMAIN messages
    /\ messages[m] > 0
    /\ messages' = [messages EXCEPT ![m] = @ - 1]

Reply(response, request) ==
    /\ messages[request] > 0
    /\ \/ /\ response \notin DOMAIN messages
          /\ messages' = [messages EXCEPT ![request] = @ - 1] @@ (response :> 1)
       \/ /\ response \in DOMAIN messages
          /\ messages' = [messages EXCEPT ![request] = @ - 1,
                                          ![response] = @ + 1]

ReceivableMessage(m, mtype, term_match) ==
    /\ messages[m] > 0
    /\ m.mtype = mtype
    /\ \/ /\ term_match = EqualTerm
          /\ m.mterm = currentTerm[m.mdest]
       \/ /\ term_match = LessOrEqualTerm
          /\ m.mterm <= currentTerm[m.mdest]

(* ---- Config helpers ---- *)
IsConfigCommand(serverLog, index) ==
    serverLog[index].command \in {InitClusterCommand, AddServerCommand, RemoveServerCommand}

HasPendingConfigCommand(i) == config[i].committed = FALSE

MostRecentReconfigEntry(serverLog) ==
    LET index == CHOOSE index \in DOMAIN serverLog :
                    /\ IsConfigCommand(serverLog, index)
                    /\ ~\E index2 \in DOMAIN serverLog :
                        /\ IsConfigCommand(serverLog, index2)
                        /\ index2 > index
    IN [index |-> index, entry |-> serverLog[index]]

NoConfig == [id |-> 0, members |-> {}, committed |-> FALSE]

ConfigFor(index, reconfigEntry, ci) ==
    [id        |-> reconfigEntry.value.id,
     members   |-> reconfigEntry.value.members,
     committed |-> ci >= index]

LeaderHasCommittedEntriesInCurrentTerm(i) ==
    \E index \in DOMAIN ServerLog(i) :
        /\ ServerLog(i)[index].term = currentTerm[i]
        /\ ServerCommit(i) >= index

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

InitBaseVars ==
    LET members    == InitialMembers
        leader     == CHOOSE i \in members : TRUE
        \* Config-entry values include cmd_id/key sentinels so Jetpack helpers
        \* that walk every log entry's .value.cmd_id (e.g. LogCmdIds) don't
        \* trip on the polymorphic value field.
        firstEntry == [command |-> InitClusterCommand,
                       term    |-> 1,
                       value   |-> [cmd_id  |-> Nil,
                                    key     |-> Nil,
                                    id      |-> 1,
                                    members |-> members]]
    IN
        /\ messages = [m \in {} |-> 0]
        /\ currentTerm = [i \in Server |-> IF i \in members THEN 1 ELSE 0]
        /\ ostate = [i \in Server |->
                       CASE i = leader -> Leader
                         [] i \in members -> Follower
                         [] OTHER -> NotMember]
        /\ votedFor = [i \in Server |-> Nil]
        /\ config = [i \in Server |->
                       IF i \in members
                       THEN [id |-> 1, members |-> members, committed |-> TRUE]
                       ELSE NoConfig]
        /\ log = [i \in Server |->
                    [x \in {"sole"} |->
                       IF i \in members THEN << firstEntry >> ELSE << >>]]
        /\ commitIndex = [i \in Server |->
                            [x \in {"sole"} |->
                               IF i \in members THEN 1 ELSE 0]]
        /\ votesGranted = [i \in Server |-> {}]
        /\ nextIndex = [i \in Server |-> [j \in Server |->
                          IF i = leader /\ j \in members THEN 2 ELSE 1]]
        /\ matchIndex = [i \in Server |-> [j \in Server |->
                          IF i = leader /\ j \in members THEN 1 ELSE 0]]
        /\ pending_reconfig = [i \in Server |-> NoReconfig]
        /\ electionCtr = 0
        /\ restartCtr = 0
        /\ addReconfigCtr = 0
        /\ removeReconfigCtr = 0

(***************************************************************************)
(* Restart                                                                 *)
(* Loses non-durable state. log/term/votedFor/config persist.              *)
(***************************************************************************)

Restart(i) ==
    /\ restartCtr < MaxRestarts
    /\ ostate'           = [ostate EXCEPT ![i] =
                              IF i \in config[i].members THEN Follower ELSE NotMember]
    /\ votesGranted'     = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'        = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'       = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'      = [commitIndex EXCEPT ![i]["sole"] = 0]
    /\ pending_reconfig' = [pending_reconfig EXCEPT ![i] = NoReconfig]
    /\ restartCtr'       = restartCtr + 1
    /\ UNCHANGED <<messages, config, currentTerm, votedFor, log,
                   electionCtr, addReconfigCtr, removeReconfigCtr>>

(***************************************************************************)
(* UpdateTerm: process any incoming message with a higher term first.      *)
(***************************************************************************)

UpdateTerm ==
    \E m \in DOMAIN messages :
        /\ m.mtype \in RaftMessageTypes
        /\ m.mterm > currentTerm[m.mdest]
        /\ currentTerm' = [currentTerm EXCEPT ![m.mdest] = m.mterm]
        /\ ostate'      = [ostate EXCEPT ![m.mdest] = Follower]
        /\ votedFor'    = [votedFor EXCEPT ![m.mdest] = Nil]
        /\ UNCHANGED <<messages, config, candidateVars, leaderVars, logVars,
                       pending_reconfig, auxVars>>

(***************************************************************************)
(* Elections                                                               *)
(***************************************************************************)

\* Combined Timeout + RequestVote.
RequestVote(i) ==
    /\ electionCtr < MaxElections
    /\ ostate[i] \in {Follower, Candidate}
    /\ i \in config[i].members
    /\ ostate'       = [ostate EXCEPT ![i] = Candidate]
    /\ currentTerm'  = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor'     = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ electionCtr'  = electionCtr + 1
    /\ SendMultipleOnce(
           {[mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i] + 1,
             mlastLogTerm  |-> LastTerm(ServerLog(i)),
             mlastLogIndex |-> Len(ServerLog(i)),
             msource       |-> i,
             mdest         |-> j] : j \in config[i].members \ {i}})
    /\ UNCHANGED <<config, leaderVars, logVars, pending_reconfig,
                   restartCtr, addReconfigCtr, removeReconfigCtr>>

HandleRequestVoteRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == \/ m.mlastLogTerm > LastTerm(ServerLog(i))
                        \/ /\ m.mlastLogTerm = LastTerm(ServerLog(i))
                           /\ m.mlastLogIndex >= Len(ServerLog(i))
               grant == /\ m.mterm = currentTerm[i]
                        /\ logOk
                        /\ votedFor[i] \in {Nil, j}
           IN /\ m.mterm <= currentTerm[i]
              /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
                 \/ ~grant /\ UNCHANGED votedFor
              /\ Reply([mtype        |-> RequestVoteResponse,
                        mterm        |-> currentTerm[i],
                        mvoteGranted |-> grant,
                        msource      |-> i,
                        mdest        |-> j], m)
              /\ UNCHANGED <<config, ostate, currentTerm, candidateVars,
                             leaderVars, logVars, pending_reconfig, auxVars>>

HandleRequestVoteResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, RequestVoteResponse, EqualTerm)
        /\ LET i == m.mdest
               j == m.msource
           IN /\ ostate[i] = Candidate
              /\ \/ /\ m.mvoteGranted
                    /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                            votesGranted[i] \cup {j}]
                 \/ /\ ~m.mvoteGranted
                    /\ UNCHANGED <<votesGranted>>
              /\ Discard(m)
              /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                             pending_reconfig, auxVars>>

\* Replaces upstream BecomeLeader. Candidate transitions to ToBeLeader;
\* Jetpack's FinishRecovery is what subsequently moves to Leader.
BecomeToBeLeader(i) ==
    /\ ostate[i] = Candidate
    /\ votesGranted[i] \in Quorum(config[i].members)
    /\ ostate'     = [ostate EXCEPT ![i] = ToBeLeader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                        [j \in Server |-> Len(ServerLog(i)) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ UNCHANGED <<messages, config, currentTerm, votedFor, candidateVars,
                   logVars, pending_reconfig, auxVars>>

(***************************************************************************)
(* Replication                                                             *)
(***************************************************************************)

\* Leader appends a client AppendCommand entry. Note: Jetpack's Preaccept
\* path also writes to the log directly via HandlePreacceptRequest. Both
\* paths coexist — ClientRequest is the "Raft-only" path used for testing
\* leader-side replication independently of Jetpack's recovery machinery.
ClientRequest(i, v) ==
    /\ ostate[i] = Leader
    /\ v \in Commands
    /\ LET entry  == [command |-> AppendCommand,
                      term    |-> currentTerm[i],
                      value   |-> v]
           newLog == Append(ServerLog(i), entry)
       IN log' = [log EXCEPT ![i]["sole"] = newLog]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars,
                   commitIndex, pending_reconfig, auxVars>>

AppendEntries(i, j) ==
    /\ i /= j
    /\ ostate[i] = Leader
    /\ j \in config[i].members
    /\ nextIndex[i][j] >= 1
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm  == IF prevLogIndex > 0
                           THEN ServerLog(i)[prevLogIndex].term
                           ELSE 0
           lastEntry    == Min({Len(ServerLog(i)), nextIndex[i][j]})
           entries      == SubSeq(ServerLog(i), nextIndex[i][j], lastEntry)
       IN Send([mtype         |-> AppendEntriesRequest,
                mterm         |-> currentTerm[i],
                mprevLogIndex |-> prevLogIndex,
                mprevLogTerm  |-> prevLogTerm,
                mentries      |-> entries,
                mcommitIndex  |-> Min({ServerCommit(i), lastEntry}),
                msource       |-> i,
                mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, nextIndex, matchIndex, logVars,
                   pending_reconfig, auxVars>>

LogOk(i, m) ==
    IF m.mentries # <<>>
    THEN /\ m.mprevLogIndex > 0
         /\ m.mprevLogIndex <= Len(ServerLog(i))
         /\ m.mprevLogTerm = ServerLog(i)[m.mprevLogIndex].term
    ELSE
         /\ m.mentries = <<>>
         /\ m.mprevLogIndex = Len(ServerLog(i))
         /\ \/ m.mprevLogIndex = 0
            \/ m.mprevLogTerm = ServerLog(i)[m.mprevLogIndex].term

RejectAppendEntriesRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesRequest, LessOrEqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == LogOk(i, m)
               rc    == CASE m.mterm < currentTerm[i] -> StaleTerm
                          [] /\ m.mterm = currentTerm[i]
                             /\ ostate[i] = Follower
                             /\ \lnot logOk -> EntryMismatch
                          [] OTHER -> Ok
           IN /\ rc # Ok
              /\ Reply([mtype       |-> AppendEntriesResponse,
                        mterm       |-> currentTerm[i],
                        mresult     |-> rc,
                        mmatchIndex |-> 0,
                        msource     |-> i,
                        mdest       |-> j], m)
              /\ UNCHANGED <<ostate, candidateVars, leaderVars, serverVars,
                             logVars, pending_reconfig, auxVars>>

CanAppend(m, i) ==
    /\ m.mentries # <<>>
    /\ Len(ServerLog(i)) = m.mprevLogIndex

NeedsTruncation(m, i, index) ==
    /\ m.mentries # <<>>
    /\ Len(ServerLog(i)) >= index

TruncateLog(m, i) == [index \in 1..m.mprevLogIndex |-> ServerLog(i)[index]]

\* Compressed accept-AE: in one step truncate (if needed), append, apply
\* config entry to local config (immediately, even if uncommitted).
AcceptAppendEntriesRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesRequest, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == LogOk(i, m)
               index == m.mprevLogIndex + 1
           IN /\ ostate[i] \in {Follower, Candidate}
              /\ logOk
              /\ LET newSoleLog == IF CanAppend(m, i)
                                   THEN Append(ServerLog(i), m.mentries[1])
                                   ELSE IF NeedsTruncation(m, i, index)
                                        THEN Append(TruncateLog(m, i), m.mentries[1])
                                        ELSE ServerLog(i)
                     hasConfig  == \E k \in DOMAIN newSoleLog : IsConfigCommand(newSoleLog, k)
                     configEntry == IF hasConfig
                                    THEN MostRecentReconfigEntry(newSoleLog)
                                    ELSE [index |-> 0,
                                          entry |-> [command |-> InitClusterCommand,
                                                     term    |-> 0,
                                                     value   |-> [id      |-> 0,
                                                                  members |-> {}]]]
                     currConfig == IF hasConfig
                                   THEN ConfigFor(configEntry.index,
                                                  configEntry.entry,
                                                  m.mcommitIndex)
                                   ELSE config[i]
                 IN /\ config'      = [config EXCEPT ![i] = currConfig]
                    /\ commitIndex' = [commitIndex EXCEPT ![i]["sole"] = m.mcommitIndex]
                    /\ ostate'      = [ostate EXCEPT ![i] =
                                         IF i \in currConfig.members
                                         THEN Follower
                                         ELSE NotMember]
                    /\ log'         = [log EXCEPT ![i]["sole"] = newSoleLog]
                    /\ Reply([mtype       |-> AppendEntriesResponse,
                              mterm       |-> currentTerm[i],
                              mresult     |-> Ok,
                              mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                              msource     |-> i,
                              mdest       |-> j], m)
                    /\ UNCHANGED <<candidateVars, leaderVars, votedFor, currentTerm,
                                   pending_reconfig, auxVars>>

HandleAppendEntriesResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesResponse, EqualTerm)
        /\ LET i == m.mdest
               j == m.msource
           IN /\ ostate[i] = Leader
              /\ \/ /\ m.mresult = Ok
                    /\ nextIndex'  = [nextIndex EXCEPT ![i][j] = m.mmatchIndex + 1]
                    /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                 \/ /\ m.mresult = EntryMismatch
                    /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                                         Max({nextIndex[i][j] - 1, 1})]
                    /\ UNCHANGED <<matchIndex>>
                 \/ /\ m.mresult = StaleTerm
                    /\ UNCHANGED <<nextIndex, matchIndex>>
              /\ Discard(m)
              /\ UNCHANGED <<serverVars, candidateVars, logVars,
                             pending_reconfig, auxVars>>

(***************************************************************************)
(* AdvanceCommitIndex: commit, propagate config commit, possibly self-remove *)
(***************************************************************************)

IsRemovedFromCluster(i, newCommitIndex) ==
    \E index \in DOMAIN ServerLog(i) :
        /\ index > ServerCommit(i)
        /\ index <= newCommitIndex
        /\ ServerLog(i)[index].command = RemoveServerCommand
        /\ i \notin ServerLog(i)[index].value.members

AdvanceCommitIndex(i) ==
    /\ ostate[i] = Leader
    /\ LET soleLog == ServerLog(i)
           Agree(index, memberSet) ==
               IF i \in memberSet
               THEN {i} \cup {k \in memberSet : matchIndex[i][k] >= index}
               ELSE {k \in memberSet : matchIndex[i][k] >= index}
           agreeIndexes == {index \in 1..Len(soleLog) :
                              Agree(index, config[i].members) \in Quorum(config[i].members)}
           newCommitIndex ==
               IF /\ agreeIndexes /= {}
                  /\ soleLog[Max(agreeIndexes)].term = currentTerm[i]
               THEN Max(agreeIndexes)
               ELSE ServerCommit(i)
           currConfig == MostRecentReconfigEntry(soleLog)
       IN /\ ServerCommit(i) < newCommitIndex
          /\ config' = [config EXCEPT ![i] = ConfigFor(currConfig.index, currConfig.entry, newCommitIndex)]
          /\ IF IsRemovedFromCluster(i, newCommitIndex)
             THEN /\ ostate'       = [ostate EXCEPT ![i] = NotMember]
                  /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
                  /\ nextIndex'    = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
                  /\ matchIndex'   = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
                  /\ commitIndex'  = [commitIndex EXCEPT ![i]["sole"] = 0]
             ELSE /\ commitIndex'  = [commitIndex EXCEPT ![i]["sole"] = newCommitIndex]
                  /\ UNCHANGED <<ostate, votesGranted, nextIndex, matchIndex>>
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, pending_reconfig, auxVars>>

(***************************************************************************)
(* Reconfiguration: two-step, gated by Jetpack recovery                    *)
(*                                                                         *)
(*   Leader ──RequestReconfig──▶ ToBeLeader                                *)
(*                                  │                                      *)
(*                            (wrapper bumps new_view + jepoch)            *)
(*                                  │                                      *)
(*                            Jetpack recovery runs                        *)
(*                                  │                                      *)
(*                          FinishRecovery sets ostate = Leader            *)
(*                                  │                                      *)
(*       AppendPendingReconfigToLog ──▶ entry appended to log              *)
(*                                                                         *)
(* The wrapper provides the view update; this module only mutates the      *)
(* protocol-layer variables (ostate, pending_reconfig, counters).          *)
(***************************************************************************)

RequestReconfig(i, op, target) ==
    /\ ostate[i] = Leader
    /\ i \in config[i].members
    /\ pending_reconfig[i] = NoReconfig
    /\ \lnot HasPendingConfigCommand(i)
    /\ IF ~IncludeThesisBug
       THEN LeaderHasCommittedEntriesInCurrentTerm(i)
       ELSE TRUE
    /\ \/ /\ op = ReconfigAdd
          /\ target \notin config[i].members
          /\ Cardinality(config[i].members) < MaxClusterSize
          /\ addReconfigCtr < MaxAddReconfigs
          /\ addReconfigCtr' = addReconfigCtr + 1
          /\ UNCHANGED removeReconfigCtr
       \/ /\ op = ReconfigRemove
          /\ target \in config[i].members
          /\ Cardinality(config[i].members) > MinClusterSize
          /\ removeReconfigCtr < MaxRemoveReconfigs
          /\ removeReconfigCtr' = removeReconfigCtr + 1
          /\ UNCHANGED addReconfigCtr
    /\ ostate'           = [ostate EXCEPT ![i] = ToBeLeader]
    /\ pending_reconfig' = [pending_reconfig EXCEPT ![i] = [op |-> op, target |-> target]]
    /\ UNCHANGED <<messages, config, currentTerm, votedFor, candidateVars,
                   leaderVars, logVars, electionCtr, restartCtr>>

\* Fired only after Jetpack recovery completes (FinishRecovery has set
\* ostate back to Leader). Emits the actual config-log entry.
AppendPendingReconfigToLog(i) ==
    /\ ostate[i] = Leader
    /\ pending_reconfig[i] /= NoReconfig
    /\ LET pr        == pending_reconfig[i]
           cmdTag    == IF pr.op = ReconfigAdd THEN AddServerCommand ELSE RemoveServerCommand
           newMembers == IF pr.op = ReconfigAdd
                         THEN config[i].members \cup {pr.target}
                         ELSE config[i].members \ {pr.target}
           \* cmd_id/key sentinels keep Jetpack's LogCmdIds happy.
           valueRec  == IF pr.op = ReconfigAdd
                        THEN [cmd_id  |-> Nil,
                              key     |-> Nil,
                              id      |-> config[i].id + 1,
                              new     |-> pr.target,
                              members |-> newMembers]
                        ELSE [cmd_id  |-> Nil,
                              key     |-> Nil,
                              id      |-> config[i].id + 1,
                              old     |-> pr.target,
                              members |-> newMembers]
           entry     == [command |-> cmdTag,
                         term    |-> currentTerm[i],
                         value   |-> valueRec]
           newLog    == Append(ServerLog(i), entry)
       IN /\ log'    = [log EXCEPT ![i]["sole"] = newLog]
          /\ config' = [config EXCEPT ![i] = ConfigFor(Len(newLog), entry, ServerCommit(i))]
    /\ pending_reconfig' = [pending_reconfig EXCEPT ![i] = NoReconfig]
    /\ UNCHANGED <<messages, currentTerm, votedFor, ostate, candidateVars,
                   leaderVars, commitIndex, auxVars>>

(***************************************************************************)
(* Raft message receive dispatch                                           *)
(***************************************************************************)

\* Single dispatcher used by the wrapper. Fires the appropriate sub-action
\* based on message type. UpdateTerm is also exposed standalone since it
\* may apply to a message that hasn't been fully consumed yet.
RaftReceive ==
    \/ HandleRequestVoteRequest
    \/ HandleRequestVoteResponse
    \/ RejectAppendEntriesRequest
    \/ AcceptAppendEntriesRequest
    \/ HandleAppendEntriesResponse

(***************************************************************************)
(* Protocol Next (used only for standalone testing of base_raft)           *)
(* The Jetpack composition wrapper builds its own Next.                    *)
(***************************************************************************)

BaseNext ==
    \/ \E i \in Server : Restart(i)
    \/ UpdateTerm
    \/ \E i \in Server : RequestVote(i)
    \/ \E i \in Server : BecomeToBeLeader(i)
    \/ \E i \in Server : AdvanceCommitIndex(i)
    \/ \E i, j \in Server : AppendEntries(i, j)
    \/ \E i \in Server, v \in Commands : ClientRequest(i, v)
    \/ \E i \in Server, op \in {ReconfigAdd, ReconfigRemove}, t \in Server :
            RequestReconfig(i, op, t)
    \/ \E i \in Server : AppendPendingReconfigToLog(i)
    \/ RaftReceive

=============================================================================
