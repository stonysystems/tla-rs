--------------------------- MODULE base_raft_clean --------------------------
(***************************************************************************)
(* Jetpack's base Raft layer, rewritten into the clean subset (C1-C5).     *)
(*                                                                         *)
(* This is a **library module**: it declares the base protocol's state and *)
(* defines its actions, but has no `Init`/`Next` of its own. The spec is   *)
(* `jetpack_raft_clean`, which INSTANCEs this and the Jetpack layer and    *)
(* composes their actions -- exactly as the original three modules do.     *)
(* Linting this file alone therefore reports "no next-state relation", and *)
(* that is correct: a library is not a spec.                               *)
(*                                                                         *)
(* Rewrite decisions, all recorded in rewrite.md:                          *)
(*                                                                         *)
(*  - `messages` was a **bag** (a message -> count function) so that        *)
(*    duplication could be modelled. It becomes one set. Duplication is    *)
(*    lost; the original's `SendMultipleOnce` already de-duplicated, and    *)
(*    nothing in the protocol reads a count.                                *)
(*  - `log[i]["sole"]` loses its middle index. base_raft hardcodes the      *)
(*    string `"sole"` everywhere rather than quantifying over proposers,    *)
(*    so this is exact rather than a specialisation.                        *)
(*  - The four global counters become **per-node**. They exist only to      *)
(*    bound model checking; a global budget cannot survive projection,      *)
(*    and a per-node budget keeps the bounding mechanism explicit instead   *)
(*    of moving it into a cfg constraint.                                   *)
(*  - Every `\E m \in DOMAIN messages : ... LET i == m.mdest` becomes a     *)
(*    handler `H(i, m)` guarded on `m.mdest = i`. The composition then      *)
(*    binds the node, which is what C5 asks for.                            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Node, Server, Commands, MaxTerm, MaxLogLen, MaxElections, MaxRestarts

(***************************************************************************)
(* Server states. `ToBeLeader` is Jetpack's addition: a candidate that won  *)
(* an election waits there until recovery finishes before becoming Leader.  *)
(***************************************************************************)
Follower   == "follower"
Candidate  == "candidate"
ToBeLeader == "toBeLeader"
Leader     == "leader"
NotMember  == "notMember"

Nil == 0

(***************************************************************************)
(* Log entry commands.                                                     *)
(***************************************************************************)
AppendCommand       == "append"
InitClusterCommand  == "initCluster"
AddServerCommand    == "addServer"
RemoveServerCommand == "removeServer"

ReconfigAdd    == "add"
ReconfigRemove == "remove"
NoReconfig     == [op |-> "none", target |-> 0]

(***************************************************************************)
(* Message tags.                                                           *)
(***************************************************************************)
RequestVoteRequest    == "rvq"
RequestVoteResponse   == "rvp"
AppendEntriesRequest  == "aeq"
AppendEntriesResponse == "aep"

(* C4 gives the composition ONE network, so this module's actions see       *)
(* Jetpack's messages too. Only these four carry `mterm`, and `UpdateTerm`  *)
(* is the one action that reads a field before knowing the message is its   *)
(* own -- TLC caught it reading `mterm` off a `paq`.                        *)
TermCarrying == {RequestVoteRequest, RequestVoteResponse,
                 AppendEntriesRequest, AppendEntriesResponse}

Ok            == "ok"
StaleTerm     == "staleTerm"
EntryMismatch == "entryMismatch"

VARIABLES
  currentTerm,      \* this server's term
  ostate,           \* follower / candidate / toBeLeader / leader / notMember
  votedFor,         \* who this server voted for this term, Nil if nobody
  log,              \* this server's log
  commitIndex,      \* how far this server has committed
  votesGranted,     \* servers that granted this server a vote
  nextIndex,        \* per peer: next index to send
  matchIndex,       \* per peer: highest index known replicated
  config,           \* this server's view of the cluster
  pendingReconfig,  \* a reconfiguration this server has requested
  electionCtr,      \* per-node model-checking budget
  restartCtr,
  msgs              \* messages sent

Term  == 1 .. MaxTerm
Index == 0 .. MaxLogLen

Entry == [command: {AppendCommand, InitClusterCommand,
                    AddServerCommand, RemoveServerCommand},
          term: 0 .. MaxTerm,
          value: Commands]

Config == [id: Index, members: SUBSET Server, committed: BOOLEAN]

Max(s) == CHOOSE x \in s : \A y \in s : x >= y
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

(***************************************************************************)
(* P4. The original quantifies over `Quorum(config[i].members)`, a set of   *)
(* subsets. A server cannot evaluate that; it can count what it has heard.  *)
(***************************************************************************)
IsQuorumOf(s, members) == Cardinality(s) * 2 > Cardinality(members)

Message ==
       [mtype: {RequestVoteRequest}, mterm: Term,
        mlastLogTerm: 0 .. MaxTerm, mlastLogIndex: Index,
        msource: Server, mdest: Server]
  \cup [mtype: {RequestVoteResponse}, mterm: Term, mvoteGranted: BOOLEAN,
        msource: Server, mdest: Server]
  \cup [mtype: {AppendEntriesRequest}, mterm: Term,
        mprevLogIndex: Index, mprevLogTerm: 0 .. MaxTerm,
        mentries: Seq(Entry), mcommitIndex: Index,
        msource: Server, mdest: Server]
  \cup [mtype: {AppendEntriesResponse}, mterm: Term,
        mresult: {Ok, StaleTerm, EntryMismatch}, mmatchIndex: Index,
        msource: Server, mdest: Server]

RVReq(s, d, t, lt, li) ==
  [mtype |-> RequestVoteRequest, mterm |-> t, mlastLogTerm |-> lt,
   mlastLogIndex |-> li, msource |-> s, mdest |-> d]

RVResp(s, d, t, g) ==
  [mtype |-> RequestVoteResponse, mterm |-> t, mvoteGranted |-> g,
   msource |-> s, mdest |-> d]

AEReq(s, d, t, pli, plt, ents, ci) ==
  [mtype |-> AppendEntriesRequest, mterm |-> t, mprevLogIndex |-> pli,
   mprevLogTerm |-> plt, mentries |-> ents, mcommitIndex |-> ci,
   msource |-> s, mdest |-> d]

AEResp(s, d, t, r, mi) ==
  [mtype |-> AppendEntriesResponse, mterm |-> t, mresult |-> r,
   mmatchIndex |-> mi, msource |-> s, mdest |-> d]

BroadcastRequestVote(i, t, lt, li, members) ==
  { RVReq(i, j, t, lt, li) : j \in members }

BaseTypeOK ==
  /\ currentTerm \in [Node -> Term]
  /\ ostate \in [Node -> {Follower, Candidate, ToBeLeader, Leader, NotMember}]
  /\ votedFor \in [Node -> Server \cup {Nil}]
  /\ log \in [Node -> Seq(Entry)]
  /\ commitIndex \in [Node -> Index]
  /\ votesGranted \in [Node -> SUBSET Server]
  (* Inner domain is `Server`, not `Node`: a leader tracks its followers, and *)
  (* a client is never one. TLC caught this the moment a leader existed.      *)
  /\ nextIndex \in [Node -> [Server -> 1 .. MaxLogLen + 1]]
  /\ matchIndex \in [Node -> [Server -> Index]]
  /\ config \in [Node -> Config]
  /\ electionCtr \in [Node -> 0 .. MaxElections]
  /\ restartCtr \in [Node -> 0 .. MaxRestarts]
  /\ pendingReconfig \in [Node -> [op: {ReconfigAdd, ReconfigRemove, "none"},
                                   target: Server \cup {Nil}]]

(***************************************************************************)
(* Restart. Loses non-durable state; log, term, votedFor and config persist.*)
(***************************************************************************)
Restart(i) ==
  /\ restartCtr[i] < MaxRestarts
  /\ ostate' = [ostate EXCEPT ![i] =
                  IF i \in config[i].members THEN Follower ELSE NotMember]
  /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
  /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
  /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
  /\ commitIndex' = [commitIndex EXCEPT ![i] = 0]
  /\ pendingReconfig' = [pendingReconfig EXCEPT ![i] = NoReconfig]
  /\ restartCtr' = [restartCtr EXCEPT ![i] = restartCtr[i] + 1]
  /\ msgs' = msgs
  /\ UNCHANGED <<currentTerm, votedFor, log, config, electionCtr>>

(***************************************************************************)
(* A message carrying a higher term demotes the receiver first.            *)
(*                                                                         *)
(* The original writes this as `\E m \in DOMAIN messages : ... m.mdest`,    *)
(* i.e. an environment action that reaches into whichever node the message  *)
(* names. Here the node is bound by the caller and the message is checked   *)
(* against it, which is the same set of steps stated so a node can take one.*)
(***************************************************************************)
UpdateTerm(i, m) ==
  /\ m.mtype \in TermCarrying
  /\ m.mdest = i
  /\ m.mterm > currentTerm[i]
  /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
  /\ ostate' = [ostate EXCEPT ![i] = Follower]
  /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
  /\ msgs' = msgs
  /\ UNCHANGED <<log, commitIndex, votesGranted, nextIndex, matchIndex,
                 config, pendingReconfig, electionCtr, restartCtr>>

(***************************************************************************)
(* Elections. Timeout and RequestVote are one step, as upstream.           *)
(***************************************************************************)
RequestVote(i) ==
  /\ electionCtr[i] < MaxElections
  /\ currentTerm[i] < MaxTerm
  /\ ostate[i] \in {Follower, Candidate}
  /\ i \in config[i].members
  /\ ostate' = [ostate EXCEPT ![i] = Candidate]
  /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
  /\ votedFor' = [votedFor EXCEPT ![i] = i]
  /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
  /\ electionCtr' = [electionCtr EXCEPT ![i] = electionCtr[i] + 1]
  /\ msgs' = msgs \cup BroadcastRequestVote(i, currentTerm[i] + 1,
                                            LastTerm(log[i]), Len(log[i]),
                                            config[i].members)
  /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, config,
                 pendingReconfig, restartCtr>>

HandleRequestVoteRequest(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = RequestVoteRequest
  /\ m.mterm <= currentTerm[i]
  /\ votedFor' =
       IF /\ m.mterm = currentTerm[i]
          /\ \/ m.mlastLogTerm > LastTerm(log[i])
             \/ /\ m.mlastLogTerm = LastTerm(log[i])
                /\ m.mlastLogIndex >= Len(log[i])
          /\ votedFor[i] \in {Nil, m.msource}
         THEN [votedFor EXCEPT ![i] = m.msource]
         ELSE votedFor
  /\ msgs' = (msgs \ {m}) \cup
       {RVResp(i, m.msource, currentTerm[i],
               /\ m.mterm = currentTerm[i]
               /\ \/ m.mlastLogTerm > LastTerm(log[i])
                  \/ /\ m.mlastLogTerm = LastTerm(log[i])
                     /\ m.mlastLogIndex >= Len(log[i])
               /\ votedFor[i] \in {Nil, m.msource})}
  /\ UNCHANGED <<currentTerm, ostate, log, commitIndex, votesGranted,
                 nextIndex, matchIndex, config, pendingReconfig,
                 electionCtr, restartCtr>>

HandleRequestVoteResponse(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = RequestVoteResponse
  /\ m.mterm = currentTerm[i]
  /\ ostate[i] = Candidate
  /\ votesGranted' =
       IF m.mvoteGranted
         THEN [votesGranted EXCEPT ![i] = votesGranted[i] \cup {m.msource}]
         ELSE votesGranted
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<currentTerm, ostate, votedFor, log, commitIndex,
                 nextIndex, matchIndex, config, pendingReconfig,
                 electionCtr, restartCtr>>

(***************************************************************************)
(* A candidate that has a quorum becomes ToBeLeader -- not Leader. Jetpack's*)
(* FinishRecovery is what promotes it, and that coupling is the whole point *)
(* of the composition.                                                     *)
(***************************************************************************)
BecomeToBeLeader(i) ==
  /\ ostate[i] = Candidate
  /\ IsQuorumOf(votesGranted[i], config[i].members)
  /\ ostate' = [ostate EXCEPT ![i] = ToBeLeader]
  /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> Len(log[i]) + 1]]
  /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
  /\ msgs' = msgs
  /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex,
                 votesGranted, config, pendingReconfig, electionCtr,
                 restartCtr>>

(***************************************************************************)
(* Replication.                                                            *)
(***************************************************************************)
ClientRequest(i, v) ==
  /\ ostate[i] = Leader
  /\ Len(log[i]) < MaxLogLen
  /\ log' = [log EXCEPT ![i] =
               Append(log[i], [command |-> AppendCommand,
                               term |-> currentTerm[i], value |-> v])]
  /\ msgs' = msgs
  /\ UNCHANGED <<currentTerm, ostate, votedFor, commitIndex, votesGranted,
                 nextIndex, matchIndex, config, pendingReconfig,
                 electionCtr, restartCtr>>

AppendEntries(i, j) ==
  /\ i # j
  /\ ostate[i] = Leader
  /\ j \in config[i].members
  /\ nextIndex[i][j] >= 1
  /\ msgs' = msgs \cup
       {AEReq(i, j, currentTerm[i],
              nextIndex[i][j] - 1,
              IF nextIndex[i][j] - 1 > 0
                THEN log[i][nextIndex[i][j] - 1].term
                ELSE 0,
              SubSeq(log[i], nextIndex[i][j],
                     IF Len(log[i]) < nextIndex[i][j]
                       THEN Len(log[i]) ELSE nextIndex[i][j]),
              IF commitIndex[i] < nextIndex[i][j]
                THEN commitIndex[i] ELSE nextIndex[i][j])}
  /\ UNCHANGED <<currentTerm, ostate, votedFor, log, commitIndex,
                 votesGranted, nextIndex, matchIndex, config,
                 pendingReconfig, electionCtr, restartCtr>>

LogOk(i, m) ==
  IF m.mentries # << >>
    THEN /\ m.mprevLogIndex > 0
         /\ m.mprevLogIndex <= Len(log[i])
         /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    ELSE /\ m.mprevLogIndex = Len(log[i])
         (* The `> 0` is not redundant with the disjunct above it: TLC        *)
         (* evaluated `log[i][0]` on an empty log here. Guarding the index    *)
         (* cannot change LogOk's value -- at index 0 the first disjunct is   *)
         (* already TRUE -- it only removes an evaluation that is an error.   *)
         /\ \/ m.mprevLogIndex = 0
            \/ /\ m.mprevLogIndex > 0
               /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term

RejectAppendEntriesRequest(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = AppendEntriesRequest
  /\ m.mterm <= currentTerm[i]
  /\ \/ m.mterm < currentTerm[i]
     \/ /\ m.mterm = currentTerm[i]
        /\ ostate[i] = Follower
        /\ ~LogOk(i, m)
  /\ msgs' = (msgs \ {m}) \cup
       {AEResp(i, m.msource, currentTerm[i],
               IF m.mterm < currentTerm[i] THEN StaleTerm ELSE EntryMismatch,
               0)}
  /\ UNCHANGED <<currentTerm, ostate, votedFor, log, commitIndex,
                 votesGranted, nextIndex, matchIndex, config,
                 pendingReconfig, electionCtr, restartCtr>>

AcceptAppendEntriesRequest(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = AppendEntriesRequest
  /\ m.mterm = currentTerm[i]
  /\ ostate[i] \in {Follower, Candidate}
  /\ LogOk(i, m)
  /\ Len(log[i]) < MaxLogLen
  /\ log' = [log EXCEPT ![i] =
               IF m.mentries = << >>
                 THEN log[i]
                 ELSE Append(SubSeq(log[i], 1, m.mprevLogIndex),
                             m.mentries[1])]
  /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
  /\ ostate' = [ostate EXCEPT ![i] =
                  IF i \in config[i].members THEN Follower ELSE NotMember]
  /\ msgs' = (msgs \ {m}) \cup
       {AEResp(i, m.msource, currentTerm[i], Ok,
               m.mprevLogIndex + Len(m.mentries))}
  /\ UNCHANGED <<currentTerm, votedFor, votesGranted, nextIndex, matchIndex,
                 config, pendingReconfig, electionCtr, restartCtr>>

HandleAppendEntriesResponse(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = AppendEntriesResponse
  /\ m.mterm = currentTerm[i]
  /\ ostate[i] = Leader
  /\ nextIndex' =
       CASE m.mresult = Ok ->
              [nextIndex EXCEPT ![i][m.msource] = m.mmatchIndex + 1]
         [] m.mresult = EntryMismatch ->
              [nextIndex EXCEPT ![i][m.msource] =
                 IF nextIndex[i][m.msource] > 1
                   THEN nextIndex[i][m.msource] - 1 ELSE 1]
         [] OTHER -> nextIndex
  /\ matchIndex' =
       IF m.mresult = Ok
         THEN [matchIndex EXCEPT ![i][m.msource] = m.mmatchIndex]
         ELSE matchIndex
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<currentTerm, ostate, votedFor, log, commitIndex,
                 votesGranted, config, pendingReconfig, electionCtr,
                 restartCtr>>

(***************************************************************************)
(* The leader advances its commit index once a quorum has matched.         *)
(*                                                                         *)
(* The original scans `{k \in 1..Len(log) : Cardinality({j : matchIndex[j]  *)
(* >= k}) * 2 > ...}`. `matchIndex[i]` is this leader's own table, so the   *)
(* count is over data the node holds -- P4 applies directly.                *)
(***************************************************************************)
AdvanceCommitIndex(i) ==
  /\ ostate[i] = Leader
  /\ \E k \in 1 .. Len(log[i]) :
       /\ k > commitIndex[i]
       /\ IsQuorumOf({j \in Server : matchIndex[i][j] >= k} \cup {i},
                     config[i].members)
       /\ log[i][k].term = currentTerm[i]
       /\ commitIndex' = [commitIndex EXCEPT ![i] = k]
  /\ msgs' = msgs
  /\ UNCHANGED <<currentTerm, ostate, votedFor, log, votesGranted,
                 nextIndex, matchIndex, config, pendingReconfig,
                 electionCtr, restartCtr>>

(***************************************************************************)
(* Reconfiguration. `Server` is a constant and never changes; what changes  *)
(* is each node's own opinion of the membership, which is ordinary per-node *)
(* state. Q2 excludes a varying node set, not this.                         *)
(***************************************************************************)
RequestReconfig(i, op, target) ==
  /\ ostate[i] = Leader
  /\ pendingReconfig[i] = NoReconfig
  /\ config[i].committed
  /\ \/ /\ op = ReconfigAdd
        /\ target \notin config[i].members
     \/ /\ op = ReconfigRemove
        /\ target \in config[i].members
  /\ pendingReconfig' = [pendingReconfig EXCEPT ![i] =
                           [op |-> op, target |-> target]]
  /\ msgs' = msgs
  /\ UNCHANGED <<currentTerm, ostate, votedFor, log, commitIndex,
                 votesGranted, nextIndex, matchIndex, config,
                 electionCtr, restartCtr>>

=============================================================================
