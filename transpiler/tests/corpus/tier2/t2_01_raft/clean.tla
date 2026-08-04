------------------------------- MODULE RaftClean -------------------------------
(***************************************************************************)
(* Raft (ongardie/raft.tla), rewritten into the clean subset (C1-C5) of    *)
(* docs/clean_tla_subset.md. See rewrite.md; in outline:                   *)
(*                                                                        *)
(*   - the three history variables are gone: `allLogs`, `elections` and    *)
(*     `voterLog` exist for the proof, not for the protocol, and `mlog`    *)
(*     is dropped from messages for the same reason (the original says so  *)
(*     itself: "would not exist in a real implementation").                *)
(*   - `messages` was a bag; it is a set here. That removes                *)
(*     `DuplicateMessage`, which a set cannot express. Receipt still      *)
(*     consumes, as the original's `Discard`/`Reply` do -- unlike Paxos,  *)
(*     whose spec says messages are never removed.                        *)
(*   - `Quorum` was the set of all majority subsets; a node counts its own *)
(*     votes instead (P4).                                                *)
(*   - a `TypeOK` is added. The original has none, and the subset states   *)
(*     per-node-ness in terms of declarations.                             *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Server, Value, MaxTerm, MaxLogLen

ASSUME ServerAssumption == IsFiniteSet(Server) /\ Server # {}

Nil == 0

Follower == "follower"
Candidate == "candidate"
Leader == "leader"

RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "aeq"
AppendEntriesResponse == "aep"

Term == 1 .. MaxTerm

(* `nextIndex` reaches `Len(log) + 1`, one past the end of a full log, so the
   index range is one wider than the log length. *)
Index == 0 .. (MaxLogLen + 1)

VARIABLES
  currentTerm,     \* this server's term
  state,           \* follower / candidate / leader
  votedFor,        \* who this server voted for this term, Nil if nobody
  log,             \* this server's log
  commitIndex,     \* highest index known committed
  votesResponded,  \* servers that answered this candidate's vote request
  votesGranted,    \* servers that granted it
  nextIndex,       \* per peer: next index to send
  matchIndex,      \* per peer: highest index known replicated
  msgs             \* messages sent

LogEntry == [term: Term, value: Value]

Message ==
       [mtype: {RequestVoteRequest}, mterm: Term, mlastLogTerm: Term \cup {0},
        mlastLogIndex: Index, mvoteGranted: BOOLEAN, msuccess: BOOLEAN,
        mmatchIndex: Index, mprevLogIndex: Index, mprevLogTerm: Term \cup {0},
        mentries: Seq(LogEntry), mcommitIndex: Index,
        msource: Server, mdest: Server]
  \cup [mtype: {RequestVoteResponse}, mterm: Term, mlastLogTerm: Term \cup {0},
        mlastLogIndex: Index, mvoteGranted: BOOLEAN, msuccess: BOOLEAN,
        mmatchIndex: Index, mprevLogIndex: Index, mprevLogTerm: Term \cup {0},
        mentries: Seq(LogEntry), mcommitIndex: Index,
        msource: Server, mdest: Server]
  \cup [mtype: {AppendEntriesRequest}, mterm: Term, mlastLogTerm: Term \cup {0},
        mlastLogIndex: Index, mvoteGranted: BOOLEAN, msuccess: BOOLEAN,
        mmatchIndex: Index, mprevLogIndex: Index, mprevLogTerm: Term \cup {0},
        mentries: Seq(LogEntry), mcommitIndex: Index,
        msource: Server, mdest: Server]
  \cup [mtype: {AppendEntriesResponse}, mterm: Term, mlastLogTerm: Term \cup {0},
        mlastLogIndex: Index, mvoteGranted: BOOLEAN, msuccess: BOOLEAN,
        mmatchIndex: Index, mprevLogIndex: Index, mprevLogTerm: Term \cup {0},
        mentries: Seq(LogEntry), mcommitIndex: Index,
        msource: Server, mdest: Server]

TypeOK ==
  /\ currentTerm \in [Server -> Term]
  /\ state \in [Server -> {Follower, Candidate, Leader}]
  /\ votedFor \in [Server -> Server \cup {Nil}]
  /\ log \in [Server -> Seq(LogEntry)]
  /\ commitIndex \in [Server -> Index]
  /\ votesResponded \in [Server -> SUBSET Server]
  /\ votesGranted \in [Server -> SUBSET Server]
  /\ nextIndex \in [Server -> [Server -> Index]]
  /\ matchIndex \in [Server -> [Server -> Index]]
  /\ msgs \subseteq Message

Init ==
  /\ currentTerm = [i \in Server |-> 1]
  /\ state = [i \in Server |-> Follower]
  /\ votedFor = [i \in Server |-> Nil]
  /\ log = [i \in Server |-> << >>]
  /\ commitIndex = [i \in Server |-> 0]
  /\ votesResponded = [i \in Server |-> {}]
  /\ votesGranted = [i \in Server |-> {}]
  /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
  /\ msgs = {}

(***************************************************************************)
(* Helpers. `IsMajority` replaces the original's `Quorum`, the set of all  *)
(* majority subsets: a node counting its own votes needs a concrete test.  *)
(***************************************************************************)
IsMajority(s) == Cardinality(s) * 2 > Cardinality(Server)

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

Msg(t, i, j) ==
  [mtype |-> t, mterm |-> 1, mlastLogTerm |-> 0, mlastLogIndex |-> 0,
   mvoteGranted |-> FALSE, msuccess |-> FALSE, mmatchIndex |-> 0,
   mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> << >>,
   mcommitIndex |-> 0, msource |-> i, mdest |-> j]

(***************************************************************************)
(* Server i restarts, losing everything but currentTerm, votedFor and log. *)
(***************************************************************************)
Restart(i) ==
  /\ state' = [state EXCEPT ![i] = Follower]
  /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
  /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
  /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
  /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
  /\ commitIndex' = [commitIndex EXCEPT ![i] = 0]
  /\ msgs' = msgs
  /\ UNCHANGED <<currentTerm, votedFor, log>>

(***************************************************************************)
(* Server i times out and starts an election.                              *)
(***************************************************************************)
Timeout(i) ==
  /\ state[i] \in {Follower, Candidate}
  /\ currentTerm[i] < MaxTerm
  /\ state' = [state EXCEPT ![i] = Candidate]
  /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
  /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
  /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
  /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
  /\ msgs' = msgs
  /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

(***************************************************************************)
(* Candidate i asks j for a vote. `j` is a destination, not a second actor. *)
(***************************************************************************)
RequestVote(i, j) ==
  /\ state[i] = Candidate
  /\ j \notin votesResponded[i]
  /\ msgs' = msgs \cup
       {[Msg(RequestVoteRequest, i, j) EXCEPT
           !.mterm = currentTerm[i],
           !.mlastLogTerm = LastTerm(log[i]),
           !.mlastLogIndex = Len(log[i])]}
  /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex,
                 votesResponded, votesGranted, nextIndex, matchIndex>>

(***************************************************************************)
(* Candidate i becomes leader, having counted a majority of votes.         *)
(***************************************************************************)
BecomeLeader(i) ==
  /\ state[i] = Candidate
  /\ IsMajority(votesGranted[i])
  /\ state' = [state EXCEPT ![i] = Leader]
  /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> Len(log[i]) + 1]]
  /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
  /\ msgs' = msgs
  /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votesResponded,
                 votesGranted>>

(***************************************************************************)
(* Leader i appends a client value to its log.                             *)
(***************************************************************************)
ClientRequest(i, v) ==
  /\ state[i] = Leader
  /\ Len(log[i]) < MaxLogLen
  /\ log' = [log EXCEPT ![i] = Append(log[i], [term |-> currentTerm[i],
                                               value |-> v])]
  /\ msgs' = msgs
  /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, votesResponded,
                 votesGranted, nextIndex, matchIndex>>

(***************************************************************************)
(* Leader i sends j an AppendEntries carrying at most one entry.           *)
(***************************************************************************)
AppendEntries(i, j) ==
  /\ i /= j
  /\ state[i] = Leader
  /\ msgs' = msgs \cup
       {[Msg(AppendEntriesRequest, i, j) EXCEPT
           !.mterm = currentTerm[i],
           !.mprevLogIndex = nextIndex[i][j] - 1,
           !.mprevLogTerm = IF nextIndex[i][j] - 1 > 0
                              THEN log[i][nextIndex[i][j] - 1].term
                              ELSE 0,
           !.mentries = SubSeq(log[i], nextIndex[i][j],
                               IF Len(log[i]) < nextIndex[i][j]
                                 THEN Len(log[i]) ELSE nextIndex[i][j]),
           !.mcommitIndex = IF commitIndex[i] < nextIndex[i][j]
                              THEN commitIndex[i] ELSE nextIndex[i][j]]}
  /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex,
                 votesResponded, votesGranted, nextIndex, matchIndex>>

(***************************************************************************)
(* Server i grants or refuses a vote.                                      *)
(***************************************************************************)
HandleRequestVoteRequest(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = RequestVoteRequest
  /\ m.mterm <= currentTerm[i]
  /\ IF /\ m.mterm = currentTerm[i]
        /\ \/ m.mlastLogTerm > LastTerm(log[i])
           \/ /\ m.mlastLogTerm = LastTerm(log[i])
              /\ m.mlastLogIndex >= Len(log[i])
        /\ votedFor[i] \in {Nil, m.msource}
       THEN /\ votedFor' = [votedFor EXCEPT ![i] = m.msource]
            /\ msgs' = (msgs \ {m}) \cup
                 {[Msg(RequestVoteResponse, i, m.msource) EXCEPT
                     !.mterm = currentTerm[i], !.mvoteGranted = TRUE]}
       ELSE /\ votedFor' = votedFor
            /\ msgs' = (msgs \ {m}) \cup
                 {[Msg(RequestVoteResponse, i, m.msource) EXCEPT
                     !.mterm = currentTerm[i], !.mvoteGranted = FALSE]}
  /\ UNCHANGED <<currentTerm, state, log, commitIndex, votesResponded,
                 votesGranted, nextIndex, matchIndex>>

(***************************************************************************)
(* Candidate i tallies a vote response.                                    *)
(***************************************************************************)
HandleRequestVoteResponse(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = RequestVoteResponse
  /\ m.mterm = currentTerm[i]
  /\ votesResponded' = [votesResponded EXCEPT ![i] =
                          votesResponded[i] \cup {m.msource}]
  /\ IF m.mvoteGranted
       THEN votesGranted' = [votesGranted EXCEPT ![i] =
                               votesGranted[i] \cup {m.msource}]
       ELSE votesGranted' = votesGranted
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex,
                 nextIndex, matchIndex>>

(***************************************************************************)
(* Follower i accepts or rejects an AppendEntries. This slice keeps the    *)
(* accept and reject paths and drops the log-conflict truncation, which    *)
(* the rewrite notes record as out of scope.                               *)
(***************************************************************************)
HandleAppendEntriesRequest(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = AppendEntriesRequest
  /\ m.mterm <= currentTerm[i]
  /\ IF /\ m.mterm = currentTerm[i]
        /\ state[i] = Follower
        /\ \/ m.mprevLogIndex = 0
           \/ /\ m.mprevLogIndex > 0
              /\ m.mprevLogIndex <= Len(log[i])
       THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
            /\ log' = IF m.mentries = << >>
                        THEN log
                        ELSE [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
            /\ msgs' = (msgs \ {m}) \cup
                 {[Msg(AppendEntriesResponse, i, m.msource) EXCEPT
                     !.mterm = currentTerm[i], !.msuccess = TRUE,
                     !.mmatchIndex = m.mprevLogIndex + Len(m.mentries)]}
       ELSE /\ commitIndex' = commitIndex
            /\ log' = log
            /\ msgs' = (msgs \ {m}) \cup
                 {[Msg(AppendEntriesResponse, i, m.msource) EXCEPT
                     !.mterm = currentTerm[i], !.msuccess = FALSE,
                     !.mmatchIndex = 0]}
  /\ UNCHANGED <<currentTerm, state, votedFor, votesResponded, votesGranted,
                 nextIndex, matchIndex>>

(***************************************************************************)
(* Leader i records the follower's answer.                                 *)
(***************************************************************************)
HandleAppendEntriesResponse(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = AppendEntriesResponse
  /\ m.mterm = currentTerm[i]
  /\ IF m.msuccess
       THEN /\ nextIndex' = [nextIndex EXCEPT ![i][m.msource] =
                               m.mmatchIndex + 1]
            /\ matchIndex' = [matchIndex EXCEPT ![i][m.msource] =
                                m.mmatchIndex]
       ELSE /\ nextIndex' = [nextIndex EXCEPT ![i][m.msource] =
                               IF nextIndex[i][m.msource] > 1
                                 THEN nextIndex[i][m.msource] - 1 ELSE 1]
            /\ matchIndex' = matchIndex
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex,
                 votesResponded, votesGranted>>

Next ==
  \E i \in Server :
      \/ Restart(i)
      \/ Timeout(i)
      \/ BecomeLeader(i)
      \/ \E v \in Value : ClientRequest(i, v)
      \/ \E j \in Server : RequestVote(i, j)
      \/ \E j \in Server : AppendEntries(i, j)
      \/ \E m \in msgs :
            \/ HandleRequestVoteRequest(i, m)
            \/ HandleRequestVoteResponse(i, m)
            \/ HandleAppendEntriesRequest(i, m)
            \/ HandleAppendEntriesResponse(i, m)

vars == <<currentTerm, state, votedFor, log, commitIndex, votesResponded,
          votesGranted, nextIndex, matchIndex, msgs>>

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety: at most one leader per term.                                    *)
(***************************************************************************)
OneLeaderPerTerm ==
  \A i, j \in Server :
      (state[i] = Leader /\ state[j] = Leader /\ currentTerm[i] = currentTerm[j])
        => i = j

==============================================================================
