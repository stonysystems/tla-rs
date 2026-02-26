---- MODULE Raft ----
\* LLM-generated Raft consensus specification.
\* Models leader election and log replication with per-node state.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Server, MaxTerm, MaxLogLen, Value

VARIABLE currentTerm, role, votedFor, log, commitIndex,
         votesGranted, matchIndex, nextIndex

Follower  == "follower"
Candidate == "candidate"
Leader    == "leader"

\* Quorum: strict majority
Quorum == {Q \in SUBSET Server : Cardinality(Q) * 2 > Cardinality(Server)}

Init ==
    /\ currentTerm  = [s \in Server |-> 0]
    /\ role         = [s \in Server |-> Follower]
    /\ votedFor     = [s \in Server |-> 0]
    /\ log          = [s \in Server |-> <<>>]
    /\ commitIndex  = [s \in Server |-> 0]
    /\ votesGranted = [s \in Server |-> {}]
    /\ matchIndex   = [s \in Server |-> [t \in Server |-> 0]]
    /\ nextIndex    = [s \in Server |-> [t \in Server |-> 1]]

\* --- Leader Election ---

Timeout(s) ==
    /\ role[s] \in {Follower, Candidate}
    /\ currentTerm[s] < MaxTerm
    /\ currentTerm'  = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ role'         = [role EXCEPT ![s] = Candidate]
    /\ votedFor'     = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex>>

\* Log comparison for voting: candidate's log must be at least as up-to-date
LastLogTerm(s) == IF Len(log[s]) > 0 THEN log[s][Len(log[s])].term ELSE 0

LogUpToDate(candidateLastTerm, candidateLogLen, voterLastTerm, voterLogLen) ==
    \/ candidateLastTerm > voterLastTerm
    \/ (candidateLastTerm = voterLastTerm /\ candidateLogLen >= voterLogLen)

GrantVote(voter, candidate) ==
    /\ voter # candidate
    /\ currentTerm[candidate] >= currentTerm[voter]
    /\ votedFor[voter] \in {0, candidate}
    /\ LogUpToDate(LastLogTerm(candidate), Len(log[candidate]),
                   LastLogTerm(voter), Len(log[voter]))
    /\ votedFor'     = [votedFor EXCEPT ![voter] = candidate]
    /\ currentTerm'  = [currentTerm EXCEPT ![voter] = currentTerm[candidate]]
    /\ role'         = [role EXCEPT ![voter] = Follower]
    /\ votesGranted' = [votesGranted EXCEPT ![candidate] = votesGranted[candidate] \cup {voter}]
    /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex>>

BecomeLeader(s) ==
    /\ role[s] = Candidate
    /\ votesGranted[s] \in Quorum
    /\ role'       = [role EXCEPT ![s] = Leader]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in Server |-> 0]]
    /\ nextIndex'  = [nextIndex EXCEPT ![s] = [t \in Server |-> Len(log[s]) + 1]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votesGranted>>

\* --- Log Replication ---

ClientRequest(leader, val) ==
    /\ role[leader] = Leader
    /\ Len(log[leader]) < MaxLogLen
    /\ val \in Value
    /\ log' = [log EXCEPT ![leader] = Append(log[leader],
                  [term |-> currentTerm[leader], value |-> val])]
    /\ UNCHANGED <<currentTerm, role, votedFor, commitIndex, votesGranted, matchIndex, nextIndex>>

AppendEntries(leader, follower) ==
    /\ role[leader] = Leader
    /\ follower # leader
    /\ currentTerm[leader] >= currentTerm[follower]
    /\ LET ni == nextIndex[leader][follower]
           prevLogTerm == IF ni > 1 /\ ni - 1 <= Len(log[leader])
                          THEN log[leader][ni - 1].term ELSE 0
           \* Check follower's log matches at prevLogIndex
           followerMatch == IF ni = 1 THEN TRUE
                            ELSE IF ni - 1 <= Len(log[follower])
                                 THEN log[follower][ni - 1].term = prevLogTerm
                                 ELSE FALSE
       IN IF followerMatch
          THEN \* Append entries from nextIndex onward
               /\ log' = [log EXCEPT ![follower] =
                    SubSeq(log[follower], 1, ni - 1) \o
                    SubSeq(log[leader], ni, Len(log[leader]))]
               /\ matchIndex' = [matchIndex EXCEPT ![leader][follower] = Len(log[leader])]
               /\ nextIndex'  = [nextIndex EXCEPT ![leader][follower] = Len(log[leader]) + 1]
               /\ currentTerm' = [currentTerm EXCEPT ![follower] = currentTerm[leader]]
               /\ role' = [role EXCEPT ![follower] = Follower]
               /\ UNCHANGED <<votedFor, commitIndex, votesGranted>>
          ELSE \* Decrement nextIndex on mismatch
               /\ nextIndex' = [nextIndex EXCEPT ![leader][follower] =
                    IF ni > 1 THEN ni - 1 ELSE 1]
               /\ UNCHANGED <<currentTerm, role, votedFor, log, commitIndex,
                              votesGranted, matchIndex>>

AdvanceCommitIndex(leader) ==
    /\ role[leader] = Leader
    /\ \E newCI \in (commitIndex[leader] + 1)..Len(log[leader]) :
        /\ log[leader][newCI].term = currentTerm[leader]
        /\ {s \in Server : matchIndex[leader][s] >= newCI \/ s = leader} \in Quorum
        /\ commitIndex' = [commitIndex EXCEPT ![leader] = newCI]
    /\ UNCHANGED <<currentTerm, role, votedFor, log, votesGranted, matchIndex, nextIndex>>

StepDown(s) ==
    /\ role[s] \in {Leader, Candidate}
    /\ \E t \in Server : currentTerm[t] > currentTerm[s]
    /\ currentTerm' = [currentTerm EXCEPT ![s] =
          CHOOSE term \in Nat : \E t \in Server : term = currentTerm[t] /\ term > currentTerm[s]]
    /\ role'     = [role EXCEPT ![s] = Follower]
    /\ votedFor' = [votedFor EXCEPT ![s] = 0]
    /\ UNCHANGED <<log, commitIndex, votesGranted, matchIndex, nextIndex>>

Next ==
    \/ \E s \in Server : Timeout(s)
    \/ \E v, c \in Server : GrantVote(v, c)
    \/ \E s \in Server : BecomeLeader(s)
    \/ \E s \in Server, v \in Value : ClientRequest(s, v)
    \/ \E l, f \in Server : AppendEntries(l, f)
    \/ \E s \in Server : AdvanceCommitIndex(s)
    \/ \E s \in Server : StepDown(s)

vars == <<currentTerm, role, votedFor, log, commitIndex,
          votesGranted, matchIndex, nextIndex>>
Spec == Init /\ [][Next]_vars

\* --- Safety Invariants ---

\* At most one leader per term
ElectionSafety ==
    \A s1, s2 \in Server :
        (role[s1] = Leader /\ role[s2] = Leader /\ currentTerm[s1] = currentTerm[s2])
        => s1 = s2

\* A leader's log contains all committed entries
LeaderCompleteness ==
    \A s \in Server :
        role[s] = Leader =>
            \A t \in Server :
                \A i \in 1..commitIndex[t] :
                    i <= Len(log[s])

\* Terms are bounded
TermBounded ==
    \A s \in Server : currentTerm[s] <= MaxTerm

====
