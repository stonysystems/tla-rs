---- MODULE SimpleRaft ----
\* LLM-generated simplified Raft consensus specification.
\* Models leader election and log replication with term-based leadership.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Server, MaxTerm

VARIABLE currentTerm, state, votedFor, log, commitIndex, votesGranted

Follower == "follower"
Candidate == "candidate"
Leader == "leader"

Init ==
    /\ currentTerm = [s \in Server |-> 0]
    /\ state = [s \in Server |-> Follower]
    /\ votedFor = [s \in Server |-> 0]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ votesGranted = [s \in Server |-> {}]

Timeout(s) ==
    /\ state[s] \in {Follower, Candidate}
    /\ currentTerm[s] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ state' = [state EXCEPT ![s] = Candidate]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ UNCHANGED <<log, commitIndex>>

RequestVote(s, t) ==
    /\ state[s] = Candidate
    /\ t # s
    /\ currentTerm[s] > currentTerm[t]
    /\ votedFor[t] = 0
    /\ votedFor' = [votedFor EXCEPT ![t] = s]
    /\ currentTerm' = [currentTerm EXCEPT ![t] = currentTerm[s]]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \cup {t}]
    /\ UNCHANGED <<state, log, commitIndex>>

BecomeLeader(s) ==
    /\ state[s] = Candidate
    /\ Cardinality(votesGranted[s]) * 2 > Cardinality(Server)
    /\ state' = [state EXCEPT ![s] = Leader]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votesGranted>>

ClientRequest(s, v) ==
    /\ state[s] = Leader
    /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], value |-> v])]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, votesGranted>>

AppendEntries(leader, follower) ==
    /\ state[leader] = Leader
    /\ follower # leader
    /\ currentTerm[leader] >= currentTerm[follower]
    /\ currentTerm' = [currentTerm EXCEPT ![follower] = currentTerm[leader]]
    /\ state' = [state EXCEPT ![follower] = Follower]
    /\ log' = [log EXCEPT ![follower] = log[leader]]
    /\ UNCHANGED <<votedFor, commitIndex, votesGranted>>

AdvanceCommitIndex(s) ==
    /\ state[s] = Leader
    /\ Len(log[s]) > commitIndex[s]
    /\ LET newCI == commitIndex[s] + 1
           agreeing == {t \in Server : Len(log[t]) >= newCI}
       IN /\ Cardinality(agreeing) * 2 > Cardinality(Server)
          /\ commitIndex' = [commitIndex EXCEPT ![s] = newCI]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, votesGranted>>

Next ==
    \/ \E s \in Server : Timeout(s)
    \/ \E s, t \in Server : RequestVote(s, t)
    \/ \E s \in Server : BecomeLeader(s)
    \/ \E s \in Server, v \in Nat : ClientRequest(s, v)
    \/ \E s, t \in Server : AppendEntries(s, t)
    \/ \E s \in Server : AdvanceCommitIndex(s)

Spec == Init /\ [][Next]_<<currentTerm, state, votedFor, log, commitIndex, votesGranted>>

ElectionSafety ==
    \A s1, s2 \in Server :
        (state[s1] = Leader /\ state[s2] = Leader /\ currentTerm[s1] = currentTerm[s2])
        => s1 = s2

====
