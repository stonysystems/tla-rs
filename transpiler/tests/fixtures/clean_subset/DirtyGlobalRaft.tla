-------------------------- MODULE DirtyGlobalRaft ----------------------------
(* A deliberately dirty spec (Phase 52.M0 negative fixture).

   It reproduces, in miniature, the four things real global multi-server specs
   (Raft, EPaxos, Jetpack) do that block mechanical projection:

     * instantaneous cross-node reads          -> CS003
     * history/ghost variables                 -> CS005
     * aggregation over the whole node set     -> CS006
     * a global scalar variable                -> CS001
     * messages without src/dst                -> CS010
     * a non-send/discard network update       -> CS009
     * a Next disjunct with no node parameter  -> CS012
     * a whole-array write inside an action    -> CS016 *)

EXTENDS Naturals, FiniteSets

CONSTANT Server

VARIABLE log, currentTerm, elections, leaderCount, messages

AllLogs == { log[i] : i \in Server }

AppendEntries(i, j) ==
    currentTerm[i] = currentTerm[j]
    /\ log' = [log EXCEPT ![i] = log[i] \cup {currentTerm[j]}]
    /\ messages' = messages \cup {[type |-> "ae", term |-> currentTerm[i]]}
    /\ currentTerm' = currentTerm
    /\ elections' = elections \cup {[eterm |-> currentTerm[i]]}
    /\ leaderCount' = leaderCount

Timeout(i) ==
    currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ messages' = messages \cup {[type |-> "rv", src |-> i, dst |-> i]}
    /\ log' = log
    /\ elections' = elections
    /\ leaderCount' = leaderCount + 1

GlobalCommit ==
    log' = [i \in Server |-> log[i] \cup {0}]
    /\ currentTerm' = currentTerm
    /\ messages' = messages
    /\ elections' = elections
    /\ leaderCount' = leaderCount

Restart ==
    messages' = {}
    /\ log' = log
    /\ currentTerm' = currentTerm
    /\ elections' = elections
    /\ leaderCount' = leaderCount

Init ==
    log = [i \in Server |-> {}]
    /\ currentTerm = [i \in Server |-> 0]
    /\ elections = {}
    /\ leaderCount = 0
    /\ messages = {}

Next ==
    (\E i \in Server : \E j \in Server : AppendEntries(i, j))
    \/ (\E i \in Server : Timeout(i))
    \/ GlobalCommit
    \/ Restart

==============================================================================
