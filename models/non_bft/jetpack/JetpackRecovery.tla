------------------------ MODULE JetpackRecovery ------------------------
EXTENDS Integers, FiniteSets, TLC
\* One last-normal-view recovery instance, matching recovery.rs.
\* Acknowledgment and vote histories model persistent protocol evidence.
CONSTANTS Nodes, Commands, Conflict, F, Ballots
VARIABLES logs, frozen, promise, last, value, replies, proposals, votes
vars == <<logs, frozen, promise, last, value, replies, proposals, votes>>
AllDistinct == {p \in Commands \X Commands : p[1] # p[2]}
Threshold == ((F + 1) \div 2) + 1
FastSize == F + Threshold
Quorums == {q \in SUBSET Nodes : Cardinality(q) = F + 1}
Support(ls, q, x) == {a \in q : x \in ls[a]}
Selected(ls, q) == {x \in Commands : Cardinality(Support(ls, q, x)) >= Threshold}
FastCommitted == {x \in Commands : Cardinality(Support(logs, Nodes, x)) >= FastSize}
Reply(a, b) == CHOOSE r \in replies : r.node = a /\ r.ballot = b
HasReply(a, b) == \E r \in replies : r.node = a /\ r.ballot = b
ReplyLogs(q, b) == [a \in q |-> Reply(a, b).log]
Chosen(b) == b \in DOMAIN proposals /\
    \E q \in Quorums : \A a \in q : <<a, b, proposals[b]>> \in votes

Init ==
    /\ logs = [a \in Nodes |-> {}]
    /\ frozen = {}
    /\ promise = [a \in Nodes |-> -1]
    /\ last = [a \in Nodes |-> -1]
    /\ value = [a \in Nodes |-> {}]
    /\ replies = {}
    /\ proposals = [b \in {} |-> {}]
    /\ votes = {}

Acknowledge(a, x) ==
    /\ a \notin frozen
    /\ \A y \in logs[a] : <<x, y>> \notin Conflict
    /\ logs' = [logs EXCEPT ![a] = @ \cup {x}]
    /\ UNCHANGED <<frozen, promise, last, value, replies, proposals, votes>>
Freeze(a) ==
    /\ frozen' = frozen \cup {a}
    /\ UNCHANGED <<logs, promise, last, value, replies, proposals, votes>>
Prepare(a, b) ==
    /\ a \in frozen
    /\ b > promise[a]
    /\ replies' = replies \cup {[node |-> a, ballot |-> b, prior |-> last[a],
                                 val |-> value[a], log |-> logs[a]]}
    /\ promise' = [promise EXCEPT ![a] = b]
    /\ UNCHANGED <<logs, frozen, last, value, proposals, votes>>
Propose(b, q) ==
    /\ b \notin DOMAIN proposals
    /\ \A a \in q : HasReply(a, b)
    /\ LET maximum == CHOOSE m \in {-1} \cup Ballots :
                   (\E a \in q : Reply(a, b).prior = m) /\
                   (\A a \in q : Reply(a, b).prior <= m)
           proposed == IF maximum = -1 THEN Selected(ReplyLogs(q, b), q)
                       ELSE Reply(CHOOSE a \in q : Reply(a, b).prior = maximum, b).val
       IN proposals' = [k \in DOMAIN proposals \cup {b} |->
                             IF k = b THEN proposed ELSE proposals[k]]
    /\ UNCHANGED <<logs, frozen, promise, last, value, replies, votes>>
Accept(a, b) ==
    /\ b \in DOMAIN proposals
    /\ b >= promise[a]
    /\ promise' = [promise EXCEPT ![a] = b]
    /\ last' = [last EXCEPT ![a] = b]
    /\ value' = [value EXCEPT ![a] = proposals[b]]
    /\ votes' = votes \cup {<<a, b, proposals[b]>>}
    /\ UNCHANGED <<logs, frozen, replies, proposals>>
Next ==
    \/ \E a \in Nodes, x \in Commands : Acknowledge(a, x)
    \/ \E a \in Nodes : Freeze(a)
    \/ \E a \in Nodes, b \in Ballots : Prepare(a, b)
    \/ \E b \in Ballots, q \in Quorums : Propose(b, q)
    \/ \E a \in Nodes, b \in Ballots : Accept(a, b)
    \/ UNCHANGED vars

TypeOK ==
    /\ Cardinality(Nodes) = 2 * F + 1
    /\ logs \in [Nodes -> SUBSET Commands]
    /\ frozen \subseteq Nodes
    /\ promise \in [Nodes -> {-1} \cup Ballots]
    /\ last \in [Nodes -> {-1} \cup Ballots]
    /\ value \in [Nodes -> SUBSET Commands]
    /\ replies \subseteq [node: Nodes, ballot: Ballots, prior: {-1} \cup Ballots,
                          val: SUBSET Commands, log: SUBSET Commands]
    /\ DOMAIN proposals \subseteq Ballots
    /\ \A b \in DOMAIN proposals : proposals[b] \subseteq Commands
    /\ votes \subseteq Nodes \X Ballots \X (SUBSET Commands)
ReplyAccuracy == \A r \in replies :
    /\ r.node \in frozen
    /\ r.log = logs[r.node]
    /\ r.ballot <= promise[r.node]
    /\ r.prior < r.ballot
    /\ r.prior >= 0 => <<r.node, r.prior, r.val>> \in votes
    /\ \A b \in Ballots, v \in SUBSET Commands :
           r.prior < b /\ b < r.ballot => <<r.node, b, v>> \notin votes
RecoveryComplete == \A b \in DOMAIN proposals : FastCommitted \subseteq proposals[b]
RecoveryConflictFree == \A b \in DOMAIN proposals : \A x \in FastCommitted, y \in proposals[b] :
                           <<x, y>> \notin Conflict
Agreement == \A b, k \in DOMAIN proposals :
                  Chosen(b) /\ Chosen(k) => proposals[b] = proposals[k]
\* Deliberately false invariants used only by witness checks.
NoFastRecovery == ~ (\E b \in DOMAIN proposals : Chosen(b) /\ FastCommitted # {})
NoEmptyRecovery == ~ (\E b \in DOMAIN proposals : Chosen(b) /\ proposals[b] = {})
NoRetry == ~ (\E b, k \in DOMAIN proposals : b < k /\ Chosen(b) /\ Chosen(k))
=============================================================================
