---- MODULE Chain ----
\* Hand-written single-node Chain Replication spec for DPOR case 15.
\* Replaces the prior verus2tla-emitted parameterized Init/Next that TLC
\* could not enumerate (untyped record-tag access on s.role.tag).
\*
\* Models one node's local view in a chain of length ChainLen. The role
\* (RoleHead / RoleMiddle / RoleTail) is fixed at Init based on NodeId
\* — no role changes after initialization.
\*
\* `history` is modeled as a Set instead of a Seq so the translator can
\* infer the field type (Seq inference from `<<>>`-style empties is not
\* yet supported); Append/Len semantics aren't needed since the only
\* uses are membership checks and a bounded-growth guard.

EXTENDS Naturals, FiniteSets

VARIABLE role, history, pending_sent, committed_count, obj_value,
         has_predecessor, predecessor, has_successor, successor, alive

\* Role encoded as a small integer to avoid TLC model-value pitfalls and
\* to dodge the Sequences module's Head/Tail name collisions.
RoleHead   == 1
RoleMiddle == 2
RoleTail   == 3
Roles      == {RoleHead, RoleMiddle, RoleTail}

\* Bounded universe of values that can appear in the log.
Values == {1}

ChainLen == 2
NodeId   == 0   \* this spec instance models the Head node; Middle and
                \* Tail variants would set NodeId to 1.

InitialRole ==
    IF NodeId = 0 THEN RoleHead
    ELSE IF NodeId = ChainLen - 1 THEN RoleTail
    ELSE RoleMiddle

Init ==
    /\ role = InitialRole
    /\ history = {}
    /\ pending_sent = {}
    /\ committed_count = 0
    /\ obj_value = 0
    /\ has_predecessor = (NodeId > 0)
    /\ predecessor     = IF NodeId > 0 THEN NodeId - 1 ELSE 0
    /\ has_successor   = (NodeId < ChainLen - 1)
    /\ successor       = IF NodeId < ChainLen - 1 THEN NodeId + 1 ELSE 0
    /\ alive = TRUE

HeadReceiveWrite(value) ==
    /\ role = RoleHead
    /\ alive = TRUE
    /\ value \notin pending_sent
    /\ Cardinality(history) < 2
    /\ role' = role
    /\ history' = history \cup {value}
    /\ pending_sent' = pending_sent \cup {value}
    /\ committed_count' = committed_count
    /\ obj_value' = obj_value
    /\ has_predecessor' = has_predecessor
    /\ predecessor' = predecessor
    /\ has_successor' = has_successor
    /\ successor' = successor
    /\ alive' = alive

ForwardToSuccessor(value) ==
    /\ (role = RoleHead \/ role = RoleMiddle)
    /\ alive = TRUE
    /\ value \in pending_sent
    /\ has_successor = TRUE
    /\ UNCHANGED <<role, history, pending_sent, committed_count, obj_value,
                   has_predecessor, predecessor, has_successor, successor, alive>>

ReceiveUpdate(value) ==
    /\ (role = RoleMiddle \/ role = RoleTail)
    /\ alive = TRUE
    /\ value \notin history
    /\ Cardinality(history) < 2
    /\ role' = role
    /\ history' = history \cup {value}
    /\ pending_sent' = IF role = RoleMiddle THEN pending_sent \cup {value}
                       ELSE pending_sent
    /\ committed_count' = committed_count
    /\ obj_value' = obj_value
    /\ has_predecessor' = has_predecessor
    /\ predecessor' = predecessor
    /\ has_successor' = has_successor
    /\ successor' = successor
    /\ alive' = alive

TailCommit(value) ==
    /\ role = RoleTail
    /\ alive = TRUE
    /\ value \in history
    /\ role' = role
    /\ history' = history
    /\ pending_sent' = pending_sent
    /\ committed_count' = committed_count + 1
    /\ obj_value' = value
    /\ has_predecessor' = has_predecessor
    /\ predecessor' = predecessor
    /\ has_successor' = has_successor
    /\ successor' = successor
    /\ alive' = alive

ReceiveAck(value) ==
    /\ (role = RoleHead \/ role = RoleMiddle)
    /\ alive = TRUE
    /\ value \in pending_sent
    /\ role' = role
    /\ history' = history
    /\ pending_sent' = pending_sent \ {value}
    /\ committed_count' = committed_count
    /\ obj_value' = obj_value
    /\ has_predecessor' = has_predecessor
    /\ predecessor' = predecessor
    /\ has_successor' = has_successor
    /\ successor' = successor
    /\ alive' = alive

NodeFail ==
    /\ alive = TRUE
    /\ alive' = FALSE
    /\ UNCHANGED <<role, history, pending_sent, committed_count, obj_value,
                   has_predecessor, predecessor, has_successor, successor>>

Reconfigure(new_has_pred, new_pred, new_has_succ, new_succ) ==
    /\ alive = TRUE
    /\ has_predecessor' = new_has_pred
    /\ predecessor'     = new_pred
    /\ has_successor'   = new_has_succ
    /\ successor'       = new_succ
    /\ UNCHANGED <<role, history, pending_sent, committed_count, obj_value, alive>>

Next ==
    \/ \E v \in Values : HeadReceiveWrite(v)
    \/ \E v \in Values : ForwardToSuccessor(v)
    \/ \E v \in Values : ReceiveUpdate(v)
    \/ \E v \in Values : TailCommit(v)
    \/ \E v \in Values : ReceiveAck(v)
    \/ NodeFail
    \/ \E hp \in BOOLEAN, pre \in 0..(ChainLen-1),
         hs \in BOOLEAN, suc \in 0..(ChainLen-1) :
            Reconfigure(hp, pre, hs, suc)

TypeOK ==
    /\ role \in Roles
    /\ history \subseteq Values
    /\ pending_sent \subseteq Values
    /\ committed_count \in Nat
    /\ obj_value \in (Values \cup {0})
    /\ has_predecessor \in BOOLEAN
    /\ predecessor \in 0..(ChainLen-1)
    /\ has_successor \in BOOLEAN
    /\ successor \in 0..(ChainLen-1)
    /\ alive \in BOOLEAN

================================================================================
