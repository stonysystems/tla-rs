------------------------------- MODULE MakoOCC -------------------------------
EXTENDS Integers, Sequences, FiniteSets
\* One-epoch Section 4.2 OCC companion. Verus proves occ.rs; this file has only
\* SANY validation. No TLAPS proof or checked translation is claimed.
\* serialCounter is ghost state, never used by a protocol guard.
CONSTANTS Shards, Keys, TxIds, ShardOf, Base
ASSUME Shards # {} /\ ShardOf \in [Keys -> Shards] /\ Base \in [Keys -> Int]
VARIABLES tx, data, locks, clocks, installed, serialCounter
vars == <<tx, data, locks, clocks, installed, serialCounter>>
Empty == [x \in {} |-> 0]
Put(m, k, v) == [x \in DOMAIN m \cup {k} |-> IF x = k THEN v ELSE m[x]]
Without(m, ks) == [k \in DOMAIN m \ ks |-> m[k]]
Zero == [sh \in Shards |-> 0]
Max(a, b) == IF a >= b THEN a ELSE b
RECURSIVE ReadMax(_, _, _)
ReadMax(rs, sh, n) == IF n = 0 THEN 0 ELSE Max(ReadMax(rs, sh, n-1), rs[n].version.vc[sh])
Vector(t) == [sh \in Shards |-> Max(IF sh \in DOMAIN t.tickets THEN t.tickets[sh] ELSE 0,
                                  ReadMax(t.reads, sh, Len(t.reads)))]
BaseVersion(k) == [writer |-> [present |-> FALSE, id |-> 0], value |-> Base[k],
                   serial |-> 0, ticket |-> 0, vc |-> Zero]
NewTx == [phase |-> "Running", writes |-> Empty, reads |-> <<>>, checked |-> {},
          tickets |-> Empty, vc |-> Empty, serial |-> 0]
Owns(id, k) == k \in DOMAIN locks /\ locks[k] = id
AllLocked(id) == \A k \in DOMAIN tx[id].writes : Owns(id, k)
AllChecked(id) == 1..Len(tx[id].reads) \subseteq tx[id].checked
CanValidate(id, j) ==
    /\ id \in DOMAIN tx /\ tx[id].phase = "Checking"
    /\ j \in 1..Len(tx[id].reads)
    /\ LET r == tx[id].reads[j] IN
        /\ data[r.key].vc = r.version.vc
        /\ r.key \notin DOMAIN locks \/ locks[r.key] = id
Init ==
    /\ tx = Empty /\ locks = Empty /\ clocks = Zero
    /\ data = [k \in Keys |-> BaseVersion(k)] /\ installed = {} /\ serialCounter = 0
TxUpdate(id, t) ==
    /\ tx' = Put(tx, id, t)
    /\ UNCHANGED <<data, locks, clocks, installed, serialCounter>>
Open(id) == id \notin DOMAIN tx /\ TxUpdate(id, NewTx)
Read(id, k) ==
    /\ id \in DOMAIN tx /\ tx[id].phase = "Running" /\ k \notin DOMAIN locks
    /\ TxUpdate(id, [tx[id] EXCEPT !.reads = Append(@, [key |-> k, version |-> data[k]])])
Write(id, k, v) ==
    /\ id \in DOMAIN tx /\ tx[id].phase = "Running"
    /\ TxUpdate(id, [tx[id] EXCEPT !.writes = Put(@, k, v)])
Freeze(id) ==
    /\ id \in DOMAIN tx /\ tx[id].phase = "Running"
    /\ TxUpdate(id, [tx[id] EXCEPT !.phase = "Locking"])
Lock(id, k) ==
    /\ id \in DOMAIN tx /\ tx[id].phase = "Locking"
    /\ k \in DOMAIN tx[id].writes /\ k \notin DOMAIN locks
    /\ locks' = Put(locks, k, id) /\ UNCHANGED <<tx, data, clocks, installed, serialCounter>>
GetClock(id, sh) ==
    /\ id \in DOMAIN tx /\ tx[id].phase = "Locking" /\ AllLocked(id)
    /\ sh \notin DOMAIN tx[id].tickets
    /\ \E k \in DOMAIN tx[id].writes : ShardOf[k] = sh
    /\ clocks' = [clocks EXCEPT ![sh] = @ + 1]
    /\ tx' = [tx EXCEPT ![id].tickets = Put(@, sh, clocks[sh] + 1)]
    /\ UNCHANGED <<data, locks, installed, serialCounter>>
Check(id) ==
    /\ id \in DOMAIN tx /\ tx[id].phase = "Locking" /\ AllLocked(id)
    /\ \A k \in DOMAIN tx[id].writes : ShardOf[k] \in DOMAIN tx[id].tickets
    /\ tx' = [tx EXCEPT ![id].phase = "Checking", ![id].serial = serialCounter + 1,
                       ![id].vc = Vector(tx[id])]
    /\ serialCounter' = serialCounter + 1 /\ UNCHANGED <<data, locks, clocks, installed>>
Validate(id, j) ==
    /\ CanValidate(id, j)
    /\ TxUpdate(id, [tx[id] EXCEPT !.checked = @ \cup {j}])
Certify(id) ==
    /\ id \in DOMAIN tx /\ tx[id].phase = "Checking" /\ AllChecked(id)
    /\ TxUpdate(id, [tx[id] EXCEPT !.phase = "Certified"])
Install(id, sh) ==
    /\ id \in DOMAIN tx /\ tx[id].phase = "Certified"
    /\ LET ks == {k \in DOMAIN tx[id].writes : ShardOf[k] = sh} IN
        /\ ks # {} /\ \A k \in ks : Owns(id, k)
        /\ data' = [k \in Keys |-> IF k \in ks THEN
            [writer |-> [present |-> TRUE, id |-> id], value |-> tx[id].writes[k],
             serial |-> tx[id].serial, ticket |-> tx[id].tickets[sh], vc |-> tx[id].vc]
            ELSE data[k]]
        /\ locks' = Without(locks, ks)
        /\ installed' = installed \cup ({id} \X ks)
    /\ UNCHANGED <<tx, clocks, serialCounter>>
Abort(id) ==
    /\ id \in DOMAIN tx /\ tx[id].phase \notin {"Certified", "Aborted"}
    /\ tx' = [tx EXCEPT ![id].phase = "Aborted"]
    /\ locks' = Without(locks, {k \in DOMAIN locks : locks[k] = id})
    /\ UNCHANGED <<data, clocks, installed, serialCounter>>
Next ==
    \/ \E id \in TxIds : Open(id) \/ Freeze(id) \/ Check(id) \/ Certify(id) \/ Abort(id)
    \/ \E id \in TxIds, k \in Keys : Read(id, k) \/ Lock(id, k)
    \/ \E id \in TxIds, k \in Keys, v \in Int : Write(id, k, v)
    \/ \E id \in TxIds, sh \in Shards : GetClock(id, sh) \/ Install(id, sh)
    \/ \E id \in DOMAIN tx : \E j \in 1..Len(tx[id].reads) : Validate(id, j)
    \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars
Certified == {id \in DOMAIN tx : tx[id].phase = "Certified"}
SerialReads ==
    \A id \in Certified : \A j \in 1..Len(tx[id].reads) :
        LET r == tx[id].reads[j] IN
        /\ r.version.serial < tx[id].serial
        /\ IF r.version.writer.present THEN
            LET w == r.version.writer.id IN
                /\ w \in Certified /\ r.key \in DOMAIN tx[w].writes
                /\ r.version.value = tx[w].writes[r.key] /\ r.version.serial = tx[w].serial
           ELSE r.version.value = Base[r.key] /\ r.version.serial = 0
        /\ \A w \in Certified :
            (r.key \in DOMAIN tx[w].writes /\ tx[w].serial < tx[id].serial)
                => tx[w].serial <= r.version.serial
=============================================================================
