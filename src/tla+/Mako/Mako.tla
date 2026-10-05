------------------------------- MODULE Mako -------------------------------
EXTENDS Integers, Naturals, FiniteSets, Sequences

(***************************************************************************
 Mako, OSDI 2025, Sections 4-5 and Appendix A.
 Review companion of src/protocol/Mako/model.rs. Verus checks that Rust
 encoding, not this file or an equivalence theorem between the two files.
 OCC validation and Paxos prefix durability are abstract interfaces.
 No fairness is assumed; this specification states safety only.
***************************************************************************)
CONSTANTS Shards, Workers
ASSUME /\ Shards \in Nat \ {0} /\ Workers \in Nat \ {0}
S == 0..(Shards - 1)
W == 0..(Workers - 1)
Streams == Nat \X S \X W
Cells == Nat \X S
Inf == "infinity"
Bounds == Nat \cup {Inf}
Covered(v, b) == IF b = Inf THEN TRUE ELSE v <= b
BLe(a, b) == IF a = Inf THEN b = Inf ELSE Covered(a, b)
Key(t, i) == <<t.epoch, i, t.part[i]>>
Endpoint(s, k) == IF k \in s.infinity THEN Inf ELSE s.progress[k]
Put(f, k, v) == [x \in (DOMAIN f) \cup {k} |-> IF x = k THEN v ELSE f[x]]
Remove(f, k) == [x \in (DOMAIN f) \ {k} |-> f[x]]
Empty == [x \in {} |-> x]
TxType == [epoch : Nat, vc : [S -> Nat], part : UNION {[A -> W] : A \in SUBSET S}, deps : SUBSET Int]
TxValid(t) == /\ t \in TxType
              /\ DOMAIN t.part # {}
              /\ \A i \in DOMAIN t.part : t.vc[i] > 0
BelowWM(s, t) == \A i \in S : Covered(t.vc[i], s.wm[<<t.epoch, i>>])
BelowCut(s, t) == \A k \in Streams : k[1] = t.epoch => Covered(t.vc[k[2]], Endpoint(s, k))
Doomed(s, id) == /\ id \in DOMAIN s.tx
                 /\ s.tx[id].epoch \in s.finalized
                 /\ ~BelowCut(s, s.tx[id])
VCLe(a, b) == \A i \in S : a.vc[i] <= b.vc[i]

Initial(s) ==
    s = [epoch |-> 0, tx |-> Empty,
         clock |-> [p \in Cells |-> 0],
         tail |-> [k \in Streams |-> 0],
         progress |-> [k \in Streams |-> 0], busy |-> Empty,
         installed |-> {}, durable |-> {}, closed |-> {}, infinity |-> {},
         wm |-> [p \in Cells |-> 0], finalized |-> {},
         acked |-> {}, replayed |-> {}, rolled |-> {}]

ReadMax(s, t, i, v) ==
    /\ \A d \in t.deps : s.tx[d].epoch = t.epoch => s.tx[d].vc[i] <= v
    /\ v = 0 \/ \E d \in t.deps : s.tx[d].epoch = t.epoch /\ s.tx[d].vc[i] = v

Begin(s, z, id, t) ==
    /\ id \notin DOMAIN s.tx
    /\ TxValid(t) /\ t.epoch = s.epoch
    /\ \A d \in t.deps :
        /\ d \in DOMAIN s.tx
        /\ s.tx[d].epoch <= t.epoch
        /\ \E i \in S : <<d, i>> \in s.installed
        /\ s.tx[d].epoch < t.epoch => BelowWM(s, s.tx[d])
    /\ \A i \in S :
        IF i \in DOMAIN t.part THEN
            /\ Key(t, i) \notin DOMAIN s.busy
            /\ Key(t, i) \notin s.closed
            /\ \E r \in Nat : /\ ReadMax(s, t, i, r)
                 /\ t.vc[i] = IF r > s.clock[<<t.epoch, i>>] THEN r ELSE s.clock[<<t.epoch, i>>] + 1
        ELSE ReadMax(s, t, i, t.vc[i])
    /\ LET reserved == {Key(t, i) : i \in DOMAIN t.part}
       IN z = [s EXCEPT !.tx = Put(@, id, t),
           !.clock = [p \in DOMAIN s.clock |->
               IF p[1] = t.epoch /\ p[2] \in DOMAIN t.part THEN t.vc[p[2]] ELSE s.clock[p]],
           !.busy = [k \in (DOMAIN s.busy) \cup reserved |->
               IF k \in reserved THEN id ELSE s.busy[k]]]

Install(s, z, id, i) ==
    /\ id \in DOMAIN s.tx /\ i \in DOMAIN s.tx[id].part
    /\ LET k == Key(s.tx[id], i) IN
       /\ k \in DOMAIN s.busy /\ s.busy[k] = id /\ k \notin s.closed
       /\ z = [s EXCEPT !.installed = @ \cup {<<id, i>>},
                        !.tail[k] = s.tx[id].vc[i], !.busy = Remove(@, k)]

Replicate(s, z, k, p) ==
    /\ k \in Streams /\ k \notin s.closed
    /\ s.progress[k] <= p /\ p <= s.tail[k]
    /\ p = s.progress[k] \/ \E id \in DOMAIN s.tx :
        /\ k[2] \in DOMAIN s.tx[id].part /\ Key(s.tx[id], k[2]) = k
        /\ <<id, k[2]>> \in s.installed /\ s.tx[id].vc[k[2]] = p
    /\ z = [s EXCEPT !.progress[k] = p,
        !.durable = @ \cup {f \in s.installed :
            /\ f[1] \in DOMAIN s.tx /\ f[2] \in DOMAIN s.tx[f[1]].part
            /\ Key(s.tx[f[1]], f[2]) = k /\ s.tx[f[1]].vc[f[2]] <= p}]

Publish(s, z, e, i, b) ==
    /\ i \in S /\ BLe(s.wm[<<e, i>>], b)
    /\ \A k \in Streams : k[1] = e /\ k[2] = i => BLe(b, Endpoint(s, k))
    /\ z = [s EXCEPT !.wm[<<e, i>>] = b]
Advance(s, z) == z = [s EXCEPT !.epoch = @ + 1]
Close(s, z, k, good) ==
    /\ k \in Streams /\ k[1] < s.epoch /\ k \notin s.closed
    /\ good => (k \notin DOMAIN s.busy /\ s.progress[k] = s.tail[k])
    /\ z = [s EXCEPT !.closed = @ \cup {k},
               !.infinity = IF good THEN @ \cup {k} ELSE @]
Finalize(s, z, e) ==
    /\ e < s.epoch
    /\ \A k \in Streams : k[1] = e => k \in s.closed
    /\ z = [s EXCEPT !.finalized = @ \cup {e}]
Acknowledge(s, z, id) ==
    /\ id \in DOMAIN s.tx /\ BelowWM(s, s.tx[id])
    /\ z = [s EXCEPT !.acked = @ \cup {id}]
Replay(s, z, id, i) ==
    /\ <<id, i>> \in s.durable /\ BelowWM(s, s.tx[id])
    /\ z = [s EXCEPT !.replayed = @ \cup {<<id, i>>}]
Rollback(s, z, id, i) ==
    /\ <<id, i>> \in s.installed /\ Doomed(s, id)
    /\ z = [s EXCEPT !.rolled = @ \cup {<<id, i>>}]

NextState(s, z) ==
    \/ \E id \in Int, t \in TxType : Begin(s, z, id, t)
    \/ \E id \in Int, i \in S : Install(s, z, id, i)
    \/ \E k \in Streams, p \in Nat : Replicate(s, z, k, p)
    \/ \E e \in Nat, i \in S, b \in Bounds : Publish(s, z, e, i, b)
    \/ Advance(s, z)
    \/ \E k \in Streams, good \in BOOLEAN : Close(s, z, k, good)
    \/ \E e \in Nat : Finalize(s, z, e)
    \/ \E id \in Int : Acknowledge(s, z, id)
    \/ \E id \in Int, i \in S : Replay(s, z, id, i) \/ Rollback(s, z, id, i)
    \/ z = s

Safety(s) ==
    /\ \A id \in s.acked : \A i \in DOMAIN s.tx[id].part :
        <<id, i>> \in s.durable /\ <<id, i>> \notin s.rolled
    /\ \A f \in s.replayed, j \in S : <<f[1], j>> \notin s.rolled
    /\ \A id \in DOMAIN s.tx : \A d \in s.tx[id].deps :
        Doomed(s, d) => Doomed(s, id) /\ s.tx[id].epoch = s.tx[d].epoch
    /\ \A id \in DOMAIN s.tx : \A i \in DOMAIN s.tx[id].part :
        s.tx[id].epoch \in s.finalized /\ <<id, i>> \notin s.installed => Doomed(s, id)

VARIABLE state
Init == Initial(state)
Next == NextState(state, state')
Spec == Init /\ [][Next]_state
(***************************************************************************
 Target temporal statement: Spec => []Safety(state).
 Checked counterpart: theorem_mako_safety in src/protocol/Mako/safety.rs.
 No TLAPS proof or proved translation is claimed for this companion.
***************************************************************************)
=============================================================================
