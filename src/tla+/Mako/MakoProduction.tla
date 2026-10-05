-------------------------- MODULE MakoProduction --------------------------
EXTENDS Mako
CONSTANT Observers
ASSUME Observers \in Nat \ {0}
O == 0..(Observers - 1)
ViewCells == O \X Nat \X S
MinBound(a, b) == IF BLe(a, b) THEN a ELSE b
MaxBound(a, b) == IF BLe(a, b) THEN b ELSE a
RECURSIVE WorkerMin(_, _, _, _)
WorkerMin(v, e, sh, n) ==
    IF n = 0 THEN Inf ELSE MinBound(WorkerMin(v, e, sh, n-1), v[<<e, sh, n-1>>])

(***************************************************************************
 Companion to production.rs. Verus checks that encoding and its refinement
 proof. This module is SANY-checked, without a proved translation to Verus.
 core.wm is a ghost join of delivered values, never a source for local guards.
 WorkerReport and Gossip sets are authenticated message buffers. Receives
 leave messages available for duplication; explicit Drop actions model loss.
***************************************************************************)
LocalView(p, o) == [p.core EXCEPT !.wm = [q \in Cells |-> p.views[<<o, q[1], q[2]>>]]]
WorkerReport(p, k) == [stream |-> k, value |-> Endpoint(p.core, k), sealed |-> k \in p.core.closed]
Gossip(p, e, sh, o) == [dst |-> o, epoch |-> e, shard |-> sh,
    value |-> p.local[<<e, sh>>], sealed |-> <<e, sh>> \in p.sealedLocal]
AllReported(p, e, sh) == \A w \in W : <<e, sh, w>> \in p.sealedReports
AllFinal(p, o, e) == \A sh \in S : <<o, e, sh>> \in p.sealedViews

ProductionInitial(p) ==
    /\ Initial(p.core)
    /\ p = [core |-> p.core, reports |-> [k \in Streams |-> 0],
        local |-> [q \in Cells |-> 0], views |-> [q \in ViewCells |-> 0],
        sealedReports |-> {}, sealedLocal |-> {}, sealedViews |-> {},
        workerNet |-> {}, gossipNet |-> {}]

CoreOperation(p, z, o) ==
    /\ o \in O
    /\ z = [p EXCEPT !.core = z.core]
    /\ z.core.wm = p.core.wm
    /\ LET before == LocalView(p, o)
           after == [z.core EXCEPT !.wm = before.wm]
       IN \/ \E id \in Int, t \in TxType : Begin(before, after, id, t)
          \/ \E id \in Int, sh \in S : Install(before, after, id, sh)
          \/ \E k \in Streams, v \in Nat : Replicate(before, after, k, v)
          \/ Advance(before, after)
          \/ \E k \in Streams, good \in BOOLEAN : Close(before, after, k, good)
          \/ \E id \in Int : Acknowledge(before, after, id)
          \/ \E id \in Int, sh \in S : Replay(before, after, id, sh)
          \/ before = after

Sample(p, z, k) ==
    /\ k \in Streams
    /\ z = [p EXCEPT !.workerNet = @ \cup {WorkerReport(p, k)}]
ReceiveWorker(p, z, m) ==
    /\ m \in p.workerNet
    /\ z = [p EXCEPT !.reports[m.stream] = MaxBound(@, m.value),
        !.sealedReports = IF m.sealed THEN @ \cup {m.stream} ELSE @]
Compute(p, z, e, sh) ==
    /\ sh \in S
    /\ z = [p EXCEPT !.local[<<e, sh>>] = WorkerMin(p.reports, e, sh, Workers),
        !.sealedLocal = IF AllReported(p, e, sh) THEN @ \cup {<<e, sh>>} ELSE @]
SendGossip(p, z, e, sh, o) ==
    /\ sh \in S /\ o \in O
    /\ z = [p EXCEPT !.gossipNet = @ \cup {Gossip(p, e, sh, o)}]
ReceiveGossip(p, z, m) ==
    /\ m \in p.gossipNet
    /\ z = [p EXCEPT !.views[<<m.dst, m.epoch, m.shard>>] = MaxBound(@, m.value),
        !.sealedViews = IF m.sealed THEN @ \cup {<<m.dst, m.epoch, m.shard>>} ELSE @,
        !.core.wm[<<m.epoch, m.shard>>] = MaxBound(@, m.value)]
Finish(p, z, e, o) ==
    /\ o \in O /\ e < p.core.epoch /\ AllFinal(p, o, e)
    /\ z = [p EXCEPT !.core.finalized = @ \cup {e}]
LocalRollback(p, z, id, sh, o) ==
    /\ o \in O /\ id \in DOMAIN p.core.tx /\ <<id, sh>> \in p.core.installed
    /\ p.core.tx[id].epoch \in p.core.finalized
    /\ AllFinal(p, o, p.core.tx[id].epoch)
    /\ ~BelowWM(LocalView(p, o), p.core.tx[id])
    /\ z = [p EXCEPT !.core.rolled = @ \cup {<<id, sh>>}]
RestartCollector(p, z, e, sh) ==
    /\ sh \in S
    /\ z = [p EXCEPT !.reports = [k \in Streams |->
            IF k[1] = e /\ k[2] = sh THEN 0 ELSE p.reports[k]],
        !.sealedReports = {k \in p.sealedReports : k[1] # e \/ k[2] # sh},
        !.local[<<e, sh>>] = 0, !.sealedLocal = @ \ {<<e, sh>>}]
RestartObserver(p, z, o) ==
    /\ o \in O
    /\ z = [p EXCEPT !.views = [q \in ViewCells |-> IF q[1] = o THEN 0 ELSE p.views[q]],
        !.sealedViews = {q \in p.sealedViews : q[1] # o}]

ProductionNextState(p, z) ==
    \/ \E o \in O : CoreOperation(p, z, o)
    \/ \E k \in Streams : Sample(p, z, k)
    \/ \E m \in p.workerNet : ReceiveWorker(p, z, m)
    \/ \E e \in Nat, sh \in S : Compute(p, z, e, sh)
    \/ \E e \in Nat, sh \in S, o \in O : SendGossip(p, z, e, sh, o)
    \/ \E m \in p.gossipNet : ReceiveGossip(p, z, m)
    \/ \E e \in Nat, o \in O : Finish(p, z, e, o)
    \/ \E id \in Int, sh \in S, o \in O : LocalRollback(p, z, id, sh, o)
    \/ \E m \in p.workerNet : z = [p EXCEPT !.workerNet = @ \ {m}]
    \/ \E m \in p.gossipNet : z = [p EXCEPT !.gossipNet = @ \ {m}]
    \/ \E o \in O : RestartObserver(p, z, o)
    \/ \E e \in Nat, sh \in S : RestartCollector(p, z, e, sh)
    \/ z = p

VARIABLE producer
ProductionInit == ProductionInitial(producer)
ProductionNext == ProductionNextState(producer, producer')
ProductionSpec == ProductionInit /\ [][ProductionNext]_producer
ProducedWatermarksSafe(p) == \A o \in O : \A e \in Nat : \A sh \in S :
    \A w \in W : BLe(p.views[<<o, e, sh>>], Endpoint(p.core, <<e, sh, w>>))
FinalComponentsExact(p) == \A q \in p.sealedViews :
    p.views[q] = WorkerMin([k \in Streams |-> Endpoint(p.core, k)], q[2], q[3], Workers)
=============================================================================
