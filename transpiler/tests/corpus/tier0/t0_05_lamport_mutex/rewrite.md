# t0_05_lamport_mutex — rewrite notes

**Source**: `tlaplus/Examples` `specifications/lamport_mutex/LamportMutex.tla`
**Pinned commit**: `b17be0a959108701a89b5cadec1a1ee1b216f7a4`
**Clean-distance at intake**: 2 (C1 on `crit`, C4 on `network`)
**Status**: `clean.tla` written, linter accepts, TLC checked.

Lamport's 1978 distributed mutual-exclusion algorithm. It was chosen as tier-0's
*accept* specimen because it is already message-passing and has no instantaneous
cross-node reads — `beats(p,q)` reads only `req[p][...]`, which is p's own
accumulated table about q rather than q's live state.

## Which variable is the network (C4)

`network`. In the original it is `[Proc -> [Proc -> Seq(Message)]]` — a FIFO
queue per ordered pair of processes, indexed `network[sender][receiver]`.

The clean subset requires one *set* of messages, because the projection replaces
the network with framework send/receive and cannot reason about a
per-connection structure. So `network` became `network \subseteq Message`, and
messages gained `src` and `dst` fields to carry the addressing the array indices
used to encode.

## The FIFO ordering is load-bearing — and dropping it broke the algorithm

This is the substantive finding of this rewrite, and the reason the case is
worth having.

Flattening per-connection queues into one set silently drops the ordering
guarantee `network[s][r]` provided: messages from s to r were delivered in send
order. The first version of `clean.tla` did exactly that and nothing else. TLC
refuted it in 13 states:

```
State 3: p1 and p2 have both requested.
         network holds req(1->2), req(1->3), req(2->1), req(2->3)
State 4: p1 receives req(2->1), sets req[1][2] = 1, sends ack(1->2)
State 5: p2 receives ack(1->2)  <-- while req(1->2) is STILL in the network
...
State 13: crit = <<TRUE, TRUE, FALSE>>   MutualExclusion violated
```

The mechanism: p1 sent `req(1->2)` *before* `ack(1->2)`. In the original both
travel on `network[1][2]`, a FIFO queue, so p2 must consume the request first
and record `req[2][1] = 1`. With a flat set p2 can take the acknowledgement
first, leaving `req[2][1] = 0`, which makes `beats(2,1)` vacuously true — p2
then enters the critical section believing p1 has no outstanding request, while
p1's own tie-break (`req[1][1] = req[1][2] /\ 1 < 2`) also lets p1 in.

**Fix**: the ordering is now explicit protocol state rather than an assumption
about the medium.

- Every message carries `seq`.
- `sendSeq[p][q]` — the next number p will use toward q. A broadcast advances
  every peer's counter; a point-to-point send advances one.
- `recvSeq[p][q]` — the next number p will accept from q.
- `Deliverable(p, m) == m.dst = p /\ m.seq = recvSeq[p][m.src]` guards every
  receive, and accepting a message advances `recvSeq[p][m.src]`.

Both tables are `[Proc -> [Proc -> Nat]]`, i.e. per-node state indexed by peer,
so they are C1-clean and their reads are C2-clean (the outer index is always the
acting node).

This is the general shape of the rule: **the clean subset has no channels, so a
spec that depends on channel ordering must carry that ordering in its own
state.** A translator cannot infer it, which is exactly why the rewrite is a
human step.

## C1: `crit` became per-node

`crit \in SUBSET Proc` — the set of processes in the critical section — is
global mutable state spanning nodes, so it has nowhere to live after
projection. It is now `crit \in [Proc -> BOOLEAN]`.

The safety property was restated accordingly:

```tla
\* original
Mutex == \A p, q \in crit : p = q
\* clean
MutualExclusion == \A p, q \in Proc : (p # q) => ~ (crit[p] /\ crit[q])
```

## C5: receives take the message, not a second node

The original's `Next` binds two processes at once:

```tla
\/ \E p \in Proc : \E q \in Proc \ {p} :
      ReceiveRequest(p,q) \/ ReceiveAck(p,q) \/ ReceiveRelease(p,q)
```

An atomic two-node step is a cross-node read in disguise. In the clean version
the receiving node is the only bound node and the sender is read off the message
(`m.src`), which is what a real receiver has:

```tla
\/ \E m \in network :
      \/ ReceiveRequest(p, m) \/ ReceiveAck(p, m) \/ ReceiveRelease(p, m)
```

## Instantaneous cross-node reads message-ified (C2)

None were needed. Every read in the original is already into the acting node's
own state.

## Out-of-subset constructs stripped

None. There is no reconfiguration: `Proc == 1..N` is fixed.

The original's `BoundedNetwork == \A p,q \in Proc : Len(network[p][q]) <= 3`
invariant has no counterpart — there are no per-connection channels to bound.
`SeqConstraint` was added in its place, bounding the sequence numbers for model
checking exactly as `ClockConstraint` bounds the clocks.

## Semantic-fidelity claim (V2)

Both specs model-checked with TLC 2.19, `N = 3`, `maxClock = 6`, `Nat <- 0..7`:

| | original | clean |
|---|---|---|
| distinct states | 724,274 | 1,064,028 |
| depth | 61 | 55 |
| `TypeOK` | holds | holds |
| mutual exclusion | holds (`Mutex`) | holds (`MutualExclusion`) |

**The state counts are not comparable and are not expected to match.** The
rewrite changes the state *shape* — queues become a set, `crit` becomes a
function, two sequence-number tables are added — so the reachable state sets are
not in correspondence. What is compared is the safety property, which holds in
both, plus the refutation history above: the intermediate version that dropped
FIFO ordering *failed* this check, which is what gives the passing result its
meaning.

A stronger observable-behaviour comparison (per Q3/D2) needs the bespoke
spec-vs-spec comparator planned in **53.6**. This case is exactly the one that
comparator has to handle, since a naive state-count diff would call a correct
rewrite a failure.

## Golden review (before freezing golden.rs)

Not yet done — `golden.rs` is still to be produced (53.2). `reference` is empty
for this case: tla-rs has no hand-written LamportMutex spec.

## Reproducing the TLC runs

```bash
# original
mkdir orig && cp original.tla orig/LamportMutex.tla && cp MCLamportMutex.tla orig/
cp original.cfg orig/MCLamportMutex.cfg
(cd orig && java -cp tla2tools.jar tlc2.TLC -workers 8 MCLamportMutex)

# clean -- needs an MC wrapper for the Nat override and the combined constraint
mkdir clean && cp clean.tla clean/LamportMutexClean.tla
cat > clean/MCLamportMutexClean.tla <<'EOF'
------------------------ MODULE MCLamportMutexClean ------------------------
EXTENDS LamportMutexClean
CONSTANT MaxNat
ASSUME MaxNat \in Nat
NatOverride == 0 .. MaxNat
Constraint == ClockConstraint /\ SeqConstraint
=============================================================================
EOF
cat > clean/MCLamportMutexClean.cfg <<'EOF'
CONSTANTS
  N = 3
  MaxNat = 7
  maxClock = 6
  Nat <- NatOverride
INVARIANTS TypeOK MutualExclusion
SPECIFICATION Spec
CONSTRAINT Constraint
EOF
(cd clean && java -cp tla2tools.jar tlc2.TLC -workers 8 MCLamportMutexClean)
```

53.6 will replace these hand-run steps with a script.
