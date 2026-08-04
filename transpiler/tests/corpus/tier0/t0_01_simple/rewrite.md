# t0_01_simple — rewrite notes

**Source**: `tlaplus/Examples` `specifications/TeachingConcurrency/Simple.tla`
**Pinned commit**: `ab9a2c33566c2e8c9202f292540852282e1fbb32`
**Clean-distance at intake**: 1 (C2)
**Status**: `clean.tla` written, linter accepts, TLC checked both directions.

Lamport's TeachingConcurrency example. N processes in a ring; each sets its own
`x` to 1, then reads its left neighbour's `x` into its own `y`. The property is

```tla
PCorrect == (\A i \in Proc : pc[i] = "Done") => (\E i \in Proc : y[i] = 1)
```

— once everyone has finished, at least one process read a 1.

## Which variable is the network (C4)

There isn't one in the original: it is a shared-memory algorithm. The rewrite
introduces `network` as a set of addressed messages.

## Instantaneous cross-node reads message-ified (C2)

One read, and it is the entire content of the algorithm:

```tla
b(self) == y' = [y EXCEPT ![self] = x[(self-1) % N]]
```

Three message-ifications are possible and **the property is what picks between
them**. This is the clearest small illustration of why the rewrite cannot be
automated.

### Rejected: push

The neighbour broadcasts `x = 1` right after setting it, and `b(self)` waits for
that message.

Wrong: `b` can then only fire after the neighbour ran its `a`, so `y` is always
1. `PCorrect` becomes trivially true, and every behaviour in which a process
reads a 0 — which the original has — is deleted. A rewrite that removes
behaviours is not a faithful one, even when the property still holds.

### Rejected: local cache

Each process keeps its own copy of the neighbour's value, initialised to 0, and
the neighbour pushes an update after `a`. `b(self)` reads the local copy.

Wrong in the other direction: nothing forces the update to be delivered before
`b` fires, so *every* process can read a stale 0 and `PCorrect` is violated.
(This is the same shape of mistake as the LamportMutex FIFO trap in
`t0_05_lamport_mutex/rewrite.md`, and it is worth noting that the natural-looking
"cache what you were told" pattern is the wrong answer here while it is exactly
the right answer there — the difference is whether the property depends on
freshness.)

### Chosen: request / response

`b(self)` sends a read request to its left neighbour and moves to a waiting
state; the neighbour answers with the value it holds **at answer time**; the
requester records the answer and finishes.

This keeps both observations available: the answer is 0 if the neighbour has not
yet run its `a`, and 1 if it has. And `PCorrect` survives, by the same argument
as the original: consider the last reply sent. It was sent to some process `k`
by `Left(k)`. If it carried 0 then `Left(k)` had not yet run its own `a`, so
`Left(k)`'s own request — which it can only send after `a` — is still to come,
and so is the reply to it. That contradicts this being the last reply.

`Reply` is deliberately enabled in **any** control state. The original's read
observes the neighbour whether or not the neighbour has reached any particular
point, and the reply has to be able to do the same.

## C1 / C5

Nothing to do. `x`, `y`, `pc` are already `[Proc -> T]`, and `Next` is already
`\E self \in Proc : ...`. The rewrite adds one control state, `"w"` (waiting for
the reply), splitting the original's atomic `b` into ask and receive.

## No sequence numbers needed

Unlike LamportMutex, this spec needs no explicit message ordering: there is at
most one request and one reply in flight per process, so there is no pair of
messages between the same two nodes whose relative order could matter.

## Out-of-subset constructs stripped

None. The original's TLAPS proof is not part of the spec and is not carried over.

## Semantic-fidelity claim (V2)

TLC 2.19, `N = 4`:

| | original | clean |
|---|---|---|
| distinct states | 193 | 2,001 |
| depth | 9 | — |
| `TypeOK` | holds | holds |
| `PCorrect` | holds | holds |

The clean spec has an order of magnitude more states because one atomic read
became a three-step exchange (ask, answer, receive) plus network state. That is
expected; the counts are not comparable.

**Anti-vacuity check.** A rewrite that had degenerated into the "push" version
would still satisfy `PCorrect`, so passing it proves little on its own. Both
specs were therefore also checked against

```tla
EveryoneReadsOne == \A i \in Proc : (pc[i] = "Done") => (y[i] = 1)
```

and TLC **refutes it on both** — the original and the rewrite agree that reading
a 0 is a real behaviour. This is the observable-behaviour agreement the V2 check
is supposed to establish, done by hand for one property; 53.6 generalises it.

### 53.6 generalised it, and the answer is EQUAL

`tests/corpus/scripts/tlc_fidelity.sh tests/corpus/tier0/t0_01_simple`, at
`N = 3`, observables `x` and `y`:

| | clean | original |
|---|---|---|
| states dumped | 293 | 51 |
| distinct `<<x, y>>` | 18 | 18 |
| result | **EQUAL** | |

The hand-written one-property check above asked "does the rewrite still allow
reading a 0?". This asks the general form of the same question — *which*
`<<x, y>>` pairs are reachable — and the answer is: exactly the original's. The
5.7× difference in raw state count is the three-step exchange and the network,
and it does not touch the values.

`pc` is deliberately **not** compared: the clean spec adds a `"w"` state for the
process waiting on its neighbour's reply, which the original has no counterpart
for precisely because its read is instantaneous. Comparing `pc` would report the
rewrite working as intended as a fidelity failure.

## Golden review (before freezing golden.rs)

Not yet done — `golden.rs` is still to be produced (53.2.d). `reference` is empty:
tla-rs has no hand-written spec for this algorithm.

## Reproducing the TLC runs

`Simple.tla` extends `TLAPS`, which TLC cannot find. A stub module supplying the
proof-backend names (`SMT`, `Z3`, `PTL`, ...) is enough, since TLC ignores proofs:

```bash
mkdir orig && cp original.tla orig/Simple.tla
cat > orig/TLAPS.tla <<'EOF'
------------------------------- MODULE TLAPS -------------------------------
SMT == TRUE
Z3 == TRUE
PTL == TRUE
=============================================================================
EOF
printf 'CONSTANT N = 4\nSPECIFICATION Spec\nINVARIANTS TypeOK PCorrect\n' > orig/Simple.cfg
(cd orig && java -cp tla2tools.jar tlc2.TLC -workers 8 Simple)

mkdir clean && cp clean.tla clean/SimpleClean.tla
printf 'CONSTANT N = 4\nSPECIFICATION Spec\nINVARIANTS TypeOK PCorrect\n' > clean/SimpleClean.cfg
(cd clean && java -cp tla2tools.jar tlc2.TLC -workers 8 SimpleClean)
```
