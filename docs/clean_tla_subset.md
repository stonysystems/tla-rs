# The Clean TLA+ Subset (C1–C5)

The input contract for the Phase 52 translator. A TLA+ module in this subset can be
mechanically projected from a global multi-server spec into a single-process tla-rs Verus spec
(`LInit` / `LNext` / action predicates). A module outside it cannot — not because the tool is
weak, but because the missing information (which cross-node read becomes which message) is a
human design decision that the source spec does not contain.

The linter (`verus-transpile tla-lint`) is the executable form of this document. It draws the
line between "a human must rewrite this" and "the tool can translate this", and it must give a
precise reason for every rejection.

Plan of record: [`clean_tla_to_verus_translator_plan.md`](clean_tla_to_verus_translator_plan.md).
Corpus: [`transpiler/tests/corpus/`](../transpiler/tests/corpus/README.md).
How to get a spec *into* the subset: [`clean_tla_rewrite_playbook.md`](clean_tla_rewrite_playbook.md).
What the translator has been shown to do: [`clean_tla_translator_evidence.md`](clean_tla_translator_evidence.md).

---

## C1 — Per-node state

**Rule.** Every `VARIABLE` is one of:

- **per-node**: its type is `[Node -> T]` for the node set `Node`, i.e. one value per node; or
- **the network**: the single variable designated under C4; or
- **global-immutable**: a `CONSTANT`, which is not state at all.

A variable that is mutable, shared, and not the network has no projection: after projection
each node holds only its own state, and there is nowhere for a shared value to live.

**Why it is a hard rule.** Projection *deletes the node dimension*. `x \in [Node -> Nat]`
becomes `s.x: nat` — "this node's x". A variable like `crit \in SUBSET Proc` is a set that
spans nodes; dropping the dimension would silently change what the spec says.

**Accept** (LamportMutex): `clock \in [Proc -> Clock]`, `req \in [Proc -> [Proc -> Nat]]`,
`ack \in [Proc -> SUBSET Proc]` — each is one value per node. `req[p]` being itself a function
over `Proc` is fine: it is *p's own table about others*, not other nodes' state.

**Reject** (LamportMutex): `crit \in SUBSET Proc` — the set of nodes in the critical section is
global. The rewrite makes it per-node: `crit \in [Proc -> BOOLEAN]`, and the mutual-exclusion
invariant becomes a statement over all nodes rather than a statement about one set.

**Reject** (ReadersWriters): `readers`, `writers`, `waiting` are all global — the spec models a
shared lock rather than a distributed protocol, so *nothing* is per-node. Such a spec is not
"almost clean"; it has no projection at all. The linter says so plainly rather than reporting
three separate violations.

---

## C2 — No instantaneous cross-node reads

**Rule.** Inside an action parameterized by a node (`Action(self, ...)`), a per-node variable
may only be read at `self`: `x[self]`. Reading `x[other]` for any other index — a different
bound variable, an arithmetic expression, a `CHOOSE` — is out of the subset.

The action may freely read: its own node's state, its parameters, constants, and the fields of
a message it is receiving.

**Why it is the core rule.** `x[other]` says "this node atomically observes another node's
current state". No distributed implementation can do that. Turning it into something
implementable requires deciding *which message carries that value, who sends it, when, and what
the receiver does with a stale copy* — that is protocol design, and it is exactly the
information a global spec omits. This is why global → single-process is not automatable in
general, and why the subset exists.

**Reject** (TeachingConcurrency `Simple`):

```tla
b(self) == /\ pc[self] = "b"
           /\ y' = [y EXCEPT ![self] = x[(self-1) % N]]
```

`x[(self-1) % N]` reads the *left neighbour's* `x`. The rewrite must introduce a message
carrying `x` from that neighbour, and decide what `b` does before it arrives.

**Reject** (Bakery): the doorway reads `num[i]` and `flag[i]` for every other process `i`.
Bakery is a shared-memory algorithm; message-ifying it is a substantial redesign, which is why
it sits at the dirty end of tier 0 — it is the specimen the linter must reject.

**Accept** (LamportMutex):

```tla
beats(p,q) == \/ req[p][q] = 0
              \/ req[p][p] < req[p][q]
```

Every read is `req[p][...]` — p's own table, populated by messages p received earlier. `q` only
indexes *into p's own state*. This is the shape a clean spec has: what a node knows about
others is state it accumulated, not state it peeks at.

**How the linter decides.** Within `Action(self, ...)`, for each per-node variable `x`, every
`x[e]` must have `e` syntactically equal to `self`. Anything else is a violation reported with
the variable, the index expression, and the position.

---

## C3 — No history variables

**Rule.** No variable exists solely to record the past or to aggregate across nodes for the
benefit of an invariant or proof.

**Why.** A history variable is by construction global (C1) and usually reads every node's state
(C2). It also has no runtime meaning: the implementation would have to maintain state that the
protocol never consults.

**Reject** (Raft, ongardie): `allLogs == UNION {log[i] : i \in Server}`, plus `elections` and
`voterLog`, which exist for the invariants. The rewrite deletes them and restates the
invariants over the reachable state.

**Note.** Deleting a history variable can weaken the invariants that mention it. That is a
rewrite decision and must be recorded in the case's `rewrite.md`; the V2 TLC fidelity check
compares observable behaviour, not invariants that no longer exist.

---

## C4 — One designated network variable

**Rule.** Exactly one variable is the network. It is a set (or bag) of messages; each message
carries enough addressing to say who it is for; and it is touched only by the send/receive
idioms:

- **send**: `net' = net \cup {m}` (or `\cup` with a set of messages)
- **receive**: `\E m \in net : ...` with the action guarded on `m` being addressed to `self`
- **discard/consume**: `net' = net \ {m}`

**Why.** P3 rewrites the network away entirely: sends become an action's *output* messages and
receives become an action's *input* parameter, because the tla-rs framework owns delivery. That
rewrite is only sound if the tool knows which variable is the network and that nothing else is
done to it.

**Accept** (Paxos, message-passing variant): a single `msgs` set, `Send(m) == msgs' = msgs \cup
{m}`, receives via `\E m \in msgs`.

**Reject, but cheaply fixable** (LamportMutex): `network \in [Proc -> [Proc -> Seq(Message)]]`
is a 2-D array of per-pair FIFO queues, not a message set. It is still *a* network — the
rewrite flattens it into one set of messages tagged with `src`/`dst`, and records in
`rewrite.md` that pairwise FIFO ordering was dropped. That is a real semantic change, and it is
exactly what the V2 TLC check exists to catch.

**Reject** (any spec with two message-like variables, or one that also filters/rewrites the
network in place): ambiguous, so the human must designate and normalize first.

---

## C5 — Actions are parameterized by node

**Rule.** `Next` is a disjunction of node-parameterized actions:

```tla
Next == \/ \E self \in Node : Action1(self) \/ Action2(self, ...)
        \/ <environment actions>
```

Each disjunct either quantifies over the node set and applies an action to that node, or is an
environment action (message delivery, loss, crash) that the framework — not the projected node
— performs.

**Why.** The projection maps `\E self \in Node : A(self)` to a single-node `LNext(s, s_)`: the
node dimension disappears because the spec is now *about one node*. An action with no node
parameter has no node to be about.

**Accept** (Simple): `Next == (\E self \in 0..N-1: proc(self)) \/ Terminating`.

**Reject**: a `Next` disjunct that names a specific node (`Action(1)`).

**Not a violation**: binding more than one node. The first is the acting node; the rest are
parameters, and the commonest thing a spec does with one is address a message — Raft's
`\E i, j \in Server : RequestVote(i, j)` reads only `i`'s state and sends to `j`. Whether an
action actually reaches into another node's state is exactly what **C2** decides, so C5 leaves
it there rather than rejecting a legitimate shape.

An earlier draft of this rule did reject two-node binding outright, and Raft is what showed that
to be wrong.

---

## What the subset deliberately excludes (Q2)

**Reconfiguration.** Membership changes — Raft's joint consensus, Jetpack's view/epoch
machinery — are out. `Node` is a fixed constant set. A rewrite strips reconfiguration and says
so in `rewrite.md`. Reconfiguration changes what "per-node" even means and would force the
projection to reason about a node set that varies over time.

---

## Linter contract

```
verus-transpile tla-lint [--json] <file.tla>
```

- Exit `0` when the module is in the subset, non-zero otherwise.
- Human output: one line per violation, `line:col: C<n>: <what> — <why it is not projectable>`.
  A violation must name the construct and say what the human has to decide, not merely that
  something is unsupported.
- `--json`: `{"clean": bool, "violations": N, "findings": [{"rule": "C2", "line": .., "column":
  .., "message": ..}], "network_variable": "msgs"|null}`.

The `violations` count is the case's **clean-distance** in the corpus manifest: a cheap,
comparable measure of how much human rewriting a spec needs.

**A spec that fails to parse is not "dirty" — it is unmeasured.** The linter reports the parse
error and exits non-zero without a violation count, so a parser gap never masquerades as a
subset violation.
