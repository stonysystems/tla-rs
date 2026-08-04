# The Clean TLA+ Subset — Input Contract and Linter (Phase 52.M0)

Status: implemented. Linter lives in `transpiler/src/tla/clean_subset.rs`,
CLI entry point `verus-transpile clean-lint`.

## 1. Why a subset exists

Phase 51 established the negative result that motivates this whole track:
a **global multi-server** TLA+ spec (per-server arrays, actions that read
`log[j]` for an arbitrary `j`) cannot be mechanically projected onto a
**single-process** Verus spec, because the projection needs to know *which
message* carries the value that the global spec reads instantaneously — and
that information is simply not in the source. Choosing the messages is a human
design act.

Everything *else* in the projection is mechanical:

| pass | what it does |
|---|---|
| P1 | state projection: `[Node -> T]` → single-node `s.field` |
| P2 | de-index actions: `x[self]` → `s.x`, `\E self : A(self)` → `A(s, s_)` |
| P3 | `messages` → framework send/receive (messages leave the state) |
| P4 | `Quorum` / `Cardinality(S) * 2 > N` → local counting on `s.responses` |
| P5 | frame conditions: auto-emit `s_.x == s.x` for untouched fields |

So the translator's contract is: **the human message-ifies, the tool
projects.** The clean subset is that contract written down, and the linter is
that contract made executable — it draws the line at a precise, checkable
place instead of leaving it to taste.

A clean report means "the Phase 52 passes can project this". It does **not**
mean the spec is correct; semantic fidelity of the human rewrite is checked
separately by TLC (`clean.tla` vs `original.tla`, plan §4 V2).

## 2. The contract

### C1 — every variable is per-node, or the network

Each `VARIABLE` must be either

* **per-node**: morally `[Node -> T]`, one independent copy per node, or
* **the network**: the single designated message variable.

A global scalar (`turn`, `epoch`, `leaderCount`) has no single-process
counterpart: after projection each node holds only its own state, so a variable
that is *shared* would have to become a message exchange. That is a human
rewrite, not a projection.

The linter classifies a variable as per-node when it is indexed (`v[i]`),
EXCEPT-updated (`[v EXCEPT ![i] = ...]`), built as `v = [i \in Node |-> ...]`,
or typed `v \in [Node -> T]` in a `TypeOK`-style operator.

### C2 — no instantaneous cross-node reads

Inside an action, the readable universe is:

* `x[self]` for a per-node variable `x`,
* the action's own parameters,
* the received message `m`.

Reading `x[j]` for any other node symbol `j` is rejected, and so is indexing by
a message header (`votes[m.src]` is fine — it stores a node id — but
`log[m.src]` reads the *sender's* state through the back door). Also rejected:
reading the whole array (`Cardinality(state)`) and rewriting the whole array in
an action (`x' = [i \in Node |-> ...]`, which only `Init` may do).

Frame conditions of the form `x' = x` and `\A j \in Node : x'[j] = x[j]` are
recognised and exempt: they mention a non-self index but carry no information
across nodes, and pass P5 regenerates them anyway.

### C3 — no history variables

History (ghost) variables exist to make the *original* proof go through
(`allLogs`, `elections`, `voterLog`). They aggregate a global view of state
that no node can observe, so they have no projection.

Two syntactic signals:

* **write-only accumulation** — a variable that only ever grows
  (`h' = h \cup {..}`, `h' = h + 1`) and is never read by `Init` or by any
  action guard or by another variable's update. Reads in invariants and
  theorems deliberately do not count: that is precisely what a history variable
  is for.
* **aggregation over the node set** — `{ log[i] : i \in Server }`,
  `UNION {...}`, `[i \in Server |-> f(x[i])]`, i.e. a comprehension over the
  node set whose body reads per-node state at the comprehension's own bound
  variable.

A variable updated with `EXCEPT` is never reported as history state, even if
this module happens not to read it — `EXCEPT` is real per-node state whose
readers may live in another module.

### C4 — exactly one designated network variable

Exactly one variable is the message set. It may only be:

* **sent to**: `messages' = messages \cup {m}`
* **discarded from**: `messages' = messages \ {m}`
* **replied on**: `messages' = (messages \ {m}) \cup {m2}`
* **received from**: `\E m \in messages : ...`
* or passed to a whitelisted helper (`Send`, `Reply`, `Discard`, `Broadcast`,
  `Receive`, `WithMessage`, `WithoutMessage`, …).

Anything else (`messages' = {}`, indexing the network, cardinality of the whole
network) assumes a global view of the channel that the framework does not
provide.

Every sent message record must carry a **source** and a **destination** field
(`src`/`source`/`msource`/`from`/`sender` and `dst`/`dest`/`mdest`/`to`/
`receiver`/`target`): the runtime routes on them.

The network variable is found by name first (`messages`, `msgs`, `sentMsg`,
`network`, …); if no conventional name exists but exactly one variable has the
accumulate-with-`\cup` shape, it is inferred and a **warning** is emitted, since
an inferred choice should be made explicit before the corpus freezes it.

### C5 — actions are parameterised by node

`Next` must be a disjunction whose disjuncts are either

* `\E self \in Node : Action(self, ...)` — a protocol step, or
* an **environment action** that writes nothing but the network (message loss,
  duplication, reordering).

An unquantified disjunct that touches per-node state does not say *which* node
executes it, so there is nothing to project onto. `Init` and `Next` must both
exist.

## 3. Diagnostic codes

| code | rule | meaning |
|---|---|---|
| `CS001` | C1 | variable is neither per-node nor the network |
| `CS003` | C2 | cross-node read / index that is not `self` |
| `CS005` | C3 | write-only accumulator — a history variable |
| `CS006` | C3 | aggregation of per-node state over the whole node set |
| `CS007` | C4 | no network variable found |
| `CS008` | C4 | more than one variable looks like the network |
| `CS009` | C4 | network updated by a non-send/receive/discard shape |
| `CS010` | C4 | sent message is missing `src`/`dst` |
| `CS011` | C5 | no `Next` |
| `CS012` | C5 | `Next` disjunct is neither node-quantified nor network-only |
| `CS014` | C5 | no `Init` |
| `CS015` | C2 | whole per-node array read |
| `CS016` | C2 | whole per-node array written inside an action |
| `CS018` | C1 | node set could not be determined |
| `CS019` | C4 | network variable inferred from shape (**warning**) |

Every diagnostic carries the operator, the operator's source line, and a hint
that names the rewrite the human has to perform. `CS019` is the only warning;
all other codes are errors, and the **clean distance** of a spec is its error
count — the number used to grade corpus candidates in Phase 53.

## 4. Using it

```bash
# accept / reject
verus-transpile clean-lint --input spec.tla

# corpus intake: never fail, just measure how far from clean the spec is
verus-transpile clean-lint --input spec.tla --json --no-fail

# when the spec does not use conventional names
verus-transpile clean-lint --input spec.tla --node-set Replica --network-var wire
```

Exit code is `1` when the spec is not clean, `0` otherwise (or always `0` with
`--no-fail`). `--json` emits the module summary, the per-variable
classification, the action list, and the full violation list.

Programmatic entry points:

```rust
use verus_transpiler::tla::{lint_module, lint_module_with_config, parse_module, CleanSubsetConfig};

let module = parse_module(&source)?;
let report = lint_module(&module);
if report.is_clean() { /* the Phase 52 passes can project it */ }
```

## 5. Reference fixtures

`transpiler/tests/fixtures/clean_subset/`:

* `CleanVoting.tla` — the positive reference. A leader-election-shaped spec
  satisfying all five rules; read it as the target of a rewrite.
* `DirtyGlobalRaft.tla` — the negative reference. Reproduces in miniature what
  real global specs do: cross-node reads, `elections`-style history variables,
  `{log[i] : i \in Server}` aggregation, a global counter, an unrouted message,
  `messages' = {}`, an unquantified `Next` disjunct, a whole-array write.
* `SharedMemoryFlags.tla` — the other failure family: no network at all, and
  mutual exclusion by reading the peer's flag. No mechanical rewrite fixes
  this; the human must introduce messages first.

`transpiler/tests/clean_subset_lint_test.rs` asserts the expected verdict and
codes for each; 26 further unit tests in the module cover one rule each.

## 6. Known limitations

These are honest gaps, not silent ones:

* **The linter is only as good as the front-end parser.** `transpiler/src/tla`
  does not yet accept multi-binding comprehensions
  (`{ e : x \in S, y \in T }` — this is what stops `docs/jetpack_reference/
  base_raft.tla` at line 129), bulleted `/\` lists in some positions, or
  `INSTANCE` composition. A spec that fails to parse cannot be linted; Phase
  53.1 intake must report parse failures separately from clean distance.
* **Interprocedural analysis is one level deep.** `Next` call sites fix each
  action's `self` symbol; helper operators called from an action are checked
  with their own first parameter as `self`, which can mis-attribute `self` in
  helpers that take the node in a later position.
* **C1 classification is syntactic.** A per-node variable that is never indexed
  in this module (e.g. only touched through an `INSTANCE`) will be reported as
  unclassified.
* **C3 write-only detection ignores invariants and theorems by design.** A
  variable read only by an invariant is a history variable under this contract;
  that is the intended verdict, but it means deleting it changes what the
  original spec can state about itself.

## 7. Where this fits

* Plan: `docs/clean_tla_to_verus_translator_plan.md` §1 (subset), §5 (M0).
* Next milestone, 52.M1: the P1/P2/P5 projection passes, gated on this linter.
* Phase 53 consumes the linter for corpus intake (`53.1`), using clean distance
  to grade candidates into tiers.
