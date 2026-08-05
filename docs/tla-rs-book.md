# The tla-rs Book

`tla-rs` lets you write TLA-style state-machine specifications in Rust and
[Verus](https://verus-lang.github.io/verus/), explore finite instances of those
specifications, and derive executable Rust functions together with the contracts that relate
them back to the specification. It is primarily a Verus reimplementation of the ideas in
[IronFleet](https://doi.org/10.1145/2815400.2815428) and
[AutoMan](https://doi.org/10.1145/3731569.3764822), extended with more protocols,
TLA+/Verus translation, source-first model checking, DPOR, and a deployable networking
runtime.

Part I is a user guide: it takes a specification through generation, checking,
verification, compilation, and execution. Part II is a developer guide for changing the
transpiler, proofs, model checker, protocol integrations, runtime, and build system.

> **Scope of this book.** This is a guide to the current repository, not a record of every
> development phase. When prose disagrees with source, tests, configuration, or CI, the
> executable artifact wins. Exact verification totals and performance measurements are
> snapshots; reproduce them before citing them.

## What is in the project

The repository contains ten integrated protocol families: RSL (a Multi-Paxos replicated
state machine), single-decree Paxos, Raft, EPaxos, PBFT, Chain Replication,
Primary-Backup, Vertical Paxos, Two-Phase Commit, and Bully-style leader election. Each is
mounted in the common Rust/Verus crate and has generated code plus a service integration.
Jetpack recovery-layer work is present as protocol-specification research, while the old
Lock material is retained as legacy source and is not mounted with the integrated protocols.

The project has four related, but distinct, tool paths:

| Goal | Start with | Primary tool path | Result |
|---|---|---|---|
| Write and run a verified transition | Verus relational spec | `.automan` + `_transpile.toml` → transpiler → Verus | Executable Rust with refinement contracts |
| Find finite-state bugs | Verus `LInit`/`LNext` spec | `model-check` + `model.toml` | Counterexample or bounded search evidence |
| Bring in an existing TLA+ model | TLA+ module | `translate-tla`, or human cleanup → `tla-lint` → `clean-tla` | Verus protocol-layer specification |
| Compare with TLC | TLA+ or Verus model | wrapper/parity export tools | Normalized states and transitions for comparison |

These paths can be combined, but none silently proves the result of another. In particular,
translation creates an artifact; model checking explores a finite model; and Verus checks
the proof obligations that are actually present after trusted boundaries are accounted for.

## The evidence ladder

Use the strongest claim justified by the artifact you ran:

| Evidence | A justified claim | A claim it does not justify |
|---|---|---|
| `tla-lint` accepts a module | The parsed module meets the implemented C1–C5 projection contract | The protocol is correct, or even that projection preserves every intended property |
| `clean-tla` emits Rust/Verus | The accepted module was mechanically projected into a protocol-layer spec | The emitted spec or an implementation has been proved correct |
| Exact model search reaches `FrontierExhausted` | No checked violation exists in the resolved finite model | The property holds for unbounded nodes, values, messages, or executions |
| A lossy or incomplete model search finds a trace | The trace is a concrete candidate bug to inspect | Absence of a trace is evidence of safety |
| Verus reports a body verified | That body meets its contract under its preconditions and admitted dependencies | The specification, trusted bodies, FFI, or environment is correct |
| An end-to-end service runs | The compiled integration executes for that test scenario | Its safety or liveness follows merely from the successful run |

An `assume` accepts a proposition at a proof site. `#[verifier::external_body]` and external
function specifications trust a body or interface contract. The project also uses
`#[verus::trusted]` as a trusted-code *audit classification* for Verus line accounting; it
identifies code that requires manual inspection and should not be confused with a successful
proof of its assumptions. Finally, the C# network runtime and unsafe Rust/FFI entry points
sit outside the deductively verified protocol core. Chapter 14 develops this trust model in
detail.

## End-to-end artifact flow

```text
TLA+ source (optional)
       │
       ├── translate-tla
       └── human message-aware rewrite → tla-lint → clean-tla
       ▼
Verus TLA-style specification ───────────────► finite model checking
       │                                           │
       │ .automan modes + _transpile.toml          ├── counterexample
       ▼                                           └── bounded evidence
spec-to-exec transpiler
       │
       ├── concrete types and executable transitions
       └── requires/ensures and generated proof obligations
       ▼
Verus verification
       ▼
Rust shared library ── FFI ── C# I/O and service runtime
       ▼
runnable distributed service
```

The hand-written sources and derived artifacts are deliberately separate:

| Artifact | Purpose | Ownership |
|---|---|---|
| `src/protocol/<P>/*.rs` | Logical state, actions, invariants, and refinement proofs | Hand-written |
| `*.automan` | Input/output modes and helper signatures | Hand-written |
| `*_transpile.toml` | Naming, mappings, proof generation, and calling convention | Hand-written |
| `src/generated/<P>/*_gen.rs` | Concrete types and executable transitions | Generated; never hand-edit |
| `src/implementation/<P>/` | Host and runtime-facing protocol integration | Hand-written unless marked otherwise |
| `src/services/<P>/` | Service entry points | Hand-written integration |
| `model.toml` | Finite domains, search bounds, and checked properties | Hand-written |
| `reports/` | Reproducible checking and performance evidence | Generated where its README says so |

If generated output is wrong, change the specification, annotation, configuration, or
transpiler and regenerate it. Hand-editing `src/generated/` makes the checked-in program
irreproducible and is prohibited by [`AGENTS.md`](../AGENTS.md).

## Notation used throughout

| Notation | Meaning |
|---|---|
| `L*` | Logical/specification type or operation |
| `C*` | Concrete/executable type or operation |
| `s`, `s_` | Pre-state and post-state of a relational action |
| `spec fn` | Mathematical ghost function; erased from the executable |
| `proof fn` | Ghost lemma or proof procedure; erased from the executable |
| `exec fn` | Executable function checked against its contract |
| `value@` | The logical view of a concrete value through `View` |
| `+`, `-` | Supplied input and synthesized output in an AutoMan annotation |

Logical `int`, `Set`, and `Map` values are mathematical and need not be machine-bounded.
Executable integer and collection types are finite representations, so their functions often
need range, validity, or finite-domain preconditions.

## Reading routes

| If you want to… | Read |
|---|---|
| Try the project | Chapters 1–3 and the Counter quickstart in Chapter 2 |
| Write a Verus specification | Chapters 3–7, then Chapter 11 |
| Start from TLA+ | Chapters 3, 9, 8, and 7 |
| Model check a protocol | Chapters 3 and 8; contributors continue with Chapter 22 |
| Run an included service | Chapters 2, 7, and 10 |
| Contribute to the transpiler or proofs | Chapters 13–20 and 24–27 |
| Change translation or model checking | Chapters 22–24 and the relevant appendices |

# Part I — User Guide

Part I follows the main user path from a small relational specification to generated,
verified, executable code, then extends that path to model checking, TLA+ conversion, and
the integrated distributed services.

## Chapter 1 — Welcome to tla-rs

`tla-rs` is a framework for describing distributed state machines as
TLA-style relations in Rust and Verus, checking finite instances of those
relations, and generating executable Rust functions whose contracts connect
the concrete computation back to the logical specification.

The project brings together two lines of work:

- [IronFleet](https://doi.org/10.1145/2815400.2815428) supplies the refinement
  methodology, verified distributed-systems architecture, and the
  Multi-Paxos replicated-state-machine lineage.
- [AutoMan](https://doi.org/10.1145/3731569.3764822) supplies the idea of using
  input/output modes to synthesize executable implementations and their proof
  obligations from relational specifications.

Both original projects used Dafny. tla-rs re-expresses their core ideas in
Rust with [Verus](https://github.com/verus-lang/verus), then extends the
workflow with more protocols, TLA+/Verus translation, source-first model
checking, DPOR search, code-generation options for Rust ownership patterns,
and a C# networking/runtime layer. The root [README](../README.md) gives the
short project overview and paper attribution.

### What is included

The current crate mounts ten protocol families. Their selectors are also the
names accepted by the shared server entry point, except that RSL has a
separate recommended UDP server binary.

| Protocol | Repository module | Shared-server selector |
|---|---|---|
| Replicated State Machine / Multi-Paxos (RSL) | `RSL` | `rsl` |
| Single-Decree Paxos | `Paxos` | `paxos` |
| Raft | `Raft` | `raft` |
| EPaxos | `EPaxos` | `epaxos` |
| PBFT | `PBFT` | `pbft` |
| Chain Replication | `ChainReplication` | `chainreplication` |
| Primary-Backup | `PrimaryBackup` | `primarybackup` |
| Vertical Paxos | `VerticalPaxos` | `verticalpaxos` |
| Two-Phase Commit | `TwoPhase` | `twophase` |
| Bully-style Leader Election | `LeaderElection` | `leaderelection` |

The presence of a protocol in this table does not mean that every protocol
has the same proof depth, performance tuning, client workload, or remaining
assumptions. In particular, do not read “included” as “Byzantine fault
tolerant”: PBFT is Byzantine-fault-tolerant, while several other entries have
crash-fault or coordination semantics.

### The workflow at a glance

The common path is:

```text
hand-written Verus spec                    optional TLA+ source
  types + Init/actions/Next/invariants          │
                │                               │ translate/project
                ├──────── bounded model check ◄─┘
                │          finite evidence
                │
         .automan input/output modes
         _transpile.toml codegen policy
                │
                ▼
        spec-to-exec transpiler
                │
                ├── concrete C* types
                ├── executable C* functions
                └── requires/ensures and proof code
                │
                ▼
          Verus verification
                │
                ▼
       Rust shared library + C# runtime
                │
                ▼
       runnable distributed service
```

The repository keeps these concerns separate:

| Location | Responsibility |
|---|---|
| `src/protocol/<P>/` | Logical types, protocol actions, invariants, and refinement proofs |
| `src/generated/<P>/` | Transpiler output; never hand-edit |
| `src/implementation/<P>/` | Concrete support code, host/scheduler integration, and messages |
| `src/services/<P>/` | Service entry points |
| `transpiler/` | Spec parser, mode analysis, code generation, TLA+ tools, and model checker |
| `csharp/` | Networking, certificate handling, clients, and process lifecycle |

### What the evidence means

Formal-methods vocabulary becomes dangerous when different kinds of evidence
are blurred together. This book uses the following meanings consistently.

| Evidence or boundary | What it supports | What it does not establish by itself |
|---|---|---|
| A Verus-verified function | The checked body satisfies its stated contract under its preconditions and trusted dependencies | That the contract is the intended specification, or that dependencies and the environment are correct |
| An `ensures` refinement link | The concrete result's logical view satisfies a named logical relation | An end-to-end theorem outside that relation's scope |
| A bounded model-check result | No configured violation was found in the resolved finite model before the reported stop condition | An unbounded proof over all values and executions |
| `assume(...)` | Verus may use the proposition without a proof at that site | Evidence that the proposition is true |
| `#[verifier(external_body)]` or an external specification | A trusted body is used through a specified interface | Verification of the hidden implementation |
| C#/FFI and host/runtime code | The machinery that performs real I/O and invokes the protocol | Deductive Verus verification unless a particular relation is explicitly modeled and proved |

`#[verus::trusted]` deserves a separate warning: in this tree it is used as an
audit/line-count classification marker. Do not infer from the marker alone
that Verus skipped the annotated code. Audit actual assumptions and unchecked
boundaries through `assume`, `external_body`, external specifications, and the
FFI/runtime surface.

The generated-code policy is equally important. Files below `src/generated/`
have one source of truth: the transpiler, its configuration, and its inputs.
If generated code is wrong or fails verification, change those sources and
regenerate. Do not patch the derived Rust file. See [AGENTS.md](../AGENTS.md)
for the repository policy.

### Safety, liveness, and refinement

Most Verus work in this repository concerns state invariants, executable
contracts, and refinement: statements about individual states or steps and
their relation to a higher-level specification. The source-first model checker
can also diagnose bounded `leads_to` obligations with fairness configuration,
but only after fully exploring the configured finite graph. Neither facility
silently upgrades the other: a bounded search is not an unbounded proof, and a
function contract is not automatically a temporal theorem.

If you are new to the project, read Chapters 2–7 in order, then Chapter 8 for
model checking and Chapter 10 for running a cluster. Existing TLA+ users can
read Chapter 9 after the mental model in Chapter 3.

## Chapter 2 — Install tla-rs and Run the Counter Quickstart

The counter example is the smallest complete proof-producing workflow in the
repository. It has no C# or networking dependency: you need a Rust toolchain,
the transpiler's Cargo dependencies, and Verus.

### Prerequisites

The versions below are the versions pinned by the current CI workflow, not a
promise that unrelated future releases will behave identically.

| Tool | Current tested version or role |
|---|---|
| Platform | Linux x86-64; CI verification runs on Ubuntu 24.04 |
| Verus | `0.2026.08.02.b677dd5` |
| Rust for that Verus release | `1.97.1` |
| Rust for the transpiler | A recent stable toolchain |
| .NET SDK | 6.0.x, needed only for the integrated services |
| Python and SCons | Needed only for the integrated build; install SCons with `pip install scons` |

The pinned Verus Linux binary links against glibc 2.39, which is why the CI
verification job uses Ubuntu 24.04. Download the matching Verus release, make
its `verus` binary executable, and point `VERUS_PATH` at the binary itself:

```bash
export VERUS_PATH=/absolute/path/to/verus/verus

"$VERUS_PATH" --version
rustc --version
cargo --version
```

Run the remaining commands from the repository root.

### Read the four quickstart artifacts

The logical source is
[`examples/quickstart/counter_spec.rs`](../examples/quickstart/counter_spec.rs):

```rust
use vstd::prelude::*;

verus! {
    pub open spec fn LInit(value: int) -> bool {
        value == 0
    }

    pub open spec fn LIncrement(value: int, value_: int) -> bool {
        value_ == value + 1
    }
}
```

`LIncrement` is a relation. It says which pair of old and new values is a
valid step; it does not yet say how executable Rust computes the new value.

The mode file
[`counter_spec.automan`](../examples/quickstart/counter_spec.automan) supplies
that data flow:

```text
module counter_spec {
    LInit(-);
    LIncrement(+, -);
}
```

`+` means the caller supplies the argument. `-` means the generated function
must synthesize it. The configuration
[`counter_transpile.toml`](../examples/quickstart/counter_transpile.toml) maps
logical `int` to executable `i64`, asks for proof generation, imports the
logical source, and adds the overflow precondition required by bounded `i64`
addition. The checked-in
[`counter_gen.rs`](../examples/quickstart/counter_gen.rs) is generated output,
and [`main.rs`](../examples/quickstart/main.rs) is the executable runner.

### Generate

Generate the executable functions from the repository root:

```bash
cargo run --manifest-path transpiler/Cargo.toml -- \
  -i examples/quickstart/counter_spec.rs \
  -a examples/quickstart/counter_spec.automan \
  -c examples/quickstart/counter_transpile.toml \
  -o examples/quickstart/counter_gen.rs
```

This command is allowed to replace `counter_gen.rs` because the transpiler is
its source. It should reproduce the checked-in file exactly:

```bash
git diff --exit-code -- examples/quickstart/counter_gen.rs
```

Do not “fix” a difference in `counter_gen.rs`. Investigate the spec,
annotation, configuration, transpiler version, or stale checked-in artifact.

### Inspect the generated contract

The generated increment is intentionally small:

```rust
pub exec fn CIncrement(value: &i64) -> (result: i64)
requires
    *value < i64::MAX,
ensures
    LIncrement(*value as int, result as int),
{
    ((*value) + 1)
}
```

The `requires` clause accounts for the difference between mathematical `int`
and bounded `i64`. The `ensures` clause is the refinement link: after casting
the executable values to logical integers, the result satisfies
`LIncrement`. The body itself is ordinary executable addition.

### Verify, compile, and run

Verus can verify and compile the runner in one command:

```bash
"$VERUS_PATH" --compile examples/quickstart/main.rs -o /tmp/tla-rs-counter
/tmp/tla-rs-counter
```

The relevant output is:

```text
verification results:: 2 verified, 0 errors
Counter: 0 -> 1
```

“2 verified” means Verus checked the two generated executable functions in
this crate against their contracts. It does not prove a network protocol, an
infinite temporal property, or the correctness of Verus itself.

CI uses a stricter wrapper that regenerates into a temporary directory,
compares bytes, rejects `assume`, `admit`, and `external_body` in this example,
and—when `VERUS_PATH` is set—verifies, compiles, and runs it:

```bash
VERUS_PATH="$VERUS_PATH" ./scripts/check_readme_quickstart.sh
```

If that script passes without `VERUS_PATH`, it has checked regeneration and
the absence of those proof shortcuts, but it has not performed the Verus
compile/run stage.

## Chapter 3 — The tla-rs Mental Model

### A protocol is a relation over states

A state machine has four basic ingredients:

- **constants**, fixed for one model or deployment;
- **state**, the values that may change;
- **initialization**, a predicate selecting allowed first states; and
- **actions**, relations selecting allowed pre-state/post-state pairs.

If `s` is the current state and `s_` is the next state, an action such as

```rust
pub open spec fn LIncrement(value: int, value_: int) -> bool {
    value_ == value + 1
}
```

describes a valid step. For a structured state the same idea appears as
`LAction(s, s_, c, ...)`. `LNext` normally composes named actions with
disjunction. An invariant is a state predicate expected to hold initially and
to be preserved by every step.

Relational specifications are more general than executable functions. A
relation can permit several post-states, quantify over an unknown witness, or
leave a field unconstrained. An executable Rust function must choose one
finite result. The annotation and transpiler configuration identify the
functionalizable part of the relation; Chapter 5 explains the restrictions.

### Three Verus modes

Verus separates mathematical description, proof, and execution:

```rust
verus! {
    pub open spec fn abstract_relation(x: int, y: int) -> bool {
        y == x + 1
    }

    pub proof fn relation_is_increasing(x: int, y: int)
        requires abstract_relation(x, y)
        ensures y > x
    {
    }

    pub exec fn concrete_step(x: i64) -> (y: i64)
        requires x < i64::MAX
        ensures abstract_relation(x as int, y as int)
    {
        x + 1
    }
}
```

| Mode | Purpose | Runtime presence |
|---|---|---|
| `spec fn` | Pure mathematical definitions and relations | Erased |
| `proof fn` | Lemmas and proof steps | Erased |
| `exec fn` | Executable Rust with checked contracts | Retained |

`pub` controls Rust visibility. In `pub open spec fn`, `open` controls logical
transparency—whether the body is available for unfolding—not module
visibility. A `recommends` clause records the intended well-formed domain of a
spec function, but should not be treated as an executable precondition or as
a universal substitute for a proved `requires` clause.

### Logical and concrete values

The naming convention makes refinement visible:

- `LState`, `LMessage`, and `LAction` are logical objects and relations.
- `CState`, `CMessage`, and `CAction` are executable counterparts.
- `s` and `s_` are conventional pre-state and post-state names.

For non-primitive values, Verus's `View` trait maps a concrete value to its
logical meaning. The expression `value@` invokes that view. A generated view
for a set-backed field, for example, can map an executable `HashSet<u64>` to a
logical `Set<int>`:

```rust
impl View for CConstants {
    type V = LConstants;

    open spec fn view(&self) -> LConstants {
        LConstants {
            rm: self.rm@.map(|x: u64| x as int),
        }
    }
}
```

Generated types also commonly expose a `valid()` or `well_formed()` predicate.
It states representation conditions needed by generated code. It is not the
same thing as a protocol safety invariant: a state can be representable while
violating the protocol's safety property.

### The contract is the bridge

For a functional calling convention, a generated action has the conceptual
shape:

```rust
pub exec fn CAction(s: &CState, c: &CConstants) -> (result: CState)
    requires s.valid(), c.valid()
    ensures result.valid(), LAction(s@, result@, c@)
```

For an in-place convention, the same bridge uses `old(self)@` and `self@`:

```rust
pub exec fn CAction(&mut self, c: &CConstants)
    requires old(self).valid(), c.valid()
    ensures self.valid(), LAction(old(self)@, self@, c@)
```

The first says “the returned state implements the relation”; the second says
“the mutation from old to new `self` implements the relation.” Both are local
step contracts. A separate refinement proof may connect a protocol state to a
higher-level service state, and runtime integration must connect returned
messages to actual I/O.

### Mathematical domains versus executable representations

Logical `int` is unbounded. Logical `Set<T>` and `Map<K,V>` can describe
mathematical domains that are not backed by finite storage. Executable `i64`,
`u64`, `Vec`, `HashSet`, and `HashMap` are finite machine representations.
Bridging them requires choices and obligations:

- arithmetic needs range or overflow preconditions;
- indexing needs bounds;
- iteration needs a finite executable collection;
- a view must describe how concrete keys and values abstract to logical ones;
- model checking needs explicit finite domains even when a spec quantifier is
  mathematically unbounded.

Do not “fix” this mismatch by asserting that all Verus sets are finite. Instead
state finiteness where an operation—cardinality, iteration, extraction, or
bounded exploration—actually needs it.

### Proof and bounded exploration answer different questions

A Verus proof is symbolic and applies to every value satisfying its
preconditions, but only proves the stated contract and relies on its trusted
dependencies. A model checker executes a resolved finite domain and is very
good at producing concrete counterexamples, but its non-violation result is
bounded by domains, depth, state limits, reductions, timeout, and stop reason.

A productive workflow uses both: model check small instances to catch shallow
specification mistakes, then prove the general invariants and refinement
relations that matter. Chapter 8 covers the model checker; Chapters 4–7 cover
the spec-to-proof path.

## Chapter 4 — Write a TLA-Style Specification in Verus

Write the logical state machine before thinking about generated Rust. A good
specification should make its state, frames, guards, and observable outputs
obvious to a human reviewer. The maintained Two-Phase Commit protocol is a
compact example; its logical source lives in
[`src/protocol/TwoPhase/`](../src/protocol/TwoPhase/).

### Define logical types and constants

Logical state is ordinary Verus data inside `verus!`:

```rust
pub enum LTPCMessage {
    Prepare,
    PreparedVote { rm: int },
    Commit,
    Abort,
}

pub enum LTMState {
    Init,
    Committed,
    Aborted,
}

pub struct LState {
    pub tm_state: LTMState,
    pub tm_prepared: Set<int>,
    pub rm_prepared: Set<int>,
    pub rm_committed: Set<int>,
    pub rm_aborted: Set<int>,
}

pub struct LConstants {
    pub rm: Set<int>,
}
```

State fields can change from one step to the next. Constants describe a fixed
instance—in this case, the set of resource-manager identifiers. Splitting the
two prevents a transition from silently changing configuration.

### Select the initial states

An initialization predicate constrains an output state rather than mutating
an allocated object:

```rust
pub open spec fn LInit(s: LState, c: LConstants) -> bool {
    &&& s.tm_state is Init
    &&& s.tm_prepared == Set::<int>::empty()
    &&& s.rm_prepared == Set::<int>::empty()
    &&& s.rm_committed == Set::<int>::empty()
    &&& s.rm_aborted == Set::<int>::empty()
}
```

`c` is part of the uniform protocol signature even though this initialization
does not need to inspect it. The predicate denotes every state satisfying all
five conjuncts.

### Write one named action at a time

An action relates a pre-state `s`, a post-state `s_`, constants, explicit
inputs, and observable outputs. The resource-manager prepare action is:

```rust
pub open spec fn LRMReceivePrepare(
    s: LState,
    s_: LState,
    c: LConstants,
    rm: int,
    sent_packets: Seq<LTPCMessage>,
) -> bool {
    &&& c.rm.contains(rm)
    &&& !s.rm_prepared.contains(rm)
    &&& !s.rm_aborted.contains(rm)
    &&& s_.tm_state == s.tm_state
    &&& s_.tm_prepared == s.tm_prepared
    &&& s_.rm_prepared == s.rm_prepared.insert(rm)
    &&& s_.rm_committed == s.rm_committed
    &&& s_.rm_aborted == s.rm_aborted
    &&& sent_packets == seq![LTPCMessage::PreparedVote { rm }]
}
```

The first three conjuncts are guards. The remaining conjuncts completely
describe the post-state and output. Explicit equalities for unchanged fields
are the relational equivalent of TLA+'s `UNCHANGED`; they also make accidental
state changes visible in review.

There are two useful guard styles, with different semantics:

1. A **pure guarded action**, as above, is false when the guard is false. A
   scheduler must call its executable implementation only when the generated
   preconditions hold.
2. A **guard/transition/else-stutter action** uses `if guard { ... } else {
   s_ == s }`. It is enabled for every input and explicitly does nothing when
   the guard fails.

Choose deliberately. Adding an else-stutter branch changes the transition
relation; it is not just formatting.

### Compose actions into `Next`

`LNext` says that one named action accounts for each step. Outputs or choices
that are internal to the transition are existentially quantified:

```rust
pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
    ||| (exists |sent_packets: Seq<LTPCMessage>|
        LTMSendPrepare(s, s_, c, sent_packets))
    ||| (exists |rm: int, sent_packets: Seq<LTPCMessage>|
        LRMReceivePrepare(s, s_, c, rm, sent_packets))
    ||| (exists |rm: int, sent_packets: Seq<LTPCMessage>|
        LRMAbort(s, s_, c, rm, sent_packets))
    // ...the remaining named actions...
}
```

This is useful for proof and model checking even when `LNext` itself is not
turned into one executable function. In TwoPhase, the atomic actions are
generated and the host scheduler dispatches them; `LNext` remains logical.

### Core expression vocabulary

The table below covers the stable Verus forms used throughout the current
protocol sources. It is not a claim that every expression can be synthesized
as executable code.

| Intent | Verus specification form |
|---|---|
| Conjunction | `a && b`, or bulleted `&&& a` / `&&& b` |
| Disjunction | `a || b`, or bulleted `||| a` / `||| b` |
| Negation | `!p` |
| Implication | `p ==> q` |
| Equivalence | `p <==> q` |
| Equality relation | `x == y` |
| Conditional expression | `if p { a } else { b }` |
| Universal quantifier | `forall |x: T| P(x)` |
| Existential quantifier | `exists |x: T| P(x)` |
| Empty sequence / singleton | `Seq::<T>::empty()`, `seq![x]` |
| Sequence length / index / update | `s.len()`, `s[i]`, `s.update(i, x)` |
| Empty set / membership / insert | `Set::<T>::empty()`, `s.contains(x)`, `s.insert(x)` |
| Empty map / domain / lookup / insert | `Map::<K,V>::empty()`, `m.dom()`, `m[k]`, `m.insert(k, v)` |
| Enum test / field projection | `msg is Variant`, `msg->field` |

Use `==` to state equality. A lone `=` is assignment syntax and is not a
state relation.

### Quantifiers, domains, and triggers

Logical quantifiers need not be finite merely because an executable model will
be finite. Bound them when the property actually ranges over a collection or
index interval:

```rust
forall |i: int| 0 <= i < entries.len() ==> entries[i].valid()
```

When a proof needs set or map cardinality, establish that the relevant domain
is finite; Verus specification sets are not finite by default. In model
checking, Chapter 8 explains how `model.toml` supplies finite domains for
quantified types.

Verus uses trigger terms to decide how universally quantified facts are
instantiated. Start with natural expressions that mention the bound variable.
If arithmetic inside a trigger is unstable, introduce a second variable that
names the computed index:

```rust
forall |i: int, j: int|
    j == i + 1 && 0 <= i < entries.len() ==> P(entries[j])
```

Treat manual triggers as proof-engineering decisions, not decoration. Chapter
20 covers the repository's trigger workflow in depth.

### State invariants and lemmas

An invariant is just a logical state predicate. TwoPhase includes:

```rust
pub open spec fn LSafetyNoCommitAbortOverlap(
    s: LState,
    c: LConstants,
) -> bool {
    forall |rm: int|
        s.rm_committed.contains(rm) ==>
        !s.rm_aborted.contains(rm)
}
```

Defining an invariant does not prove it. A complete deductive argument shows
that initialization establishes it and every `LNext` branch preserves it. A
`proof fn` can package reusable steps; a finite model check can search for
counterexamples in chosen domains.

Keep type/representation predicates separate from semantic invariants. For
example, “every concrete enum has a valid logical view” and “no resource
manager is both committed and aborted” answer different questions.

### Messages, packets, and the environment

TwoPhase models an action's outgoing messages as a `Seq<LTPCMessage>`. Larger
protocols use packets carrying source, destination, and message, plus an
environment that records send, receive, clock, timeout, delivery, and stutter
steps. The reusable definitions live under
[`src/common/framework/`](../src/common/framework/) and RSL's aliases and
protocol-specific environment live under
[`src/protocol/RSL/`](../src/protocol/RSL/).

Keep the logical boundary explicit:

- the protocol decides which abstract packets should be sent;
- the concrete host converts generated values into runtime messages;
- the networking layer performs actual I/O;
- any theorem connecting the abstract packet sequence to real I/O needs an
  explicit contract or trusted boundary.

### Compose components and refinement layers

Large protocols split state into components such as proposer, acceptor,
learner, executor, and election. A composite action invokes the component
relation for the changing field and frames the other fields. This keeps local
proofs small and makes ownership of each transition clear.

An abstraction function then maps a lower-level protocol or concrete state to
a higher-level service state. A refinement relation states that the lower
state represents the abstract state, while a refinement proof shows that
initial states and steps preserve that representation. A generated
`ensures LAction(old(self)@, self@, ...)` is one refinement link, not the whole
system theorem.

### Specification style checklist

- Give every meaningful action a name; keep `LNext` a readable disjunction.
- State all changed and unchanged fields, or construct the entire post-state.
- Decide explicitly whether a failed guard disables an action or stutters.
- Keep external choices as named inputs when executable code must receive
  them.
- Separate abstract messages from runtime serialization.
- Use small pure helpers for repeated logic, with clear termination measures
  for recursion.
- Use `pub open spec fn` when callers need both visibility and transparent
  unfolding; do not use `open` as a synonym for `pub`.
- Write invariants independently of the proof and independently of concrete
  representation validity.

## Chapter 5 — Design a Specification the Transpiler Can Execute

The transpiler is not a general solver for arbitrary relations. It succeeds
when the relation exposes a deterministic construction for each output. The
best time to make that data flow clear is while designing the action, not after
generation fails.

### Inputs and outputs

A `.automan` file assigns a mode to every annotated parameter:

- `+` is an input supplied to the executable function;
- `-` is an output synthesized from the relation.

For the action in Chapter 4, the maintained annotation is:

```text
module TwoPhase::twophase {
    LInit(-, +);
    LRMReceivePrepare(+, -, +, +, -);
}
```

The five modes of `LRMReceivePrepare` correspond, in order, to `s`, `s_`, `c`,
`rm`, and `sent_packets`. Its generated function therefore receives the old
state implicitly as `&mut self`, receives constants and `rm`, mutates the state,
and returns a `Vec` of concrete messages.

Annotation files allow `#`, `//`, and trailing comments. Validate their syntax
with:

```bash
cargo run --manifest-path transpiler/Cargo.toml -- \
  check --annotations src/protocol/TwoPhase/twophase.automan
```

`check` parses the annotation file. Full spec/annotation agreement and output
data-flow checks occur when the transpiler analyzes the actual spec during
generation.

### Value-returning helpers

Not every logical function is a predicate with synthesized parameters. A
value-returning helper uses explicit helper syntax, as in the current Raft
annotation file:

```text
module Raft::raft {
    helper step_down_if_needed(+, +) -> LState;
    helper log_up_to_date(+, +, +) -> bool;
}
```

Helpers still need an executable translation or a configured function path.
The return type is part of the annotation because there is no `-` parameter to
carry it.

### The three mode-analysis obligations

The AutoMan vocabulary is useful for reviewing a relation:

1. **Saturation:** every output is constructed on every relevant path. A
   post-state field omitted from both branches leaves executable Rust with no
   value to return.
2. **Harmony:** the relation does not give one output incompatible
   constructions on the same path. Conjuncts cannot require both
   `s_.term == x` and `s_.term == y` without establishing `x == y`.
3. **Obligation:** an output is not consumed before its construction is known.
   Data dependencies must form an executable order.

These are necessary but not sufficient for verification. Generated arithmetic
may still need bounds, concrete collections may need view lemmas, and called
helpers may need stronger contracts.

### Patterns with direct executable meaning

The current `list-templates` command advertises the core quantifier/structure
templates:

```bash
cargo run --manifest-path transpiler/Cargo.toml -- list-templates
```

It lists sequence, map, and set comprehensions and field-by-field struct
construction. More generally, the maintained protocols demonstrate these
useful shapes:

| Relational shape | Typical generated computation |
|---|---|
| `out == expression(inputs)` | Return the translated expression |
| `s_ == s` | Preserve or clone state, depending on calling convention |
| One equality per post-state field | Construct a new struct or assign fields in place |
| `if guard { construction A } else { construction B }` | Executable `if` with one complete construction per branch |
| `sent == Seq::empty()` / `sent == seq![m]` | `vec![]` / `vec![m]` |
| `set_ == set.insert(x)` | Clone/mutate a `HashSet`, with a view-preservation proof |
| A bounded indexed sequence characterization | A loop with invariants, when the matching template is supported |
| A configured helper call | A function or method call with mapped arguments |

Exact support depends on expression shape, types, and configuration. Use the
runnable examples under
[`transpiler/verus_examples/`](../transpiler/verus_examples/) and current
protocols as evidence; do not infer support from a superficially similar old
documentation snippet.

### Make nondeterministic choices explicit

Suppose a logical action says only:

```rust
pub open spec fn LChoose(s: LState, s_: LState) -> bool {
    s_.owner == 1 || s_.owner == 2
}
```

Both post-states are legal, but no input tells an executable function which one
to produce. If the environment or scheduler makes the choice, expose it:

```rust
pub open spec fn LChoose(
    s: LState,
    s_: LState,
    choice: int,
) -> bool {
    &&& (choice == 1 || choice == 2)
    &&& s_.owner == choice
    &&& s_.other == s.other
}
```

The annotation becomes `LChoose(+, -, +);`. The resulting executable contract
must require or otherwise establish the choice guard. This refactoring does
not arbitrarily resolve nondeterminism; it names who owns it.

Existential witnesses in a top-level `LNext` are often scheduler choices, so
it is normal to leave `LNext` logical while generating its atomic actions.

### Spec-only, skipped, and unsupported functions

Configuration distinguishes several cases:

- `spec_only_functions` names logical helpers that should stay in proof space
  rather than acquire a `C` prefix.
- `skip_functions` prevents generation for functions whose executable body is
  supplied through another maintained source or whose pattern is not yet
  supported.
- `function_paths` and `method_calls` connect a logical call to an existing
  concrete implementation with an appropriate contract.

A skipped function is not automatically implemented or proved. The build must
obtain any needed executable definition from an intentional, reviewed module.

The CLI also exposes `--auto-skip` and `--proof-fallback`. They are diagnostic
tools:

- `--auto-skip` continues after per-function translation failures and reports
  what was omitted.
- `--proof-fallback` emits `#[verifier(external_body)]` stubs and therefore
  introduces trusted bodies.

Neither option is a production proof strategy. Use them to inventory gaps,
then implement the missing general translation/proof support or provide an
explicitly reviewed boundary. Never paste a replacement body into
`src/generated/`.

## Chapter 6 — Configure Code Generation

Mode annotations answer “which values flow in and out?” The TOML configuration
answers “which concrete Rust representation and code-generation policy should
implement that flow?” Start with the smallest configuration that works, then
add a mapping only when the generated interface requires it.

### A minimal configuration

The checked-in counter uses:

```toml
[naming]
spec_prefix = "L"
exec_prefix = "C"
int_type = "i64"
nat_type = "u64"

# Rust's executable i64 is bounded even though Verus's spec int is not.
[extra_requires]
CIncrement = ["*value < i64::MAX"]

[output]
generate_inline_types = false
generate_proofs = true
custom_imports = [
    "use vstd::prelude::*;",
    "use crate::counter_spec::*;",
]
```

This file makes four decisions:

1. logical names beginning with `L` become executable names beginning with
   `C`;
2. mathematical `int` and `nat` use `i64` and `u64` in executable code;
3. increment is legal only below the machine maximum; and
4. generated proof code and the required imports are emitted.

`[output] generate_proofs` defaults to `false`. With proof generation disabled,
some translation paths can emit assumption placeholders rather than proof
blocks. Consequently, output from the default is not proof evidence until it
has been audited. Proof-producing configurations in this repository set
`generate_proofs = true`, keep `assume_postconditions = false`, run Verus, and
separately audit trusted sites. `generate_proofs = true` asks the transpiler to
construct proofs; it does not guarantee that every generated function will
verify.

### TOML scope matters

Options such as `skip_functions`, `mut_self_types`, and `primitive_types` are
root keys. Put root keys before the first table header. Once TOML enters
`[naming]`, `[output]`, or another table, following keys belong to that table
until the next table header; TOML has no “return to root” header.

For example:

```toml
# root options first
skip_functions = ["LNext"]
mut_self_types = ["CState"]

[naming]
spec_prefix = "L"
exec_prefix = "C"
int_type = "u64"
nat_type = "u64"

[output]
generate_proofs = true
validity_predicate_name = "valid"
custom_imports = [
    "use vstd::prelude::*;",
    "use crate::protocol::Example::example::*;",
]
```

`custom_imports` belongs inside `[output]`, not at the root.

### Naming and representation

`[naming]` supplies default prefixes and numeric types:

```toml
[naming]
spec_prefix = "L"
exec_prefix = "C"
int_type = "u64"
nat_type = "u64"
```

Mapping a logical `int` to `u64` is a representation choice, not a theorem
that every logical integer is non-negative or in range. The generated
function needs preconditions that justify casts and arithmetic. Add
function-specific bounds through `[extra_requires]` only when they accurately
express the executable domain:

```toml
[extra_requires]
"CAdvance" = [
    "*index < u64::MAX",
    "*index as int < s@.entries.len()",
]
```

Prefer a logical `nat` when non-negativity is intrinsic to the model. Still
account for the finite upper bound of its executable type.

### Remap names and calls only when defaults are insufficient

The configuration supports several distinct kinds of mapping:

```toml
[remapping]
"RslPacket" = "CPacket"
"Ballot" = "CBallot"

[variant_remapping]
"IncompleteBatchTimerOff" = "CIncompleteBatchTimer::CIncompleteBatchTimerOff"

[function_paths]
"BroadcastToEveryone" = "crate::generated::RSL::broadcast_gen::CBroadcastToEveryone"

[method_calls]
"LMinQuorumSize" = { method_name = "CMinQuorumSize", receiver_arg_index = 0 }
```

- `remapping` overrides logical-type to concrete-type naming.
- `variant_remapping` supplies a fully qualified concrete enum variant.
- `function_paths` resolves a concrete helper in another module.
- `method_calls` changes a logical free-function call into a method call. Its
  current fields are `method_name`, `receiver_arg_index`, and optional
  `destructure_index`.

Views need two different mechanisms. A generated type field can override its
view using a `LogicalType.field` key:

```toml
[view_overrides]
"LAcceptor.votes" = "abstractify_cvotes(&self.votes)"
```

A function parameter or return type can use a template containing `{param}`:

```toml
[type_view_exprs]
"RequestBatch" = "abstractify_crequestbatch({param})"
```

These expressions become Verus code. Treat them as part of the proof surface,
not as stringly typed convenience aliases.

### Validity, imports, and proof options

Important `[output]` options include:

```toml
[output]
generate_abstraction_fns = true
generate_validity_predicates = true
validity_predicate_name = "valid"
generate_clone = true
generate_loops_for_verification = true
generate_inline_types = false
generate_proofs = true
assume_postconditions = false
custom_imports = [
    "use vstd::prelude::*;",
]
```

Generated validity predicates describe concrete representation constraints.
Generated abstraction functions implement `View`. Loop generation is useful
when iterator code would not expose the invariants Verus needs. Inline type
generation is convenient for self-contained inputs; the maintained protocols
usually generate their `types_gen.rs` separately.

Avoid `manual_code` as a workaround for failed generation. Some legacy
repository modules still carry explicit manual-source inputs, but the project
policy is to fix proof/code generation and regenerate, not accumulate pasted
bodies in derived files.

### Collections and cloning

Executable collections need more information than logical `Seq`, `Set`, and
`Map`. The root configuration includes options such as:

- `collection_fields`, `set_fields`, and `vec_fields` to classify fields;
- `struct_vec_fields` and `map_fields` to describe element/value abstraction;
- `clone_strategy` and `clone_up_to_view_types` to select proof-compatible
  clones;
- `verified_clone_fns` to name an existing verified collection clone; and
- `vec_element_ensures` to require validity or abstraction predicates for each
  returned element.

Do not add a field to every list “just in case.” Use the generated error and a
nearby maintained config with the same concrete representation as evidence.

### Functional versus in-place output

The default conceptual form returns a new state:

```rust
fn CAction(s: &CState, ...) -> (CState, Vec<CMessage>)
```

Listing an executable state type in `mut_self_types` requests an in-place
method:

```toml
mut_self_types = ["CState"]
```

```rust
fn CAction(&mut self, ...) -> Vec<CMessage>
```

The in-place form avoids rebuilding the outer state and uses
`old(self)@`/`self@` in its contract. It works when the relation describes
field updates that can be assigned in a safe order. Raft remains functional
because several handlers compute an intermediate whole state and then reason
from that value; the current `&mut self` transform cannot generally lift that
pattern into a mutation.

For functional code that must repeatedly rebuild large states,
`arc_wrap_types` or `arc_wrap_fields` can make selected unchanged clones
shallow. Arc wrapping conflicts with `mut_self_types`: the transpiler clears
both Arc options and emits a warning when in-place generation is active. New
configs should choose one ownership strategy rather than knowingly request
both.

### Inspect the resolved configuration

The transpiler infers additional information from the spec and its sibling
`types.rs`, then merges TOML overrides. Print the result without generating:

```bash
cargo run --manifest-path transpiler/Cargo.toml -- \
  -i examples/quickstart/counter_spec.rs \
  -a examples/quickstart/counter_spec.automan \
  -c examples/quickstart/counter_transpile.toml \
  --dump-config
```

Use this when a mapping appears to be ignored, a default surprises you, or a
field was auto-classified. The complete schema belongs in Appendix C; the
authoritative definitions are in
[`transpiler/src/config.rs`](../transpiler/src/config.rs), and current protocol
configs are the best worked examples.

## Chapter 7 — Generate, Inspect, and Verify Executable Code

Generation is a reproducible build step, not an editing technique. Keep the
hand-written inputs under review, regenerate the outputs, inspect their
contracts and trust surface, and then run Verus.

### Know the inputs and outputs

For a single-module protocol such as Raft:

| Artifact | Example | Ownership |
|---|---|---|
| Logical types | `src/protocol/Raft/types.rs` | Hand-written |
| Logical actions | `src/protocol/Raft/raft.rs` | Hand-written |
| Mode annotations | `src/protocol/Raft/raft.automan` | Hand-written |
| Configuration | `src/protocol/Raft/raft_transpile.toml` | Hand-written |
| Concrete types | `src/generated/Raft/types_gen.rs` | Generated only |
| Executable actions | `src/generated/Raft/raft_gen.rs` | Generated only |
| Runtime messages and host | `src/implementation/Raft/` | Explicit generated or hand-written support, according to file header/workflow |

RSL is multi-module and has separate annotation/config pairs for acceptor,
learner, proposer, executor, election, replica, and broadcast. Do not flatten
those module boundaries into one guessed command.

### Build the transpiler

```bash
cargo build --release --manifest-path transpiler/Cargo.toml
TLA_RS_TRANSPILER="$PWD/transpiler/target/release/verus-transpile"
```

The resulting CLI supports both a `generate-types` subcommand and the default
spec-to-exec mode.

### Reproduce a protocol in a scratch directory

Before overwriting checked-in output, reproduce Raft into a scratch directory:

```bash
mkdir -p /tmp/tla-rs-raft-generated

"$TLA_RS_TRANSPILER" generate-types \
  -i src/protocol/Raft/types.rs \
  -c src/protocol/Raft/raft_transpile.toml \
  -o /tmp/tla-rs-raft-generated/types_gen.rs

"$TLA_RS_TRANSPILER" \
  -i src/protocol/Raft/raft.rs \
  -a src/protocol/Raft/raft.automan \
  -c src/protocol/Raft/raft_transpile.toml \
  -o /tmp/tla-rs-raft-generated/raft_gen.rs

cmp /tmp/tla-rs-raft-generated/types_gen.rs \
    src/generated/Raft/types_gen.rs
cmp /tmp/tla-rs-raft-generated/raft_gen.rs \
    src/generated/Raft/raft_gen.rs
```

No output from `cmp` means the files are byte-identical. A difference can be
legitimate after changing a source, but it must be explained by that source
change.

To intentionally regenerate the checked-in files, use the same commands with
the `src/generated/Raft/` output paths, then inspect the diff:

```bash
git diff -- src/generated/Raft
```

The convenience command `./scripts/regenerate_all.sh Raft` also generates
Raft types, functions, and runtime messages. Use it only when all of those
outputs are in scope. For RSL, prefer its explicit per-module generation
workflow and current parity tests; do not follow historical instructions that
ask for manual patches after generation.

### Inspect the generated interface

Start with signatures and contracts, not the implementation details:

```rust
pub exec fn CInit(c: &CConstants) -> (result: CState)
requires
    c.valid(),
ensures
    result.valid(),
    LInit(result@, c@),
```

```rust
pub exec fn CRMReceivePrepare(
    &mut self,
    c: &CConstants,
    rm: &u64,
) -> (result: Vec<CTPCMessage>)
requires
    old(self).valid(),
    c.valid(),
    c@.rm.contains(*rm as int),
    !old(self)@.rm_prepared.contains(*rm as int),
    !old(self)@.rm_aborted.contains(*rm as int),
ensures
    self.valid(),
    LRMReceivePrepare(
        old(self)@,
        self@,
        c@,
        *rm as int,
        result@.map(|i, p: CTPCMessage| p@),
    ),
```

Check four things:

1. concrete inputs have the intended borrow/mutation convention;
2. every necessary representational and guard precondition appears;
3. the output validity condition is appropriate; and
4. the final `ensures` names the intended logical action with the correct old
   and new views.

Generated proof blocks may call collection lemmas or establish mapped-view
equalities. Their presence does not replace running Verus.

### Focused verification

Use the pinned Verus binary to verify a generated module and its concrete
types:

```bash
"$VERUS_PATH" --crate-type=lib src/lib.rs \
  --verify-only-module generated::Raft::raft_gen \
  --verify-only-module generated::Raft::types_gen
```

A focused pass is fast feedback, not the final integration gate. The whole
crate contains protocol proofs, shared infrastructure, generated modules,
implementations, and service entry points. Run:

```bash
scons --verus-path="$VERUS_PATH" --skip-dotnet
```

SCons invokes Verus with `src/lib.rs` as the crate root and builds
`liblib.so`; it fails if verification or compilation fails. Use
`--verus-extra-args="--time-expanded"` when collecting the timing format used
by CI. `--no-verify` deliberately skips proof checking and must never be
reported as a verification pass.

### Check deterministic regeneration

The repository includes a single-threaded regeneration parity test:

```bash
cargo test --manifest-path transpiler/Cargo.toml --release \
  regen_matches_checked_in -- --test-threads=1
```

Single-threading matters because these tests spawn Cargo commands that can
contend for the build lock. Also run the general transpiler suite when changing
generation behavior:

```bash
cargo test --manifest-path transpiler/Cargo.toml --all-features
```

### Audit assumptions and unchecked bodies

For generated RSL files, the CLI can emit a structured syntactic inventory of
`assume(...)` sites:

```bash
"$TLA_RS_TRANSPILER" report-assumes \
  --input-dir src/generated/RSL \
  --output /tmp/rsl-generated-assumes.json
```

That report is not a complete trust audit. Search the relevant scope for other
boundaries as well:

```bash
rg -n 'assume\s*\(|external_body|assume_specification|verifier\(external\)' \
  src/generated src/protocol src/implementation src/lib.rs
```

Classify each hit: comments are not assumptions; an `external_body` is a
trusted body; an external specification is an interface assumption; and FFI
entry points cross into runtime code. Do not use the raw number of hits as a
correctness score.

### When generation fails

Respond at the owning layer:

| Failure | Correct place to act |
|---|---|
| Annotation arity or mode error | `.automan` file or spec signature |
| Output not fully constructible | Refactor the logical action's data flow |
| Wrong concrete name or call | `_transpile.toml` mapping |
| Missing general expression/pattern support | Transpiler parser/translator/code generator plus tests |
| Missing proof lemma or invariant | Proof generation or a reviewed hand-written proof module |
| Runtime message/scheduler mismatch | `src/implementation/<P>/` and service integration |
| Wrong generated Rust | Fix one of the above, then regenerate |

Never make the last row mean “edit `src/generated/` until it compiles.”

## Chapter 8 — Model Check a Specification

Model checking is the fastest way to turn a small protocol model into either a concrete
counterexample or carefully bounded evidence. tla-rs can explore the `LInit`/`LNext` relations
in a Verus protocol source file directly; it does not first translate them to TLA+ or invoke
TLC. This source-first path is useful early, when a counterexample is cheaper to understand
than a failed proof, and later as a regression gate beside deductive verification.

The word “check” needs a boundary. A successful run says something about the finite domains,
collection bounds, transition semantics, search horizon, reductions, and properties selected
for that run. It is not an unbounded Verus proof. Conversely, a counterexample is often useful
even when the run is lossy or incomplete: it is a concrete execution to inspect, provided the
evaluator faithfully supports the expressions involved.

### Build the checker and identify its three inputs

Build the current CLI from the repository root:

```bash
cargo build --manifest-path transpiler/Cargo.toml --bin verus-transpile
```

A source-first run has three logical inputs:

1. the protocol file containing the transition relation;
2. the corresponding type file; and
3. a `model.toml` that makes every otherwise unbounded choice finite.

The default entrypoints are `LInit` and `LNext`. The checker expects the usual relational
shapes `LInit(s, c)` and `LNext(s, s_, c)`. If `--types` is omitted, it looks for `types.rs`
beside the protocol file. A minimal invocation is:

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/TwoPhase/twophase.rs \
  --types src/protocol/TwoPhase/types.rs \
  --model transpiler/tests/model_check_fixtures/twophase_small.model.toml \
  --search bfs \
  --json-report
```

Use `--init` or `--next` when the source uses different names. `--invariant` is repeatable; if
present, it replaces rather than extends `properties.invariants` in `model.toml`.

### Make the model finite deliberately

The checker can only enumerate concrete runtime values. A small starting model might be:

```toml
[constants.assignments]
limit = 2

[quantifiers.int]
min = 0
max = 2

[quantifiers.nat]
max = 2

[quantifiers.types.LRole]
kind = "enum_subset"
variants = ["Follower", "Leader"]

[collections]
max_seq_len = 2
max_set_len = 2
max_map_len = 2

[search]
max_depth = 8
max_states = 10000
timeout_ms = 30000
candidate_eval_guardrail = 10000

[properties]
invariants = ["LTypeOK", "LSafety"]
check_deadlock = false
successor_semantics = "deadlock"
```

`[constants.assignments]` pins fields of `LConstants`. A field not pinned there can be filtered
through `[constants.domains.<field>]`. The checker explores every resolved constants valuation,
not just the first. Do not put the same field in both tables; validation rejects that ambiguous
configuration.

`[quantifiers.int]` and `[quantifiers.nat]` supply fallback finite domains for those primitive
types. `[quantifiers.types.<Type>]` supplies a domain for a named type. Domain specifications
have one of four tagged forms:

```toml
[quantifiers.types.NodeId]
kind = "values"
values = [0, 1]

[constants.domains.epoch]
kind = "int_range"
min = 0
max = 2

[constants.domains.round]
kind = "nat_range"
max = 2

[quantifiers.types.LMessage]
kind = "enum_subset"
variants = ["Request", "Reply"]
```

Values in TOML are booleans, signed integers, or strings. For a structured constant domain,
current fixtures sometimes use a string equal to the runtime value's canonical key, for
example `"set:{int:0}"`; copy that syntax only after inspecting an existing fixture and the
resolved output. Structs, enums, tuples, references, and the built-in `Seq`, `Set`, and `Map`
containers are expanded recursively. Their cross-products can grow much faster than the search
frontier, so collection bounds are semantic inputs, not merely performance settings.

Before a long run, print the resolved and validated configuration:

```bash
transpiler/target/debug/verus-transpile model-config \
  --model path/to/model.toml \
  --max-depth 4 \
  --max-states 2000 \
  --int-range=-1..2 \
  --nat-max 2
```

`model-config` also accepts overrides for timeout, collection lengths, and the candidate
evaluation guardrail. It is the simplest way to catch a misspelled enum mode, an empty domain,
a zero limit, or an invalid property combination before exploration begins.

### Choose BFS, DFS, or DPOR

The search strategy is selected on the command line, not in `model.toml`.

| Strategy | Best use | Current behavior |
|---|---|---|
| `bfs` | Shortest-depth safety witnesses, ordinary regression evidence, liveness graph construction | Sequential by default; `--workers N` enables level-synchronous parallel BFS. |
| `dfs` | Low-memory bug hunting along deep paths | Sequential; `--workers` does not make DFS parallel. |
| `dpor` | Reducing redundant interleavings in concurrent models | Integrated sleep-set/independence explorer; `--workers N` enables its parallel frontier/work-stealing path. Treat its current reporting path as experimental, as described below. |

BFS and DFS globally deduplicate reached states. They differ in frontier order, so BFS usually
finds the shallowest violation while DFS may reach a deep one sooner. Neither order changes the
finite model being requested.

DPOR groups actions by process and uses read/write footprints to decide when cross-process
steps are independent. Same-process transitions, unknown footprints, and conflicting reads or
writes remain dependent. Keyed paths such as `pc[0]` and `pc[1]` can be independent, while a
whole-field path such as `pc` conflicts with every keyed path below it. Sleep sets and
backtracking then avoid exploring interleavings intended to be equivalent. With
`--conflict-profile`, the checker reports the field pairs most often preventing an independence
decision; this option has no meaning for BFS or DFS.

There are important limitations in the current main-path DPOR adapter. It retains canonical
state-key strings rather than the `ExploredState` values used by the ordinary report path. The
adapter therefore emits no ordinary explored-state payload, does not propagate detailed
invariant/deadlock witnesses, and currently maps every non-violation termination to
`FrontierExhausted`. It also does not apply `timeout_ms`, and parity/liveness consumers do not
receive a useful graph from it. In addition, its state store uses a 64-bit fingerprint fast
path. For now:

- use BFS or DFS for authoritative stop-reason reporting and detailed witnesses;
- use BFS for bounded liveness and cross-engine state export;
- treat DPOR as bounded safety-oriented reduction and bug finding;
- compare DPOR with a small canonical BFS model before relying on a reduction change; and
- do not infer that a DPOR run is exact merely because its JSON `evidence_mode` says so.

Those restrictions describe the current integration, not the intended endpoint of DPOR.

### Select properties and transition semantics

Safety invariants are boolean spec functions named in `properties.invariants` or with repeated
`--invariant` options. Each is resolved before exploration and evaluated on every reached state.
An unknown or duplicate name is an error rather than a silently skipped property.

Deadlock behavior is controlled by two separate settings:

```toml
[properties]
check_deadlock = true
successor_semantics = "deadlock"
```

Under `deadlock` semantics, a state with no enabled `LNext` branch has no successor. If
`check_deadlock` is true, reaching such a state below the depth cutoff stops the run with a
deadlock witness. Under `stuttering` semantics, the solver inserts `s_ == s` when no branch is
enabled. Stuttering therefore removes deadlocks, and the configuration validator rejects
`check_deadlock = true` with `successor_semantics = "stuttering"`.

The invisible-branch POR heuristic is configured separately:

```toml
[search]
por_heuristic = "invisible_branch"
```

It prunes branches whose writes are syntactically invisible to other branches and selected
invariants. Because even an invisible transition can matter to deadlock, the validator rejects
this heuristic when deadlock checking is enabled. Keep it at `"none"` when establishing a
baseline.

### Check bounded liveness and fairness

Liveness obligations name two boolean state predicates:

```toml
[properties]
leads_to = [
  { name = "request_eventually_done", from = "LRequestPending", to = "LDone" },
]
fairness = { weak = ["branch_send"], strong = ["branch_retry"] }
```

The checker builds the reached transition graph, finds cyclic strongly connected components,
and looks for a fair cycle containing a `from` state but no `to` state. Predicate signatures
must be `(state[, constants]) -> bool`. Fairness names are `LNext` branch labels, not function
names guessed by the reader; preflight validation rejects labels not present in the analyzed
transition relation and rejects duplicates across weak and strong lists.

Fairness filtering is branch-label based. Weak fairness removes a candidate component when a
named branch is enabled at every state in the component but never appears on an internal edge.
Strong fairness does the analogous check when the branch is enabled at any state in the
component. This is a useful bounded diagnostic, not a complete temporal proof procedure.

Liveness is evaluated only when the ordinary explorer reports `FrontierExhausted`. There is a
subtle but important qualification: the explorer also reports `FrontierExhausted` after it has
stopped expanding states at `max_depth`. If `summary.depth` reaches `search.max_depth`, the
graph may be depth-truncated even though the worklist is empty. Interpret a liveness result as
bounded by that horizon, and increase the depth until the reached graph stabilizes. Do not use
the current DPOR adapter for liveness evidence.

### Read results on four independent axes

No single word such as “exact” captures a run. Read every positive result on four axes:

| Axis | Question |
|---|---|
| Finite model | Which constants, primitive domains, enum variants, and collection lengths existed? |
| Search completion | Did the run stop on a violation, state cap, timeout, or an emptied worklist? Did it reach the depth cutoff? |
| State identity | Were canonical keys retained, or could hash compaction/symmetry merge states? |
| Transition reduction | Were all branches explored, or was POR/DPOR used under an independence argument? |

The normal `result` values are `ok`, `max_states_reached`, `timeout_reached`,
`invariant_violated`, and `deadlock_detected`; a liveness witness changes the result to
`leads_to_violated`. `stop_reason` gives the corresponding internal reason such as
`FrontierExhausted`, `MaxStatesReached`, or `TimeoutReached`. The command currently returns a
successful process status after emitting a model-check result, including a property violation,
so CI must inspect the JSON result rather than treating exit code zero as “properties held.”

The JSON report also contains an `evidence_mode`:

- canonical deduplication with no symmetry fields is labeled
  `exact_proof_strength`;
- `state_dedup = "hash_compaction64"` is labeled
  `lossy_bug_finding_accelerator` because collisions can merge states;
- any nonempty `symmetry_fields` is labeled lossy because identities are intentionally
  normalized together.

That classifier is narrow: it examines state deduplication and symmetry only. It does not turn
a finite run into an unbounded proof, prove that a configured symmetry is sound, account for
reaching `max_depth`, or certify POR/DPOR. In the current implementation it also does not account
for DPOR's internal fingerprint store. Read `proof_strength: true` as “the selected ordinary
dedup settings preserve explored-state distinctions,” not “the protocol is proved.”

A practical confidence ladder is:

1. A reproduced counterexample is a concrete bounded bug witness.
2. A lossy or incomplete run with no witness is only a bug-finding attempt.
3. A canonical BFS/DFS run that reaches a cap is incomplete bounded evidence.
4. A canonical BFS/DFS run whose graph closes below the depth cutoff is exhaustive for the
   configured finite model and supported semantics.
5. A Verus proof establishes its stated theorem under its assumptions and trusted boundary; it
   is a different kind of evidence.

### Tune execution without changing the model accidentally

The bytecode evaluator is enabled by default. Expressions it cannot compile fall back to the
AST interpreter. `--no-bytecode` forces the interpreter and is useful when debugging a dispatch
difference.

`--native-codegen` adds an opt-in native path that compiles supported expressions into dynamic
libraries with `rustc`. Dispatch is native, then bytecode, then AST fallback. Native generation
adds startup cost and requires the transpiler runtime library to be buildable, so record both
the flag and the toolchain when publishing performance numbers.

`--workers N` changes only the implementation of BFS or DPOR, not DFS. Parallel BFS does not
use the same cooperative solver-timeout hook as the sequential path, so compare stop reasons
and state counts rather than assuming timing parity. Performance flags should never be smuggled
into a semantic comparison: hold the model, properties, reductions, and search strategy fixed.

The branch telemetry in a JSON report explains where time and combinatorics went. A branch with
`fallback_reason = "direct"` exposed usable next-state equalities. A branch with
`no_next_state_assignment` or `not_all_fields_assigned` required candidate enumeration. Inspect
`candidate_state_count`, `enumeration_candidate_evaluations`, guard-pruned counts, evaluator
calls, and cache hits before merely raising `candidate_eval_guardrail`.

### Read the JSON report and preserve evidence

The top-level report records the protocol and types paths, resolved entrypoints, configured and
resolved invariants, search settings, summary, liveness summary, stop reason, and optional
violation payloads. For an invariant or deadlock it currently reports the failing canonical
state key and depth. A leads-to violation contains a representative cycle edge plus an
action-labeled prefix/cycle witness with coarse state diffs.

Checked-in examples live under [`reports/model_check/`](../reports/model_check/README.md). To
refresh the supported matrix:

```bash
./scripts/run_model_check_matrix.sh
./scripts/check_model_check_drift.py
```

The drift guard removes wall-clock fields and the manifest's Git revision, then compares all
other generated content exactly. `timeout_ms` is deliberately retained because it is a model
input, not timing noise. Review semantic changes—state counts, transitions, paths, stop reasons,
telemetry fields—before committing regenerated artifacts.

### Cross-check with TLC when the engines should agree

Source-first checking is normally the direct path. Generate a TLC wrapper when an independent
engine, an existing TLC workflow, or historical parity is valuable:

```bash
transpiler/target/debug/verus-transpile generate-mc-wrapper \
  --input out/Protocol.tla \
  --output out/Protocol_MC.tla \
  --invariant Safety
```

The input must expose relational `Init(s, c)` and `Next(s, s_, c)`. The command writes a wrapper
and a `.cfg` skeleton; it does not run TLC. Packet projection can be `none`, `append-seq`, or
`replace-seq`, with `--packet-var` naming the relational packet output. These modes change the
wrapper model and must match the source-first state projection being compared.

For current source-first exports, use `--export-parity DIR`. It writes `states.jsonl`. Despite
older prose and the CLI description referring to states and edges, the ordinary export path
currently writes no edge file. `--export-parity-debug DIR` writes streaming
`generated_states.jsonl`, `distinct_states.jsonl`, and `edges.jsonl` for ordinary BFS/DFS
exploration. Compare state payloads, not engine-specific `id` strings:

```bash
python3 scripts/diff_parity_states.py \
  reports/model_check/parity/source_first/protocol/states.jsonl \
  reports/model_check/parity/tlc/protocol/states.jsonl \
  --left-label source-first --right-label TLC
```

Constants and wrapper bookkeeping such as a lifted message channel may need to be projected
out. Sequence indices, enum encodings, sets, maps, and record field ordering must be normalized
consistently. A state-set match still does not prove transition-graph or behavior equivalence;
an action can disappear while leaving the same reachable states.

### Troubleshooting

When the model explodes, reduce numeric domains first, then named-type domains, collection
lengths, and unpinned constants. Start at a small depth and grow one dimension at a time. An
error about candidate expansion is often raised before the search begins; raising
`max_states` may permit that cross-product, but narrowing the model is usually more informative.

When evaluation reports an unsupported construct, simplify the relevant spec helper to the
documented subset or add evaluator support with tests. Currently useful forms include boolean
logic, equality/comparison, integer arithmetic, `if`, identifier `let` bindings, structs/enums,
field access, indexing, sequence/set/map literals, selected collection methods, finite
`forall`/`exists`, `match`, and struct updates. Bitwise/shift operators, arbitrary casts,
non-identifier patterns, and unresolved or recursive helper shapes remain common boundaries.

When constants resolution reports zero valuations, inspect the resolved domains and verify that
assignments use the runtime type expected by `LConstants`. When a fairness label is unknown,
inspect the analyzed `LNext` branch labels rather than renaming the property blindly. When a
positive result matters, rerun with canonical BFS, no symmetry, no POR, and a larger depth before
making a stronger claim.

The practical command reference and current limitations are maintained in
[`model-checking-source-first.md`](model-checking-source-first.md); the full configuration and
report schema appears in Appendix E.

## Chapter 9 — Import and Export TLA+

tla-rs has several TLA+-related paths, but they solve different problems. Choose one maintained
source of truth, generate the other representation, and attach only the evidence the chosen
path actually produces. A parser success is not a translation guarantee, a translated spec is
not a proof, an executable body generated with assumptions is not verified, and a finite
state-set comparison is not behavioral equivalence.

### Choose the path before choosing the command

| Starting point and goal | Recommended path |
|---|---|
| A distributed TLA+ spec that can be rewritten into tla-rs's message-aware per-node model | Human rewrite to the clean subset, then `tla-lint` and `clean-tla`. |
| A TLA+ module already close to one global relational state model | `translate-tla`, optionally with `.tla-types` and mode generation. |
| A maintained Verus relational spec that should be inspected or checked with TLA+ tools | `verus2-tla`, then review and generate a TLC wrapper if needed. |
| A TLA+ source intended to continue automatically into executable Verus | General `pipeline`, followed by explicit Verus verification and assumption audit. |

Do not alternate the maintained source on each edit. Bidirectional conversion is most useful
for review, migration, and cross-engine checking; it is not a conflict-free two-master editing
system.

### Understand the guarantee ladder

The import workflow has four distinct checkpoints:

1. `tla-lint` decides whether a parsed module satisfies the structural C1–C5 projectability
   contract.
2. `clean-tla` mechanically projects such a module into a single-process protocol-layer Verus
   spec.
3. Verus can typecheck that generated spec, and the source-first checker can explore a chosen
   finite model of it.
4. Human-written or generated proof obligations, discharged by Verus without unreviewed
   assumptions, establish deductive claims.

Passing one checkpoint does not imply the next. In particular, clean-subset acceptance does not
mean the original distributed spec was preserved by a preceding human rewrite, and the
projector emits a spec but never a proof.

### Rewrite a global TLA+ spec into the clean subset

Mechanical projection can remove a node dimension only when the source already says what each
node owns and what it learns through messages. The executable contract is documented in
[`clean_tla_subset.md`](clean_tla_subset.md):

- **C1, per-node state:** every mutable variable is indexed by the fixed node set, is the one
  designated network variable, or is removed as non-runtime history state.
- **C2, no instantaneous cross-node reads:** an action may read its own node's state and message
  fields, but not another node's current array entry or a whole distributed array. Frame
  conditions are exempt.
- **C3, no history variables:** proof-only records of the past are not projected into runtime
  state.
- **C4, one addressed network:** the network uses recognized send, receive, reply, and discard
  idioms, and messages carry source and destination information.
- **C5, node-parameterized actions:** `Next` exposes which node acts; additional node parameters
  may be destinations or other action arguments.

Membership reconfiguration is deliberately outside the current subset. The node set is fixed.

The hard boundary is C2. Replacing `state[other]` requires deciding who sends the value, when it
is sent, whether the receiver caches it, how stale information behaves, and whether a request
blocks. Those are protocol-design choices absent from the original expression. The tool cannot
recover them. Follow the review and TLC procedure in
[`clean_tla_rewrite_playbook.md`](clean_tla_rewrite_playbook.md), and record every semantic
change in the case documentation.

### Lint before translating

Run the current positional-input command:

```bash
transpiler/target/debug/verus-transpile tla-lint path/to/Protocol.tla
transpiler/target/debug/verus-transpile tla-lint --json path/to/Protocol.tla
```

Exit status is part of the interface:

- `0`: the parsed module satisfies all currently checked clean-subset rules;
- `1`: it parsed but has subset violations; and
- `2`: it did not parse and therefore was not measurable.

Machine-readable parse failure uses `"clean": null`, not `false`. A dirty-module JSON report
contains `clean`, `violations`, findings with C1–C5 rule names and source positions, and inferred
metadata such as the network variable. Treat a suspiciously small violation count skeptically
if node-set inference failed; linter silence is not evidence that a real-world module is close
to projectable.

### Project a clean module

Once the linter is clean:

```bash
transpiler/target/debug/verus-transpile clean-tla \
  path/to/Protocol.clean.tla \
  --output out/protocol.rs
```

With no output path, the generated Verus is printed to standard output. The command exits `0`
after emitting a complete projection, `1` when a supported clean module still contains
projection gaps, and `2` for parse or subset failure. On a projection gap it writes no source;
an incomplete relation would still look plausible and must not be reviewed as a complete spec.

The output contains the single-node state/constants/message shapes and projected `LInit`, action,
and `LNext` predicates, including generated frame conditions. It is protocol-layer spec code.
It contains no semantic-equivalence proof, refinement proof, or implementation proof.

The clean-subset path is also reachable through:

```bash
transpiler/target/debug/verus-transpile pipeline \
  --clean-subset \
  --tla-input path/to/Protocol.clean.tla \
  --exec-output out/protocol.rs \
  --spec-output out/protocol.spec.rs
```

At present this mode deliberately stops after writing the projected spec because mode
annotations for the projected signatures are not implemented. `--exec-output` is still required
by the CLI but is not produced. The command also writes a source-derived `.automan` beside the
spec before it stops; its parameter modes describe the unprojected source operators and must not
be used to generate the exec layer. Use `clean-tla` when only the projection is wanted.

### State clean-subset evidence precisely

The corpus under [`transpiler/tests/corpus/`](../transpiler/tests/corpus/README.md) separates
three checks:

- **V1:** a generated golden typechecks with Verus. A spec-only file can report zero verified
  items; the useful result is that names, fields, variants, and types are accepted. The guard
  skips when no Verus binary is installed, so read test output rather than assuming it ran.
- **V2:** under a stated finite TLC model, original and human-rewritten clean specs reach the
  same set of declared observable states. This is not trace, action, or behavioral equivalence.
- **V3:** current projector output byte-matches the frozen generated block after human review.

The evidence report in
[`clean_tla_translator_evidence.md`](clean_tla_translator_evidence.md) records which cases have
which checks. Do not copy a corpus-wide success claim onto a new module. Run the corresponding
checks for that module, and remember that V2 assesses the human rewrite while V3 assesses
projector drift.

### Use the general TLA+ translator

The older, general translator works on a global-model AST rather than the clean-subset
projection:

```bash
transpiler/target/debug/verus-transpile translate-tla \
  --input path/to/Protocol.tla \
  --output out/protocol_spec.rs \
  --types path/to/Protocol.tla-types \
  --gen-modes
```

It parses the module, infers types, applies any `.tla-types` overrides, emits Verus spec code,
and optionally writes `out/protocol_spec.automan`. `--spec-prefix` and `--state-name` control
generated naming. Type hints are especially valuable for empty collections, records, operator
parameters, and named domains that usage alone cannot determine.

This translator is permissive in places: unresolved external shapes in generated round-trip
contexts can become `arbitrary()` placeholders, and some parsed constructs render comments or
marker calls rather than preserved semantics. Inspect the generated file for `arbitrary`,
`unsupported`, `panic!`, temporal markers, and suspicious scalar fallback types. Then typecheck
it. Parser acceptance and a plausible-looking `verus!` block are not enough.

The general end-to-end command is:

```bash
transpiler/target/debug/verus-transpile pipeline \
  --tla-input path/to/Protocol.tla \
  --types path/to/Protocol.tla-types \
  --exec-output out/protocol_exec.rs \
  --keep-intermediate
```

It translates TLA+ to a Verus spec, generates mode annotations, and passes those artifacts to
the spec-to-exec transpiler. The default pipeline configuration sets
`assume_postconditions = true`, so successful generation is not proof that the executable body
establishes its postcondition. The broader code generator's `[output].generate_proofs` setting
also defaults to false. Audit assumptions and run the explicit Verus verification gates before
describing the output as verified.

### Export a Verus spec to TLA+

For a relational Verus spec:

```bash
transpiler/target/debug/verus-transpile verus2-tla \
  --input src/protocol/TwoPhase/twophase.rs \
  --output out/Twophase.tla \
  --spec-prefix L
```

The converter extracts spec functions and type definitions, converts supported expression
bodies to a TLA+ AST, and prints a module. The default prefix rule removes `L` only when the
following character is uppercase, so `LState` becomes `State` while `Learner` is unchanged.
Batch mode accepts an input directory and requires an output directory:

```bash
transpiler/target/debug/verus-transpile verus2-tla \
  --batch --input src/protocol/TwoPhase --output out/tla
```

Batch conversion warns and continues when an individual file fails; inspect warnings and the
converted count rather than trusting the command's final success alone.

The export is a specification view, not a proof export. Requires, ensures, decreases clauses,
proof functions, trigger annotations, trusted markers, and executable Rust semantics are not a
preservation channel. The current CLI exposes `--include-recommends`, but the converter does not
currently consume that configuration when building the module, so do not rely on recommends
appearing as `ASSUME` until a regression test demonstrates it.

Several mappings are intentionally approximate. Views and casts are erased. Map literals are
represented by simplified TLA+ values. Enum matching uses tag-shaped records. Unknown method
calls become ordinary operator applications. Bitwise operations, dereferences, and closure
expressions are rejected. Review generated type operators and data encodings before running
SANY or TLC.

### Generate a TLC wrapper for relational output

`verus2-tla` commonly produces `Init(s, c)` and `Next(s, s_, c)`, whereas TLC expects module
variables and zero-argument initial/next predicates. Generate the adapter explicitly:

```bash
transpiler/target/debug/verus-transpile generate-mc-wrapper \
  --input out/Twophase.tla \
  --output out/Twophase_MC.tla \
  --cfg-output out/Twophase_MC.cfg \
  --init Init \
  --next Next \
  --invariant Consistency
```

The generated `.cfg` is a skeleton. Fill its finite constants and check the wrapper with the
TLA+ tools. Packet projection is optional and semantic: `append-seq` accumulates relational
packet outputs, while `replace-seq` replaces the wrapper channel at each step.

### Respect the semantic fault lines

TLA+ sequences are one-indexed and Verus sequences are zero-indexed. The general translator
adjusts known operators such as `Head` and `SubSeq`, but a generic `f[x]` cannot always be
distinguished as a sequence lookup rather than a map lookup and is emitted directly. Inspect
index boundaries in both directions.

TLA+ functions are total values over a domain; Verus `Map` usage and generated finite runtime
maps may have different definedness expectations. TLA+ admits heterogeneous values and
type-incompatible equality that ordinary Rust/Verus types reject. `CHOOSE` is deterministic but
unspecified in TLA+, while executable choice and bounded model enumeration need an explicit
finite domain. Non-deterministic actions translate naturally as relations but do not become a
deterministic implementation without mode and witness choices.

The parser has AST nodes for temporal operators and fairness. The general translator renders
marker-shaped expressions; that does not make Verus a temporal-logic prover. The source-first
checker handles only configured bounded `leads_to` obligations and branch-label fairness, not an
arbitrary translated temporal formula. Keep temporal checking in the engine whose semantics you
actually invoked.

### Review a round trip responsibly

A useful round-trip review is staged:

1. Parse the source and record which declarations were retained.
2. Translate and typecheck the generated target.
3. Search for placeholders, markers, omitted proof metadata, and changed data encodings.
4. Canonicalize and structurally compare the supported expression subset.
5. Model-check matched finite configurations in both engines when behavior matters.
6. Diff reachable states, initial states, and—when available—edges or action labels.
7. Preserve the source, configs, generated artifacts, tool versions, and stop reasons.

The repository's tests cover parser shapes, representative mappings, mode annotations, clean
projection goldens, Verus typechecking when available, and selected finite TLC state-set
comparisons. Some tests named “roundtrip” verify generated structure without performing a full
semantic cycle. Never summarize that collection as universal TLA+ ↔ Verus equivalence. Appendix
D records support by stage so that a successful parse cannot be mistaken for a verified
translation.

## Chapter 10 — Build and Run an Integrated Protocol

The quickstart proves that the spec-to-executable path works without a
network. An integrated protocol adds a native Rust/Verus shared library, a C#
UDP runtime, certificates that identify the replicas, and one or more service
processes. Treat verification and deployment as separate gates: a service can
build without being verified, and a verified crate can still be misconfigured
at runtime.

### Choose the build you intend

Run SCons from the repository root. `--verus-path` takes the path to the
`verus` executable itself.

| Goal | Command | What it establishes |
|---|---|---|
| Verify/compile Rust and build all C# projects | `scons --verus-path="$VERUS_PATH"` | Full local build gate |
| Verify/compile only the Rust/Verus crate | `scons --verus-path="$VERUS_PATH" --skip-dotnet` | Produces `liblib.so`; no C# binaries |
| Build only the C# projects | `scons --skip-verus` | Produces `bin/*.dll`; reuses any existing native library |
| Build one C# target | `scons --skip-verus bin/IronRSLServerUDP.dll` | Builds that target without invoking Verus |

The integrated commands are defined in [`SConstruct`](../SConstruct). The
normal Verus action both verifies and compiles `src/lib.rs` into `liblib.so`.
`--no-verify` asks Verus to compile without checking proofs; it is useful only
when verification has already passed for the same sources, and its output must
not be described as verified.

The C# projects currently target .NET 6. After building, expose the repository
root to the native loader before starting a service:

```bash
export LD_LIBRARY_PATH="$PWD"
```

If `liblib.so` is old, C# can load an ABI that no longer matches the Rust
sources. Rebuild it after Rust, generated-code, feature, or toolchain changes.

### Run the RSL service

RSL uses dedicated UDP server and client binaries. First generate identities
and a three-replica service description:

```bash
dotnet bin/CreateIronServiceCerts.dll \
  outputdir=certs name=MyCounter type=IronRSL \
  addr1=127.0.0.1 port1=4001 \
  addr2=127.0.0.1 port2=4002 \
  addr3=127.0.0.1 port3=4003
```

Start one server per terminal, keeping `LD_LIBRARY_PATH` set in each:

```bash
dotnet bin/IronRSLServerUDP.dll \
  certs/MyCounter.IronRSL.service.txt \
  certs/MyCounter.IronRSL.server1.private.txt
```

```bash
dotnet bin/IronRSLServerUDP.dll \
  certs/MyCounter.IronRSL.service.txt \
  certs/MyCounter.IronRSL.server2.private.txt
```

```bash
dotnet bin/IronRSLServerUDP.dll \
  certs/MyCounter.IronRSL.service.txt \
  certs/MyCounter.IronRSL.server3.private.txt
```

Then run a workload from a fourth terminal:

```bash
dotnet bin/IronRSLClientUDP.dll \
  ip1=127.0.0.1 port1=4001 \
  ip2=127.0.0.1 port2=4002 \
  ip3=127.0.0.1 port3=4003 \
  nthreads=4 duration=10
```

Stop the servers with Ctrl-C when the experiment finishes. The older
`IronRSLServer.dll` and `IronRSLClient.dll` TCP+SSL pair remains available for
compatibility; use the UDP pair for the maintained default path.

### Run a protocol through the shared server

The other nine protocol selectors share
[`IronProtocolServer.dll`](../csharp/IronProtocolServer/Program.cs):

```text
twophase  leaderelection  primarybackup  chainreplication  paxos
verticalpaxos  raft  pbft  epaxos
```

The server form is:

```bash
dotnet bin/IronProtocolServer.dll \
  <service-description> <node-private-key> protocol=<selector>
```

Server support is not the same as workload-client support. The maintained
[`IronGenericClient.dll`](../csharp/IronGenericClient/Program.cs) has adapters
for `raft`, `pb`/`primarybackup`, `pbft`, and `epaxos` only. For those four, the
repository helper starts the right number of servers, runs the client, prints
its results, and cleans up the processes it started:

```bash
# scripts/bench_generic.sh <protocol> [duration_seconds] [trials] [threads]
scripts/bench_generic.sh raft 8 1 4
scripts/bench_generic.sh epaxos 8 1 4
scripts/bench_generic.sh pbft 8 1 4
```

Generate the certificate files expected by the helper before running it. Raft
and EPaxos use three nodes in `bench/certs`:

```bash
dotnet bin/CreateIronServiceCerts.dll \
  outputdir=bench/certs name=MyRaft type=IronProtocol \
  addr1=127.0.0.1 port1=4001 \
  addr2=127.0.0.1 port2=4002 \
  addr3=127.0.0.1 port3=4003
```

PBFT uses four nodes in `bench/certs_4node`:

```bash
dotnet bin/CreateIronServiceCerts.dll \
  outputdir=bench/certs_4node name=MyRaft type=IronProtocol \
  addr1=127.0.0.1 port1=4001 \
  addr2=127.0.0.1 port2=4002 \
  addr3=127.0.0.1 port3=4003 \
  addr4=127.0.0.1 port4=4004
```

Primary Backup uses the same `bench/certs` filename convention but needs a
two-node service. Regenerate that directory with only `addr1`/`port1` and
`addr2`/`port2`, then run:

```bash
scripts/bench_generic.sh pb 8 1 4
```

Because different protocols reuse `MyRaft.IronProtocol.service.txt`, do not
assume certificates left by a previous node-count experiment are suitable.
The client prints aggregate operations per second and average latency. These
numbers depend on hardware, system load, build mode, client count, and run
duration; they are performance observations, not proof results.

### Use the cluster smoke test for its stated purpose

The integration harness accepts all ten selectors:

```bash
./scripts/integration_test_cluster.sh
./scripts/integration_test_cluster.sh rsl raft
./scripts/integration_test_cluster.sh twophase
```

[`integration_test_cluster.sh`](../scripts/integration_test_cluster.sh)
generates temporary certificates, starts replicas, waits for readiness, and
checks that they stay alive. It runs an end-to-end request/reply client for RSL
and, when its dedicated client is available, a Raft workload. For the other
protocols—including TwoPhase—the pass condition is startup and short-term
stability, not application-level semantic coverage.

### Understand the runtime boundary

The integrated path crosses several boundaries:

```text
generated action and Verus contract
        ↓
hand-written Rust scheduler/host
        ↓
Rust native I/O and FFI declarations
        ↓
C# UDP runtime, files, sockets, clocks, and processes
```

An `ensures` clause on a generated action establishes that action's relation
to its logical predicate when its preconditions hold. It does not by itself
prove that the host calls every action under exactly the modeled conditions,
that marshalling is injective, or that the operating system delivers packets.
Report those runtime components as trusted or separately tested unless a
specific refinement theorem covers them.

## Chapter 11 — Add a Small Protocol End to End

The checked-in TwoPhase protocol is the most useful maintained example for
adding a small networked protocol. It demonstrates logical types, actions,
mode annotations, concrete generation, message generation, scheduler metadata,
a host, a service entry point, and shared-server dispatch. The Counter example
from Chapter 2 remains the smaller reference when you only need to understand
one generated function.

This chapter reproduces TwoPhase before turning that reproduction into a
checklist. That keeps the example grounded in source that the repository
actually builds.

### State the protocol and claim

Two-phase commit has one transaction manager (TM) and a set of resource
managers (RMs). The TM requests preparation, collects prepared votes, and
broadcasts a commit or abort decision. The checked-in logical model records:

- the TM decision state;
- the RMs that have prepared, committed, or aborted; and
- the votes the TM has observed.

Its three named safety predicates say that no RM is both committed and
aborted, every committed RM was prepared, and a committed TM has collected all
required prepared votes. Those are state predicates. They do not assert that a
transaction eventually terminates, survives every failure pattern, or matches
an external database API.

### Map the maintained artifacts

| Role | File |
|---|---|
| Logical types | [`src/protocol/TwoPhase/types.rs`](../src/protocol/TwoPhase/types.rs) |
| Logical actions and safety predicates | [`twophase.rs`](../src/protocol/TwoPhase/twophase.rs) |
| Input/output modes | [`twophase.automan`](../src/protocol/TwoPhase/twophase.automan) |
| Generation, messages, and scheduler config | [`twophase_transpile.toml`](../src/protocol/TwoPhase/twophase_transpile.toml) |
| Concrete generated types/actions | [`src/generated/TwoPhase/`](../src/generated/TwoPhase/) |
| Runtime message type and host | [`src/implementation/TwoPhase/`](../src/implementation/TwoPhase/) |
| Service entry point | [`main_i.rs`](../src/services/TwoPhase/main_i.rs) |
| Native dispatch | [`src/lib.rs`](../src/lib.rs) |

Read the files in that order. The spec tells you what is allowed; the
annotations tell the generator what must be computed; the config maps the
logical representation to Rust; and the host decides when network events call
the generated methods.

### Bound and explore the state graph

Before code generation, run the small finite model used by the transpiler
tests:

```bash
cargo run --quiet --release --manifest-path transpiler/Cargo.toml -- \
  model-check \
  --input src/protocol/TwoPhase/twophase.rs \
  --types src/protocol/TwoPhase/types.rs \
  --model \
    transpiler/tests/model_check_fixtures/twophase_safety_invariants.model.toml \
  --search bfs \
  --json-report
```

At the current revision, this finite configuration exhausts a graph of three
states and four transitions at depth one and reports its configured
`LSafetyTmCommittedRequiresAllPrepared` invariant as satisfied. That is exact
exploration of this configured finite model. It is not an unbounded induction
proof, and changing the bounds, initial values, transition subset, or
invariant changes the claim.

### Validate data-flow annotations

The mode file declares `LInit(-, +)` and marks each transition's old state and
constants as inputs, its new state and sent packet sequence as outputs, and any
selected RM identifier as an input. Check the annotation syntax first:

```bash
cargo run --quiet --manifest-path transpiler/Cargo.toml -- \
  check --annotations src/protocol/TwoPhase/twophase.automan
```

This confirms that the annotation file parses. Generation is the stronger
test because it resolves the annotations against Rust signatures and attempts
to synthesize every output.

The checked-in TwoPhase config currently contains both `arc_wrap_types` and
`mut_self_types` for `CState`. The current generator warns and clears the Arc
settings because these calling conventions conflict. Preserve that warning
when reproducing the existing artifact, but do not copy the conflict into a
new protocol: choose functional state, Arc-backed functional state, or
`&mut self` after studying the action shapes.

### Regenerate into scratch space

Build once, then generate the concrete types and actions outside the source
tree:

```bash
cargo build --release --manifest-path transpiler/Cargo.toml
TLA_RS_TRANSPILER="$PWD/transpiler/target/release/verus-transpile"
mkdir -p /tmp/tla-rs-twophase-generated

"$TLA_RS_TRANSPILER" generate-types \
  -i src/protocol/TwoPhase/types.rs \
  -c src/protocol/TwoPhase/twophase_transpile.toml \
  -o /tmp/tla-rs-twophase-generated/types_gen.rs

"$TLA_RS_TRANSPILER" \
  -i src/protocol/TwoPhase/twophase.rs \
  -a src/protocol/TwoPhase/twophase.automan \
  -c src/protocol/TwoPhase/twophase_transpile.toml \
  -o /tmp/tla-rs-twophase-generated/twophase_gen.rs

cmp /tmp/tla-rs-twophase-generated/types_gen.rs \
    src/generated/TwoPhase/types_gen.rs
cmp /tmp/tla-rs-twophase-generated/twophase_gen.rs \
    src/generated/TwoPhase/twophase_gen.rs
```

At the current revision both comparisons are byte-identical. Inspect each
generated method for validity requirements, the action guard, old/new views,
and the final logical `ensures` clause before verifying it.

Generate the runtime message enum from the same config and compare it too:

```bash
"$TLA_RS_TRANSPILER" generate-messages \
  -c src/protocol/TwoPhase/twophase_transpile.toml \
  -o /tmp/tla-rs-twophase-generated/message.rs

cmp /tmp/tla-rs-twophase-generated/message.rs \
    src/implementation/TwoPhase/message.rs
```

Messages are executable runtime data, so every logical field needs a concrete
encoding and every receiver needs to interpret it consistently with the
modeled action parameter.

### Derive scheduling metadata, then review the host

`LNext` is an existential disjunction, not a generated scheduler. The analyzer
can extract its eight action alternatives and classify them using the message
configuration:

```bash
"$TLA_RS_TRANSPILER" analyze-lnext \
  -i src/protocol/TwoPhase/twophase.rs \
  -c src/protocol/TwoPhase/twophase_transpile.toml \
  -o /tmp/tla-rs-twophase-generated/scheduler.toml
```

Review the output against `LNext`; an incorrect timer/message classification
changes which events can drive an action. The host generator can then produce
a starting point:

```bash
"$TLA_RS_TRANSPILER" generate-host \
  -c src/protocol/TwoPhase/twophase_transpile.toml \
  -p TwoPhase \
  --gen-module twophase_gen \
  -o /tmp/tla-rs-twophase-generated/host.rs
```

The resulting scaffold contains TODO/FIXME sections and placeholder
configuration. It is neither runnable nor verified as-is. Implement and
review runtime glue under `src/implementation/<Protocol>/`; never move those
placeholders into `src/generated/`.

The maintained TwoPhase host is deliberately hand-written. In particular, it
maps UDP messages and timer ticks to generated actions, assigns node zero as
the TM, constructs the RM set from the other peers, and implements only the
scheduler behavior present in that file. Its use of verified action methods
does not prove the host itself refines `LNext`. Audit guards, message origins,
retries, role assignment, and failure behavior as separate obligations.

### Register a new protocol

Following the TwoPhase layout, a new protocol normally needs all of the
following:

1. Add logical types, actions, invariants, annotation, and config files under
   `src/protocol/<Protocol>/`, plus its `mod.rs` exports.
2. Add generated module declarations under `src/generated/<Protocol>/` and
   register the protocol in `src/generated/mod.rs`.
3. Generate types, actions, and—when configured—runtime messages. Check in the
   generated output, but never hand-edit it.
4. Implement the protocol trait, scheduling, configuration, and marshalling
   under `src/implementation/<Protocol>/`; export it from
   `src/implementation/mod.rs`.
5. Add a service entry point under `src/services/<Protocol>/` and export it
   from `src/services/mod.rs`.
6. Add a selector branch to the native dispatch in `src/lib.rs`, update the C#
   server's documented selectors, and add certificate/run instructions.
7. Add regeneration parity, focused verification, model-check, message
   round-trip, scheduler, and runtime smoke tests appropriate to the claim.

Copying module names is easy; preserving the relation among logical message,
concrete message, host event, generated precondition, and next-state action is
the real integration work.

### Verify and smoke-test TwoPhase

Verify the generated modules first, then the whole crate:

```bash
"$VERUS_PATH" --crate-type=lib src/lib.rs \
  --verify-only-module generated::TwoPhase::twophase_gen \
  --verify-only-module generated::TwoPhase::types_gen

scons --verus-path="$VERUS_PATH" --skip-dotnet
```

After a full build, exercise shared-server startup:

```bash
./scripts/integration_test_cluster.sh twophase
```

For TwoPhase this harness checks that three nodes initialize and remain alive
for its observation window. It does not submit a transaction and check the
commit/abort result. Add a protocol-specific client or deterministic host test
before claiming end-to-end functional behavior.

The completion bar for a new small protocol is therefore not merely “the
generated module verifies.” It is: the bounded model says exactly what was
explored; generated contracts refine the intended actions without unreviewed
assumptions; regeneration is deterministic; the hand-written host preserves
the modeled event semantics to the extent claimed; messages round-trip; the
crate verifies; and a runtime test exercises the advertised behavior.

## Chapter 12 — Troubleshooting and Daily Workflow

Most tla-rs failures become manageable once you identify the stage that owns
them. Preserve the failing input and use the narrowest command that reproduces
it; only widen to the full crate or cluster after the local stage passes.

### Diagnose by stage

| Symptom | First command or check | Likely owner |
|---|---|---|
| Rust/Verus source will not parse | Run the same transpiler command with `-v`, then a focused Verus parse/verify | Spec syntax or unsupported parser construct |
| `.automan` rejected | `verus-transpile check --annotations <file>` | Annotation grammar, module name, arity, or mode |
| Annotation parses but generation fails | Run generation on one function/module | Mode/data-flow mismatch or unsupported synthesis |
| Wrong names, types, imports, or receiver style | `verus-transpile --dump-config ...` | TOML placement or mapping |
| Generated file differs unexpectedly | Regenerate to `/tmp` and `cmp` | Changed source/config/tool or stale artifact |
| Generated Rust fails Verus | Focused `--verify-only-module` | Generated contract/proof, logical lemma, bounds, or generator bug |
| Finite model finds a trace | Save JSON report and replay the shortest trace | Spec/invariant or intended model bounds |
| Finite model exhausts immediately | Inspect constants, enum subsets, initial states, and enabled actions | Over-constrained model or transition extraction |
| C# cannot load native code | Check `liblib.so`, `LD_LIBRARY_PATH`, architecture, and current build | Build/loader/ABI boundary |
| Cluster starts but makes no progress | Check every replica log, ports, node count, roles, and quorum | Certificates, scheduler, message routing, or protocol logic |

### Separate annotation syntax from synthesis

This is a useful fast check:

```bash
cargo run --quiet --manifest-path transpiler/Cargo.toml -- \
  check --annotations path/to/protocol.automan
```

It does not load the Rust signatures or prove that outputs are constructible.
If it passes but generation fails, compare every annotation argument with the
corresponding spec signature and ask whether each `-` output is uniquely
determined by conjunctions the translator understands. Use `--auto-skip` only
to inventory unsupported functions; do not silently turn skipped behavior
into a completeness claim.

### Inspect the resolved configuration

TOML keys written after a section header belong to that section. A root option
placed below `[output]`, for example, is no longer a root option. Ask the CLI
what it actually resolved:

```bash
cargo run --quiet --manifest-path transpiler/Cargo.toml -- \
  -i path/to/spec.rs \
  -a path/to/spec.automan \
  -c path/to/spec_transpile.toml \
  --dump-config
```

Check integer mappings, type/view overrides, receiver style, skip lists,
extra preconditions, imports, and `generate_proofs`. That last option defaults
to false and may leave assumption-based placeholders; proof-oriented configs
should enable it and still audit the result.

### Treat bad generated code as a generator failure

When generated Rust is wrong, reduce the input to the smallest spec action
that preserves the problem. Add a transpiler test, fix parsing/translation,
proof generation, or configuration, and regenerate. A local edit under
`src/generated/` will be overwritten, makes parity tests fail, and hides the
actual defect.

If generation writes nothing to the expected file, check the command line:
several subcommands print to standard output when `-o` is omitted. Always pass
an explicit scratch output while debugging.

### Narrow Verus failures

Start with the generated module named in the error:

```bash
"$VERUS_PATH" --crate-type=lib src/lib.rs \
  --verify-only-module generated::Raft::raft_gen \
  --verify-only-module generated::Raft::types_gen
```

Then classify the failure:

- A precondition failure at a call site usually means a guard or validity fact
  was not established.
- A postcondition failure usually means the generated body or proof does not
  establish the logical action after taking views.
- Arithmetic failures often expose the gap between mathematical `int`/`nat`
  and bounded executable integers.
- Quantifier failures often need a finite-domain fact, an explicit lemma, or a
  better trigger; they should not be silenced with an assumption.
- A resource-limit failure is inconclusive, not a counterexample. Re-run the
  same focused module with a larger budget, for example `--rlimit 60`, and
  inspect which obligation consumes it.

Once the focused module passes, run the whole-crate gate. A generated action
can verify alone while its host, shared traits, refinement modules, or feature
combination fail in integration.

### Audit what “verified” excludes

Do not infer trust status from a naming convention or from
`#[verus::trusted]` alone in this repository; that attribute is also used as a
line-count/audit classification marker. Search for the actual proof and
runtime boundaries:

```bash
rg -n 'assume\s*\(|external_body|assume_specification|verifier\(external\)' \
  src/generated src/protocol src/implementation src/lib.rs
```

For each relevant claim, record whether it rests on a Verus proof, a bounded
model-check result, an explicit assumption/external body, a test, or an
unverified runtime component. Raft's generated actions and its higher-level
refinement proof, for example, are separate scopes; explicit assumptions in
one cannot be erased by reporting that the other verifies.

### Debug runtime startup without broad process cleanup

Use the exact service description and private key for each node count. Confirm
that no two live nodes bind the same port, that the selector matches the Rust
dispatch, and that enough replicas are ready for a quorum. If native loading
fails:

```bash
ls -l liblib.so
export LD_LIBRARY_PATH="$PWD"
dotnet --info
```

Rebuild rather than copying an arbitrary shared object into place. Prefer the
repository helper scripts because they track the PIDs they start. When running
servers manually, stop those known terminals or PIDs; avoid broad `pkill`
patterns that can terminate unrelated experiments.

Zero throughput is a symptom, not a diagnosis. Read the server logs before
changing proof code: the common causes are a missing replica, mismatched
certificate set, wrong number of client endpoints, blocked port, stale native
library, or a scheduler action whose guard never becomes true.

### Choose a daily loop

| Change | Fast loop | Required wider gate |
|---|---|---|
| Spec action | Annotation check → bounded model → scratch generation → focused Verus | Invariants/refinement, parity test, whole crate |
| Annotation/config | `--dump-config` → scratch generation → `cmp` | Regeneration suite and focused/whole verification |
| Transpiler implementation | Small regression test → affected protocol regeneration | Full transpiler tests, parity test, whole crate |
| Runtime message/host | Unit/round-trip test → one protocol smoke test | Whole crate, C# build, protocol-specific integration test |
| Documentation only | Validate commands and relative links | Run every inexpensive command represented as current behavior |

A productive spec-edit loop is:

```text
write one relation
  → bound and explore it
  → make data flow explicit
  → generate to scratch
  → inspect the contract
  → verify the smallest module
  → regenerate checked-in output
  → run whole-system gates
```

Commit hand-written sources and their deterministic generated consequences
together. Keep unrelated working-tree changes out of the regeneration diff.

### Know the current edges

The repository is an active verification project, not a general TLA+ compiler
or a proof of the entire deployment stack. Plan around these boundaries:

| Boundary | Practical consequence |
|---|---|
| The transpiler accepts a functionalizable subset of Verus spec relations | Refactor complex nondeterminism and helper data flow into supported, explicit forms |
| `&mut self` generation cannot express every intermediate whole-state transformation | Use functional state where an action computes and reuses an intermediate state |
| Executable integers and collections are finite representations | Supply validity and range obligations; do not equate a concrete bound with an unbounded theorem |
| Source-first model checking operates on configured finite domains and a supported expression subset | State all bounds and distinguish exhaustive finite search from proof |
| TLA+ import/export supports a documented subset | Lint and round-trip representative modules; inspect semantic differences described in Chapters 8–9 |
| Some mature protocol/refinement paths still have explicit assumptions or special generation configuration | Scope claims to the modules actually checked and audit each boundary |
| Hosts, FFI, C# networking, clocks, files, and OS behavior are not automatically covered by action contracts | Test them and describe them as trusted unless a specific proof says otherwise |
| The generic workload client supports four of the nine shared-server protocols | Add a protocol-specific client before claiming functional end-to-end coverage for another selector |
| The maintained integrated path is Linux x86-64 with `liblib.so` and the pinned CI toolchain | Treat other platforms/tool versions as new validation work |

### Report a reproducible failure

A useful issue or review note includes:

- the commit and dirty diff relevant to the failure;
- `verus --version`, `rustc --version`, `cargo --version`, and, for integrated
  failures, `dotnet --info` and the platform;
- the smallest spec, `.automan`, and TOML files that reproduce generation;
- the exact command and complete error output;
- a model configuration and shortest trace for a state-space failure;
- whether the generated result contains assumptions or unchecked bodies; and
- for runtime failures, the service description's node count, selector, ports,
  and per-node logs with secrets removed.

Do not include private-key contents. A small reproducer that preserves the
failing relation is more valuable than a hand-edited generated file or an
unscoped full-build transcript.

# Part II — Developer Guide

Part II explains how to evolve the implementation while preserving proof, generated-code,
runtime, and evidence integrity. The normal loop is to change a source of truth, regenerate
derived artifacts, inspect the diff, run focused tests, and finish with the applicable full
gates.

## Chapter 13 — Contributor Orientation and Non-Negotiable Policies

tla-rs combines a specification language, a code generator, deductive proofs, a
bounded model checker, native Rust, and a C# runtime. A change that looks local can
therefore alter several different claims: what the protocol means, what executable
code is produced, what Verus proves, what the model checker explored, or what the
runtime actually does. The first job of a contributor is to know which of those
surfaces is being changed.

### Sources of truth

When two files disagree, resolve the disagreement in this order:

1. current source, tests, generated-output parity checks, `SConstruct`, and
   `.github/workflows/ci.yml`;
2. the generated-code policy in [`AGENTS.md`](../AGENTS.md);
3. current protocol annotations and `_transpile.toml` files;
4. the root [`README.md`](../README.md) and recently exercised operational guides;
5. design documents;
6. dated phase plans, audits, reports, `TODO.md`, `notes.md`, and `hacks.md`.

The last category is useful for understanding why a design exists, but it is not an
interface specification. In particular, old instructions that say to patch a
generated file manually are historical, even when the patch once worked.

### Generated code is derived code

Everything below `src/generated/` is produced by the transpiler. Do not edit those
files by hand. If generated output is wrong, change the earliest applicable source of
truth:

- change the logical specification if the intended transition is wrong;
- change the `.automan` file if input and output modes are wrong;
- change `_transpile.toml` if a mapping or supported code-generation choice is wrong;
- change `transpiler/src/` if the behavior should be generic;
- change a hand-written proof or implementation helper only when that helper is the
  intended, reviewed boundary.

Then regenerate and review the complete diff. Do not hide a generator limitation by
copying a generated function into an implementation module, delegating to it, and
extracting the result. Such clone/delegate/extract patterns make the checked-in output
look generated while moving its semantics to a second, manually maintained body.
Likewise, do not add an `assume`, an `external_body`, or a proof-fallback stub merely
to make verification green. Those constructs change the trusted base.

The CLI contains guarded `migrate-generated-import` and
`migrate-generated-text` commands for exact mechanical migrations. They reject files
without the generated-file marker and require an expected replacement count. They are
an emergency tool for a controlled migration, not a replacement for fixing the
generator and regenerating. Any use should be followed by a generator change or a
documented reason that regeneration cannot yet reproduce the migration.

### Name the verification boundary

Use precise language in code review and documentation:

- **Verus-verified body** means Verus checked that body against its contract, under
  its preconditions and trusted dependencies.
- **Refinement link** means an executable result is related to a logical predicate by
  a checked contract. It does not show that the logical predicate is the desired
  protocol.
- **`assume`** introduces a proposition without a proof at that point.
- **`external_body`** or an external specification gives Verus a trusted contract
  while hiding or trusting the implementation body.
- **`#[verus::trusted]`** places code in Verus's trusted/audit classification for
  manual inspection. It is not itself an `assume`, and its presence alone does not
  establish that every body in the marked scope was skipped by the verifier. Inventory
  it separately from constructs that directly introduce proof assumptions.
- **Model checked** means no selected property violation was found in the resolved
  finite model and within the reported stopping limits. It is not an unbounded proof.
- **Runtime tested** means an executable scenario ran. It is evidence about the
  integrated system, not a deductive result.

When removing one kind of gap, check that it was not converted into another. Replacing
`assume(P)` with an `external_body` function whose postcondition is `P` moves the trust;
it does not remove it.

### Work safely in a shared or dirty tree

Assume pre-existing modifications belong to somebody else. Before editing, run:

```bash
git status --short --branch
git diff --stat
```

Limit formatting and generated changes to the files in scope. Never use a destructive
reset to clean unrelated work. For derived output, regenerate only the intended
protocol when the script supports a target, and inspect the exact paths before
accepting changes.

### The normal contribution loop

Use the smallest useful gate while iterating, then finish with the gates appropriate
to the affected boundary:

```bash
# Transpiler edit
cargo fmt --manifest-path transpiler/Cargo.toml -- --check
cargo test --manifest-path transpiler/Cargo.toml <focused-test-name>

# Before proposing a general transpiler change
cargo clippy --manifest-path transpiler/Cargo.toml \
  --all-targets --all-features -- -D warnings
cargo test --manifest-path transpiler/Cargo.toml --all-features

# Proof/spec/generated-code change
scons --verus-path="$VERUS_PATH" --skip-dotnet
```

Add regeneration, model-check evidence, round-trip, or cluster tests when those
surfaces change. Chapter 24 maps changes to gates in detail.

### Documentation is part of the change

Commands in durable documentation must be runnable from the stated directory.
Version, proof-count, performance, and trust-site claims must either be generated or
carry a date and reproduction command. Describe historical results as case studies,
not as current guarantees. If a new command or configuration field is introduced,
update its reference section and add a test that makes future drift visible.

## Chapter 14 — System Architecture and Trust Boundaries

The project has two related paths from a logical protocol: a bounded exploration path
and a verified implementation path. They share source syntax but establish different
kinds of evidence.

```text
                         ┌──────────────────────┐
                         │ Verus TLA-style spec │
                         └──────────┬───────────┘
                                    │
                    ┌───────────────┴────────────────┐
                    │                                │
          source-first model checker        spec-to-exec transpiler
                    │                                │
      finite states, traces, reports       concrete types and exec code
                    │                                │
                    └──────── evidence ──────────────┤
                                                     ▼
                                             Verus verification
                                                     │
                                                     ▼
                                      protocol host and service entry
                                                     │
                                                     ▼
                                          Rust/C# FFI and network I/O
```

### Logical protocol layer

Files under `src/protocol/<P>/` define logical types, constants, initialization,
actions, invariants, and—where present—refinement proofs. The common convention is
`L*` for logical types and operations and `s`/`s_` for pre-state and post-state.
This layer describes allowed behaviors; it does not perform network I/O.

The source-first model checker ingests this layer directly. It resolves finite domains
from `model.toml`, constructs initial states, solves transition branches, explores the
bounded graph, and evaluates selected safety, deadlock, and liveness properties. Its
result must be read with the resolved configuration and stop reason.

### Concrete and generated layer

The transpiler combines three inputs:

1. a Verus specification;
2. a `.automan` mode annotation file;
3. a `_transpile.toml` configuration.

It generates concrete `C*` types and executable functions under
`src/generated/<P>/`. A generated function normally has a contract that relates its
concrete inputs and outputs, through `View`, to the corresponding logical predicate.
Some protocols use a functional convention that returns a fresh state. Others use an
`&mut self` convention whose contract relates `old(self)@` to `self@`.

Generated does not mean automatically proved. A generated file can contain verified
bodies, trusted helpers, or explicit proof-fallback stubs. Review the emitted contracts
and trust markers, not only the file banner.

### Implementation, host, and service layers

`src/implementation/<P>/` supplies runtime-facing code that does not naturally belong
in a relational specification: wire-message conversion, configuration parsing,
scheduler glue, host state, executable helpers, and calls into generated transitions.
The non-RSL protocols implement the shared traits in
`src/common/framework/protocol_trait.rs`:

- `ProtocolMessage` serializes and deserializes a wire message;
- `ProtocolConfig` builds protocol configuration and exposes peers;
- `ProtocolHost` initializes state and executes a message- or timeout-driven step;
- `StepResult` and `GenericOutbound` describe sends, broadcasts, sequences, or no
  output.

`src/services/<P>/` contains service entry points. `src/lib.rs` exposes the generic
`protocol_main_wrapper`, which dispatches a protocol name to one of the ten service
modules currently wired into the library. RSL also retains a dedicated wrapper and
dedicated C# server/client binaries.

### Rust/C# boundary

The C# runtime owns UDP receive/send operations, time, endpoint discovery, service
configuration, and process lifecycle. It passes callbacks into Rust through exported C
ABI functions. Rust owns buffers allocated through `allocate_buffer` and reclaims them
through the paired ownership protocol. The wrapper functions, raw pointers, callback
contracts, deserialization behavior, and C# implementation are outside ordinary Verus
body verification and must be treated as a runtime trust boundary.

The crate root currently uses `#![verus::trusted]`. Verus's line-count/audit tooling
uses that attribute to classify the affected source for manual TCB review; do not infer
from the marker alone that every declaration in the crate was unchecked. Separately,
the exported FFI functions are marked external and their bodies and environment are a
real proof boundary. Both facts belong in an end-to-end trust statement. A green Verus
run still provides valuable function- and proof-level checking, but it must not be
described as verification of the C# runtime, raw-pointer behavior, networking, or the
entire executable environment.

### Trust inventory

A useful audit separates at least five categories:

| Category | How to find it | Review question |
|---|---|---|
| Active assumptions | `rg '\bassume\s*\(' src` and the `report-assumes` command | Is the proposition justified, and is its scope minimal? |
| External bodies/specifications | search for `external_body`, `external`, and `assume_specification` | Is the contract strong enough and independently justified? |
| Trusted/audit classification | search for `verus::trusted` | What source is assigned to manual TCB review, and which separate escape hatches does it contain? |
| FFI and unsafe code | search exported ABI and `unsafe` blocks | Are ownership, length, encoding, and callback contracts tested? |
| Bounded evidence | inspect resolved model, report, and stop reason | Was the intended state space/property actually explored? |

Run inventories against current source. Do not copy counts from a phase report. As of
the tree used for this draft, the generated RSL directory reports no active
`assume(...)` sites, but it contains external bodies, including explicit fallback
stubs. The Raft refinement proof still contains active assumptions. These are different
facts and should never be collapsed into a single “verified/unverified” label.

### Changing a boundary

When a change crosses a boundary, update all adjacent contracts:

- a new logical message field requires logical type/action changes, concrete type and
  View changes, code-generation configuration, wire encoding, host conversion, and
  tests;
- a new scheduler action requires `LNext` coverage, action classification, host
  dispatch, guard/witness handling, and timeout/message tests;
- a changed FFI callback requires matching Rust and C# signatures plus ownership and
  failure-path tests;
- a removed trusted body requires a verified body and a regression test that fails if
  the trust marker returns.

The architecture is strongest when each relation is explicit and mechanically
checked. Avoid interfaces that rely on two components independently constructing “the
same” packet sequence without a verified or tested correspondence.

## Chapter 15 — Repository Tour and Conventions

### Root-level infrastructure

The repository root contains the integrated build and the cross-cutting developer
tools:

- `SConstruct` builds the Verus/Rust library and the C# projects;
- `.github/workflows/ci.yml` defines the authoritative CI jobs;
- `scripts/` contains regeneration, verification, model-check evidence, parity,
  trigger, timing, integration, and benchmark helpers;
- `reports/` stores checked-in evidence where a drift guard is documented;
- `examples/quickstart/` is the CI-checked minimal spec-to-program example;
- `docs/` contains this book and specialized background material.

`TODO.md` is a large engineering ledger. Use it to find active work, not to learn the
current interface.

### Protocol source

Each main protocol has a directory under `src/protocol/`. A typical non-RSL directory
contains:

```text
types.rs
<module>.rs
<module>.automan
<module>_transpile.toml
mod.rs
```

Raft additionally contains a substantial `refinement_proof/` tree. RSL is decomposed
into proposer, acceptor, learner, executor, election, broadcast, replica, configuration,
constants, shared proof, and refinement-proof modules. Shared protocol definitions live
under `src/protocol/common/`.

### Generated output

`src/generated/<P>/types_gen.rs` holds concrete types and Views; the protocol-specific
`*_gen.rs` holds executable transitions and generated proof support. `mod.rs` exposes
the generated module. `src/generated_backup/` is historical material and must not be
mistaken for the active build input.

Generated names preserve correspondence with the logical source. For example,
`LState` normally maps to `CState`, and `LSend1a` maps to `CSend1a`. RSL retains names
that mirror the IronFleet lineage even when they do not follow idiomatic Rust casing.

### Hand-written executable integration

`src/implementation/<P>/` contains a `host.rs` and `message.rs` for the generic
protocols, plus occasional verified helpers. RSL has a larger implementation surface
because its runtime and proof port predate the generic host framework. Shared
marshalling and runtime support live in `src/implementation/common/`.

`src/services/<P>/main_i.rs` connects a protocol host to the network loop. Files ending
in `_i` conventionally contain implementation-facing executable code; `_s` is used for
specification-facing or logical runtime definitions. The suffix convention is not
perfectly universal, so imports and function modes remain the final authority.

### Shared foundations

`src/common/` includes collection bridges, logical helpers, framework traits, native
I/O abstractions, and endpoint/network types. `src/verus_extra/` contains additional
Verus utilities. These directories are high-leverage: changing a contract here can
affect many protocols and proof obligations. Prefer monomorphic, well-specified bridge
lemmas over broad axioms when Verus cannot reason directly about a standard collection.

### C# runtime

`csharp/Common/` and the service projects implement networking and interop. The generic
server dispatches protocol names through `protocol_main_wrapper`. A generic client is
currently implemented for Raft, Primary-Backup, PBFT, and EPaxos; other server entries
exist but do not automatically imply a matching benchmark client. RSL has separate UDP
server and client projects. Certificate generation is shared.

### Transpiler crate

The `transpiler/` Cargo package builds the `verus-transpile` library and CLI. Its main
source modules are:

| Module | Responsibility |
|---|---|
| `annotation` | `.automan` parsing |
| `ast` | internal Verus expression, type, and function representation |
| `parser` | extraction and parsing of supported Verus syntax |
| `moder` | mode annotation, assignment tracking, functionalization checks |
| `checker` | saturation, harmony, obligation, and template checks |
| `types` | type parsing and registry |
| `templates` | recognized relational/quantifier patterns |
| `translator` | executable expression/function and proof generation |
| `codegen` | concrete types, messages, marshalable code, scheduler, and host output |
| `printer` | Rust/Verus rendering |
| `config` | TOML schema and defaults |
| `modelcheck` | finite-domain execution and exploration |
| `tla` | TLA+ parse/type/translation and clean-subset tools |
| `verus2tla` | Verus-to-TLA+ conversion |
| `roundtrip` | canonical structural comparison |

The binary entry point is `transpiler/src/main.rs`; the orchestration API is in
`transpiler/src/lib.rs`.

### Tests and evidence

Unit tests are colocated with modules. `transpiler/tests/` contains integration,
negative, pipeline, round-trip, parity, and regeneration tests, along with TLA and
model-check fixtures. Some large integration tests also assert documentation and CI
wiring. Scripts under `scripts/` test the Python evidence tools.

Use the closest existing fixture as the shape for a new regression. A translator bug
normally needs a small unit test and, when it affected a real protocol, a regeneration
or integration assertion. A model-check semantic change needs evaluator/solver tests
and evidence-drift review.

## Chapter 16 — Toolchain, Build System, and Local Development Loop

### Two Rust toolchains

The transpiler is an ordinary Rust 2021 Cargo package and is built with a recent stable
toolchain. Verus verification uses the Rust version against which the pinned Verus
release was built. At the time of this draft, CI pins Verus
`0.2026.08.02.b677dd5` and Rust `1.97.1`. Treat `.github/workflows/ci.yml` as
authoritative when these values change.

The other build dependencies are Python 3 with SCons and the .NET 6 SDK. The current
Verus release launcher requires a glibc 2.39 environment, so CI uses Ubuntu 24.04 for
verification. `scripts/verify_local.sh` documents a lower-glibc path that invokes
`rust_verify` directly with a compatible Rust toolchain and Z3 binary.

### Build graph and SCons options

`SConstruct` has two independent groups of targets: C# projects and the Verus/Rust
`liblib.so`. The `--verus-path` value is the path to the Verus executable, not its
containing directory.

```bash
# Verify/compile Rust and build C# projects
scons --verus-path=/path/to/verus/verus

# Verify/compile only the Rust/Verus crate
scons --verus-path=/path/to/verus/verus --skip-dotnet

# Build only C# projects
scons --skip-verus

# Compile Rust without verification (runtime iteration only)
scons --verus-path=/path/to/verus/verus --skip-dotnet --no-verify

# Debug rather than optimized output
scons --verus-path=/path/to/verus/verus --debug-build

# Pass diagnostics through to Verus
scons --verus-path=/path/to/verus/verus --skip-dotnet \
  --verus-extra-args="--time-expanded"
```

`--no-verify` is not evidence. Do not use a no-verify build to support a correctness
claim. It is useful only after a corresponding verified source state is known or while
debugging runtime integration.

### Transpiler inner loop

Run Cargo from the repository root with `--manifest-path`, or change into
`transpiler/`:

```bash
cargo fmt --manifest-path transpiler/Cargo.toml -- --check
cargo clippy --manifest-path transpiler/Cargo.toml \
  --all-targets --all-features -- -D warnings
cargo test --manifest-path transpiler/Cargo.toml --all-features
```

During implementation, select a test by name or test target:

```bash
cargo test --manifest-path transpiler/Cargo.toml \
  test_name_fragment -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml \
  --test negative_tests
```

Regeneration parity tests spawn the transpiler and may contend for Cargo's build lock.
When running a regeneration test directly, follow the test's documented
single-threaded invocation if needed.

### Local Verus on an older host

The helper script bypasses only the release launcher; it does not bypass verification:

```bash
VERUS_DIR=/path/to/verus-x86-linux \
RUSTUP_DIR=/path/to/rustup-home \
Z3_PATH=/path/to/z3 \
scripts/verify_local.sh
```

It also forwards Verus options, such as `--time-expanded` or trigger diagnostics. Its
defaults point to a developer cache and are not portable, so set the documented
environment variables explicitly on another machine.

### Fast loop and full loop

Choose the loop by the change:

| Change | Fast loop | Completion gate |
|---|---|---|
| Parser/AST | focused parser tests | format, clippy, full Cargo tests |
| Translator/codegen | focused unit + fixture generation | full Cargo tests, affected regeneration parity, Verus |
| Spec/proof | focused Verus module if useful | whole-crate SCons verification |
| Model checker | focused evaluator/solver/explorer test | full Cargo tests, matrix rebuild, drift guard |
| Runtime/FFI | focused Rust/C# build and smoke test | SCons build, integration test, relevant verification |
| Documentation command | run the command | documentation/quickstart guards |

`scripts/run_ci_local.sh` is convenient, but it is not a byte-for-byte reproduction of
all current workflow steps. The GitHub workflow remains authoritative: it also performs
quickstart checks, model-check normalization/drift, and trigger/timing artifact work
that the local wrapper does not fully mirror.

### CI/local mismatches

When CI fails but local checks pass:

1. compare the exact toolchain versions and OS/glibc;
2. inspect the working directory used by the CI step;
3. check whether CI regenerated a corpus or evidence before testing;
4. check feature flags and `--all-targets`/`--all-features`;
5. compare the complete Verus command, including extra flags;
6. distinguish timing noise from a structural artifact diff;
7. rebuild the transpiler so a stale binary cannot explain the difference.

## Chapter 17 — Transpiler Architecture

The main spec-to-exec path is deliberately staged. Keeping stages separate makes a
failure diagnosable and helps contributors add generic behavior instead of protocol
name checks.

### CLI and configuration entry

With no subcommand, `verus-transpile` runs the spec-to-exec path using
`--input`, `--annotations`, `--config`, and `--output` (or `--stdout`). The CLI loads
the TOML file, combines it with inferred information and command-line modes, resolves
known interactions such as `mut_self_types` versus Arc wrapping, and can print the
resolved configuration with `--dump-config`.

`--dry-run` avoids writing output. `--auto-skip` continues after per-function
translation failures and reports skipped functions. `--proof-fallback` also emits
`external_body` stubs and therefore enlarges the trusted surface; it is a diagnostic or
explicit migration mode, not a successful proof result.

### Parse and annotate

`parser` extracts supported Verus functions and expressions into the internal AST.
The AST preserves constructs the later passes need: types, calls, equality and
relations, conjunctions/disjunctions, `if`/`match`, quantifiers, collection literals,
field and arrow access, Views, closures, and struct construction/update.

The annotation parser loads one or more modules from `.automan`. Each function is
classified as a predicate or helper, and each parameter receives an input or output
mode. Helpers return a value directly; predicates describe outputs relationally.

### Mode analysis and validation

`ModeAnalyzer` attaches modes, tracks assignments, and decides whether a predicate can
be functionalized. A predicate normally needs at least one output. A helper should not
declare output parameters. Assigning a general output inside a quantifier is rejected
unless it matches a supported comprehension pattern.

Three named checks capture the AutoMan discipline:

- **saturation**: every output, or every known field of a structured output, is
  assigned;
- **harmony**: the same output member is not assigned more than once;
- **obligation**: an output is not read before it has been assigned.

The analyzer also detects input assignment and mismatched output sets across branches.
These diagnostics are preferable to letting malformed modes reach Rust type checking.

### Type registry and mapping

The type parser builds a registry of structs, enums, aliases, fields, and function
signatures. Naming rules and explicit remappings choose concrete types. Additional
configuration identifies primitive aliases, collection fields, custom View expressions,
variant paths, equality functions, and clone strategies.

Type generation emits concrete definitions, validity predicates, View implementations,
clone support, optional extra fields, aliases, derives, and imports. Multi-file type
generation processes inputs in the supplied order, which matters when later definitions
depend on earlier ones.

### Pattern recognition and functionalization

Relational predicates become executable only when the translator can identify how each
output is constructed. Common cases include whole-value assignment, field-by-field
struct construction, identity transitions, conditionals, sequence comprehensions, and
supported map/set patterns. Template matching is semantic enough to recognize a small
family of quantifier shapes, but it is not a general theorem prover.

When a new real-world pattern is missing, add it in layers:

1. a minimal parser/AST fixture if syntax is missing;
2. a matcher or analysis result that describes the pattern;
3. executable lowering;
4. proof-needs analysis and generated proof support;
5. positive and negative tests;
6. a real-protocol regeneration test when applicable.

### Translation and proof generation

`translator` converts annotated functions into executable signatures and bodies. It
shapes borrowed/owned arguments, lowers spec helpers to configured functions or methods,
constructs outputs, generates loops where enabled, and supports both functional and
mutating conventions.

Contracts are part of output generation, not decoration. Input validity and extracted
spec preconditions become `requires`; output validity and the logical relation become
`ensures`. Proof-needs analysis adds lemmas and proof blocks for known View and
collection gaps. The right fix for a repeated proof failure is normally a reusable
proof pattern keyed to an analyzed operation and type mapping.

### Printing and deterministic output

`printer` renders the internal executable representation as Rust/Verus. Generated
files carry a marker used by policy guards and migration commands. Deterministic output
is important because the repository checks generated artifacts in and compares fresh
generation with them. Avoid embedding timestamps, host paths, or nondeterministic map
iteration into generated text.

### Specialized generators

Subcommands reuse the same configuration for adjacent artifacts:

- `generate-types` emits concrete types and Views;
- `generate-messages` emits a `ProtocolMessage` implementation from `[messages]`;
- `generate-marshalable` emits configured serialization code;
- `analyze-lnext` extracts scheduler action structure;
- `generate-host` emits a host scaffold from message and scheduler configuration;
- `generate-mc-wrapper` emits a TLC wrapper and `.cfg` skeleton.

Generated host output is a scaffold. Runtime policy—timeouts, retry behavior, client
semantics, and wire compatibility—still requires review and may remain hand-written.

### Error strategy

A clean failure is better than trusted output. Unsupported syntax should report its
source context and the closest supported shape. Auto-skip reports must be reviewed;
they must not quietly become the normal build. Proof fallback must be visible in the
generated diff and trust inventory. A generic capability is complete only when its
diagnostic, code, proof, tests, and documentation agree.

## Chapter 18 — Annotation and Configuration Internals

Annotations say which values are supplied and which values a relational predicate must
compute. Configuration says how logical names and operations become concrete Rust and
which supported generation strategy to use. Keep those responsibilities distinct:
annotations describe data flow; TOML describes representation and code generation.

### Annotation model

A `.automan` file contains module blocks. Ordinary entries are predicates; entries
prefixed with `helper` are value-returning functions:

```text
module Example::Counter {
    LInit(-, +);
    LIncrement(+, -, +);
    helper NextValue(+) -> int;
}
```

`+` means the caller supplies the parameter. `-` means the generated function computes
it. Modes follow the specification's parameter order. A helper's explicit return type
is optional in the current parser; when omitted, translation falls back to the parsed
specification return type. Supplying it is often clearer and gives better diagnostics.

The parser accepts `//` comment lines. Existing annotation files also contain ordinary
Rust-like comments around entries. Keep each declaration on one line; the current
annotation parser is line-oriented.

### Mode invariants

Mode checking answers a concrete question: can the relation be turned into a function?

- For a predicate, at least one parameter must be an output.
- A helper is a value-producing function and should have input parameters only.
- A structured output must be assigned as a whole or have all known fields assigned.
- A field cannot receive two independent assignments.
- Every branch must construct a coherent set of outputs.
- An output cannot be used as an input before its value is known.
- General assignments under quantifiers are rejected; supported comprehensions are
  recognized explicitly.

Validate an annotation file independently with:

```bash
cargo run --manifest-path transpiler/Cargo.toml -- \
  check --annotations src/protocol/Raft/raft.automan
```

The annotation checker establishes that the file parses. Full mode and
functionalization checks happen when the annotated spec is transpiled, so a successful
`check` command is necessary but not sufficient.

### Configuration resolution

The root TOML schema is `TranspilerConfig` in `transpiler/src/config.rs`. It contains
root keys and maps, a `[naming]` table, an `[output]` table, optional message,
marshalable, and scheduler sections, and optional module-specific settings. Real
protocol configurations are the best examples of combinations that currently run.

Before debugging translation, inspect the resolved configuration:

```bash
cargo run --manifest-path transpiler/Cargo.toml -- \
  --input src/protocol/Raft/raft.rs \
  --annotations src/protocol/Raft/raft.automan \
  --config src/protocol/Raft/raft_transpile.toml \
  --dump-config
```

Resolution can infer collection and clone information from parsed types and can apply
CLI modes. The dump is more useful than reasoning from an individual TOML fragment.

### Naming and representation

`[naming]` selects logical and concrete prefixes and the concrete integer types.
`[remapping]` handles exceptions to the prefix rule. Representation-related maps then
make the abstraction explicit:

- `view_overrides` customizes a generated type field's View expression;
- `type_view_exprs` customizes how a type appears in function contracts;
- `primitive_types` maps integer-like aliases through a cast rather than `@`;
- `skip_valid_types` keeps `@` but suppresses a nonexistent validity method;
- `variant_remapping` and `arrow_variants` connect logical variant syntax to concrete
  enum patterns;
- `eq_function_fields` routes equality through a verified/configured comparison
  function.

Do not solve a representation mismatch by inserting a cast at a single translation
site. Encode the type-level rule so every function and proof sees the same mapping.

### Calls and preconditions

`function_paths` resolves cross-module generated calls. `method_calls` turns a logical
free-function call into a concrete method call and can extract a tuple element.
`inline_expansions` controls a small set of analyzed call-shaping strategies, such as an
owned call, a conditionally lowered binary operation, or mixed borrowed arguments.

`extra_requires` is a last-mile mechanism for a precondition the translator cannot yet
derive. Each entry changes the callable domain of the generated function. Review it as
a semantic change, not a type-checking hint, and add a test showing why it is needed.

### Collections, Views, and clones

Collection configuration provides facts that Rust types alone may not expose to the
translator across files:

- `collection_fields` and `set_fields` identify set-backed fields;
- `vec_fields` and `hashmap_index_fields` distinguish sequence/map operations;
- `struct_vec_fields` describes an element View mapping;
- `map_fields` describes deep map abstraction and proof-helper generation;
- `clone_fields`, `clone_field_types`, `clone_strategy`,
  `clone_up_to_view_types`, and `verified_clone_fns` control proof-aware cloning;
- `vec_element_ensures` adds per-element output contracts.

Prefer a verified clone function whose contract states View preservation over a trusted
clone wrapper. If a generic collection limitation forces a trusted helper, make its
contract narrow, document the soundness argument, and inventory it.

### Calling convention and performance options

`mut_self_types` changes functions on the listed concrete state types from a
functional `&State -> State` convention to `&mut self`, with contracts expressed using
`old(self)` and the post-state `self`. This is a semantic-preserving lowering only when
the translator can express intermediate state updates and prove the resulting body.

`arc_wrap_types` and `arc_wrap_fields` provide shallow sharing for functional code.
They conflict with `mut_self_types`; current resolution warns and clears Arc wrapping
when mutable-self generation is selected. Do not configure both and rely on the
warning. Choose a convention deliberately and keep the TOML readable.

### Skips and trust-producing options

Several fields need heightened review:

- `skip_functions` suppresses normal translation;
- `no_stub_functions` suppresses fallback stubs for definitions supplied elsewhere;
- CLI `--proof-fallback` emits trusted `external_body` stubs;
- `[output].assume_postconditions` makes postconditions vacuous through
  `assume(false)`, except for listed `proven_functions`;
- `[output].manual_code` injects another source file into generated output.

These are migration mechanisms, not proof strategies. The repository policy forbids
hand-patching generated output and directs contributors to improve proof generation.
Do not introduce a new trusted fallback to finish ordinary feature work. If an existing
protocol still uses one, preserve its visibility and work toward a generic replacement.

### Adding a configuration option

A new option is complete only when all of the following land together:

1. a serde field with an accurate default and documentation in `config.rs`;
2. resolution into the internal translator/type/printer configuration;
3. validation of incompatible values;
4. behavior in every applicable generation path, including `generate-types` when
   relevant;
5. unit tests for default, enabled, and invalid/interaction cases;
6. a resolved-config or real-protocol test;
7. Appendix C and a focused example;
8. regenerated output if a checked-in protocol adopts it.

Avoid a protocol-name conditional. If the option cannot be described in terms of syntax,
types, modes, or an explicit generic policy, the underlying abstraction is probably
missing.

## Chapter 19 — Generated Artifact Lifecycle

Generated files are checked in so reviewers can see executable and proof changes, CI
can verify the exact artifacts users receive, and downstream builds do not need to run
the transpiler implicitly. That benefit depends on reproducibility.

### Inputs determine output

For a single-module protocol, generated output normally depends on:

```text
src/protocol/<P>/types.rs
src/protocol/<P>/<module>.rs
src/protocol/<P>/<module>.automan
src/protocol/<P>/<module>_transpile.toml
transpiler/src/**
```

RSL type generation consumes several specification files in dependency order and each
RSL component has its own annotation and configuration. Message generation can also
write an implementation-layer `message.rs`; review the regeneration script before
assuming its writes are confined to `src/generated`.

### Regenerate an intended target

Build the current transpiler, then target one protocol:

```bash
./scripts/regenerate_all.sh Raft
git diff -- src/generated/Raft src/implementation/Raft/message.rs
```

For diagnosis, prefer generating into a temporary output path with direct CLI commands:

```bash
scratch_dir=$(mktemp -d)
cargo run --manifest-path transpiler/Cargo.toml -- generate-types \
  -i src/protocol/Raft/types.rs \
  -c src/protocol/Raft/raft_transpile.toml \
  -o "$scratch_dir/types_gen.rs"
cargo run --manifest-path transpiler/Cargo.toml -- \
  -i src/protocol/Raft/raft.rs \
  -a src/protocol/Raft/raft.automan \
  -c src/protocol/Raft/raft_transpile.toml \
  -o "$scratch_dir/raft_gen.rs"
diff -u src/generated/Raft/raft_gen.rs "$scratch_dir/raft_gen.rs"
```

The temporary directory keeps exploration out of the active artifact tree. Remove it
after review; do not commit scratch or `src/generated_fresh` directories.

### Diagnose drift at the source

Classify a diff before changing anything:

- **spec drift**: contracts or behavior changed because the logical source changed;
- **annotation drift**: signature, ownership, or return construction changed;
- **configuration drift**: names, imports, representation, calling convention, or proof
  options changed;
- **generator drift**: the same inputs now produce different text;
- **manual drift**: checked-in output contains text fresh generation cannot produce.

Manual drift is a policy violation or historical debt. Do not preserve it by teaching
the script to copy the old file. Reconstruct the intended behavior in a real source of
truth and add a parity test.

### Review four dimensions

A generated diff needs more than a compile review:

1. **Behavior** — do branches, guards, updates, and outputs still implement the logical
   action?
2. **Contract** — are all required preconditions, validity claims, and View-based
   refinement links present?
3. **Trust** — did `assume`, `external_body`, an external specification, a manual
   injection, or a fallback stub appear or broaden?
4. **Cost** — did ownership, cloning, collection traversal, or proof complexity change?

Search the changed output explicitly:

```bash
rg -n 'assume\s*\(|external_body|assume_specification|TRANSLATE-TODO|PROOF-TODO' \
  src/generated/<P>
```

For RSL-generated assumptions, the CLI can produce JSON:

```bash
cargo run --manifest-path transpiler/Cargo.toml -- \
  report-assumes --input-dir src/generated/RSL
```

The command scans files directly in the supplied directory; invoke it separately per
protocol directory rather than assuming recursive traversal.

### Parity and verification

The integration suite contains per-protocol function and type regeneration checks.
Run the affected test first, then the broader suite. Finally run Verus over the crate:

```bash
cargo test --manifest-path transpiler/Cargo.toml \
  regen_matches_checked_in -- --test-threads=1
scons --verus-path="$VERUS_PATH" --skip-dotnet
```

If a generated function is used by a runtime host, add or run the corresponding
integration/cluster test. A byte-identical regeneration proves reproducibility, not
runtime correctness; Verus proves contracts, not network compatibility. Both layers
matter.

### Unsupported functions

The preferred response to an unsupported function is to reduce it to a minimal fixture
and add generic support. Until that work is complete, an explicit skip or fallback in
configuration is more honest than an untracked hand edit, but it is still a documented
gap. A fallback stub must remain visible in source, generated output, trust inventories,
and status documentation.

Do not use an implementation function with the same postcondition as proof of generated
equivalence. Two implementations can satisfy a nondeterministic relation while choosing
different allowed results. If exact equivalence matters, prove or test the stronger
determinism/equality property.

### Recovering from historical instructions

Some old regeneration notes prescribe Arc patches, body copying, or manual merges into
`src/generated`. Do not follow them. Use them only to identify the behavior that once
needed support. Then locate the current configuration and generator implementation,
write a regression for the intended output, implement the generic capability, regenerate,
and delete or clearly archive the obsolete instruction.

## Chapter 20 — Verus Proof Engineering and Proof Generation

Proof failures are often representation failures: the executable operation is correct,
but Verus needs an explicit bridge between a concrete collection, its View, and the
logical operation. The scalable response is a small lemma or a generator pattern—not a
trusted postcondition.

### Start from the failed contract

Read a generated function in this order:

1. `requires`: what is the caller promising?
2. executable body: what value or mutation is produced?
3. validity `ensures`: what representation invariants must hold?
4. refinement `ensures`: which logical action must follow?
5. helper contracts and trusted dependencies.

Reduce the failure to one of four classes:

- the executable body is wrong;
- a necessary input condition is missing;
- the relation is correct but an abstraction lemma is missing;
- the statement crosses a genuine trusted boundary.

Do not begin by increasing rlimits. A timeout can be a trigger explosion or a malformed
goal rather than an intrinsically hard proof.

### Validity by construction

When a concrete output is built entirely from valid inputs and valid constructors,
Verus can often prove `result.valid()` after unfolding the relevant definitions. Keep
validity predicates compositional. For nontrivial nested fields, add a lemma at the
constructor/helper boundary rather than repeating field assertions at every call site.

Extra executable fields used only for optimization still need a clear relationship to
validity and View. If they are absent from the logical type, initialize and maintain
them so they cannot affect the logical result unexpectedly.

### Input-only clauses become preconditions

A relational action may contain clauses that constrain only the pre-state and constants.
The generated body cannot prove an arbitrary fact about its input. Such clauses belong
in `requires`, provided that callers can establish them and the action is intended to be
partial on other states.

Extract the smallest input-only condition. Do not copy the entire action guard into
every helper. Then verify every call site. Adding a precondition that callers establish
with `assume` has only displaced the gap.

### Clone and View preservation

An identity logical transition needs more than Rust's `Clone`: the proof needs the
clone's View to equal the source View, and sometimes needs validity preservation or full
structural equality. Prefer an executable helper with a verified body and a narrow
contract such as:

```rust
ensures
    result@ == input@,
    input.valid() ==> result.valid(),
```

Use full structural equality only when a concrete downstream operation genuinely
depends on it. Stronger contracts increase proof cost and can force trust in concrete
equality implementations.

### Empty collection mapping

An empty concrete `HashSet<u64>` views as a `Set<u64>`, while the logical field may be
`Set<int>`. The required fact is not simply “empty equals empty”; it is that mapping the
empty concrete set through the conversion yields the empty logical set. Bind the map
function or mapped collection before a quantified assertion so the trigger does not
contain an inline lambda.

The same shape occurs for `Vec<CEntry>` to `Seq<LEntry>` and for deeply abstracted maps.
Generate one helper per mapping shape and deduplicate it per file.

### Insert, remove, and push commute with abstraction

Common executable updates need corresponding algebraic lemmas:

```text
map(insert(S, x), f) = insert(map(S, f), f(x))
map(remove(S, x), f) = remove(map(S, f), f(x))
map(push(Q, x), f)   = push(map(Q, f), f(x))
```

Set removal requires injectivity of `f`; otherwise removing one concrete value could
remove a logical image shared by another concrete value. State that premise or use a
mapping, such as `u64 as int`, whose injectivity is provable. Use extensional equality
when Verus needs elementwise set/sequence reasoning.

### Deep map abstraction

RSL uses maps whose keys and values both change representation. Define the abstraction
once, then provide lemmas for the operations the executable code performs: empty,
singleton, insert, remove, get, contains, and filter. Each lemma should expose exactly
the logical operation needed by action proofs.

HashMap/HashSet iteration is a recurring Verus boundary because executable iteration
and logical domain reasoning do not always have sufficient library specifications.
When a trusted bridge is unavoidable, keep it monomorphic where practical, make its
soundness basis explicit, and prevent it from being mistaken for a proved algorithm.

### Branch decomposition

For an `if`/`else` logical action, match executable branches to logical branches. In
each branch:

1. establish the logical guard or its negation;
2. establish field-level View equalities;
3. use collection extensionality where necessary;
4. fold those facts into the logical predicate.

This is more stable than asking SMT to unfold a large action and discover the branch
correspondence unaided.

### Loops and invariants

Generated loops need invariants that describe the processed prefix/domain, not only the
final result. For a sequence-building loop, typical invariants include index bounds,
result length, and a quantified fact for every completed index. For a map filter, track
seen keys, output-domain inclusion, value preservation, and the filter predicate.

When the final contract concerns `result@.map(|...| ...)`, field-level invariants on
`result@[i]` are often more trigger-friendly than an invariant containing a mapped
sequence and lambda. After the loop, bind the mapped sequence and prove the extensional
connection once.

Recursive helpers need a decreases measure that follows the executable recursion.
Proving termination and proving functional correctness are separate obligations; do not
hide either with a fallback stub.

### Triggers and solver stability

For arithmetic in triggers, separate the arithmetic relation from the term that should
trigger instantiation. A common shape is to introduce another quantified variable and
state `j == i + 1`, then trigger on a non-arithmetic use of `j`.

Explicit triggers are performance-sensitive proof code. Before changing them:

1. capture the current trigger inventory and per-module timing;
2. make a small batch;
3. run full verification with the same Verus release and trigger mode;
4. diff removed, added, and changed trigger choices;
5. reject material solve-time regressions even if verification remains green.

[`phase54-trigger-workflow.md`](phase54-trigger-workflow.md) documents the inventory,
timing, and guard commands. Compare inventories only when their capture modes match.

### Trust decision tree

Before accepting a trusted construct, ask:

1. Is the proposition an input condition? Make it a precondition and prove callers.
2. Is it a View/collection fact? Add a reusable verified lemma.
3. Is it a solver-instantiation problem? Restructure the proof or trigger and measure it.
4. Is it an executable library operation with a missing spec? Add the narrowest justified
   external specification and document the soundness basis.
5. Is it truly environment behavior, such as network callback semantics? Put the trust
   at that boundary and test it end to end.

Every new `assume`, `external_body`, external specification, or trusted marker deserves
an explicit review note. Add a guard test when the accepted count, placement, or exact
form matters.

### Turn a local proof into a generator capability

Once a proof works in one protocol:

1. identify its applicability condition in AST/type terms;
2. add proof-needs analysis rather than a protocol-name test;
3. generate and deduplicate the helper;
4. call it only at matching operations;
5. add positive, negative, and no-duplicate tests;
6. regenerate the motivating protocol;
7. run focused and whole-crate verification;
8. check verification timing and trust inventories.

That workflow converts proof effort into infrastructure instead of accumulating
one-off assertions.

## Chapter 21 — Protocol, Scheduler, Runtime, and FFI Integration

A protocol is runnable only when its logical actions, concrete transitions, scheduler,
wire format, host, service entry, and FFI dispatch agree. Treat this as an interface
chain; test each link.

### Standard protocol shape

For a new non-RSL protocol, start with logical types and actions, annotation and config,
generated types/functions, a wire message, a host, and a service entry:

```text
src/protocol/NewProtocol/
src/generated/NewProtocol/
src/implementation/NewProtocol/{host.rs,message.rs,...}
src/services/NewProtocol/main_i.rs
```

Register modules in the surrounding `mod.rs` files. The generic runtime expects the
host's message type to implement `ProtocolMessage`, its configuration to implement
`ProtocolConfig`, and the host to implement `ProtocolHost`.

### From `LNext` to scheduler actions

`LNext` is generally a disjunction of action predicates, sometimes with existential
parameters. `analyze-lnext` extracts this structure and classifies actions using the
configuration's message declarations and overrides:

```bash
cargo run --manifest-path transpiler/Cargo.toml -- analyze-lnext \
  --input src/protocol/Paxos/paxos.rs \
  --config src/protocol/Paxos/paxos_transpile.toml
```

The host must supply existential values from a real runtime source: a message field, the
sender endpoint, current state, a timer, or a deliberate choice. Never substitute a
placeholder merely because it satisfies a Rust type.

Current scheduler configuration distinguishes:

- message-driven actions and their message variants;
- timer-driven actions;
- role-dispatched actions selected by configuration index or a state field;
- flag injections for protocols that model received information in state fields;
- guard checks that return a no-op when an action is disabled.

`generate-host` produces a scaffold from `[messages]` and `[scheduler]`. Review every
TODO and guard. Scheduling policy affects liveness and performance even when each
individual action refines its spec.

### Wire messages and concrete messages

The generated `CMessage` used by verified transitions and the runtime wire enum need not
be the same Rust type. Hosts commonly provide `to_wire` and `from_wire` conversions.
For each variant, verify:

- tags are unique and stable;
- field order, widths, signedness, and endianness match serialization;
- deserialization checks length before indexing;
- invalid tags and malformed payloads fail safely;
- endpoint and node identifiers use the intended mapping;
- round-trip tests cover every variant.

`generate-messages` and `generate-marshalable` reduce repetition when their configured
formats fit, but generated serialization is still part of the runtime boundary and
requires tests.

### Host responsibilities

`ProtocolHost::next` receives either a packet or a timeout. A sound host should:

1. reject or ignore wire messages that cannot become the expected concrete message;
2. check the action's runtime guard;
3. call exactly the generated transition associated with that action;
4. update state according to the selected calling convention;
5. translate every logical/concrete outbound message into the intended wire packet;
6. preserve source and destination identity;
7. return failure only according to the service policy.

For functional transitions, assign the returned state once. For `&mut self` transitions,
avoid an additional clone/rebuild layer. Do not infer outbound messages by diffing state
unless that inference is a documented and tested part of the host contract.

### Service and generic dispatch

The service entry parses the endpoint/configuration data, initializes the host, and
runs the generic network loop. `protocol_main_wrapper` currently recognizes:

```text
rsl, twophase, leaderelection, primarybackup, chainreplication,
paxos, verticalpaxos, raft, pbft, epaxos
```

Add a new protocol consistently to Rust module declarations, the wrapper match,
supported-name diagnostics, the C# server usage/validation text, and SCons project
targets where applicable. Add a dispatch test so those lists cannot drift silently.

The generic benchmark client currently supports only Raft, Primary-Backup, PBFT, and
EPaxos. A server dispatch entry does not mean an end-user client workflow exists.

### FFI ownership and failure paths

The C# server supplies callbacks for endpoint discovery, time, receive, and send. Rust
exports allocation/free helpers and the protocol wrapper. Any signature change must be
made atomically on both sides. Test at least:

- zero-length and oversized buffers;
- invalid UTF-8 protocol names;
- malformed endpoint bytes;
- receive timeout and receive failure;
- deserialization failure;
- send failure;
- allocation ownership on early returns;
- unknown protocol names and return codes.

The FFI functions are external/trusted from Verus's perspective. Rust type checking does
not protect a mismatched C# delegate layout.

### I/O logs and packet identity

RSL specifications model I/O sequences more explicitly than the generic host. The
architectural risk is a correspondence asserted between packets returned by a protocol
action and send events recorded by an external runtime. The strongest design constructs
both from one verified value. When the runtime supplies the log independently, the
correspondence is a trust boundary unless a checked contract bridges it.

Current generated RSL dispatch includes external-body fallback sites rather than the
old packet-identity `assume` inventory described by historical phase documents. Audit
the source, not those old counts, before changing or describing the boundary.

### Integration checklist for a new protocol

Before calling a protocol integrated:

- logical `LInit`/`LNext` and action tests exist;
- annotation and config validate;
- types/functions regenerate reproducibly;
- generated code verifies with its intended trust inventory;
- every wire variant round-trips;
- scheduler branches cover intended `LNext` actions;
- message and timeout paths run in host tests;
- service and FFI dispatch recognize the protocol;
- SCons builds required binaries;
- a cluster smoke test reaches a meaningful state change;
- model-check support/status and limitations are documented accurately;
- the protocol/trust matrix is updated with a dated audit.

## Chapter 22 — Source-First Model Checker Internals

The source-first checker evaluates the protocol relation written in Verus syntax. It is not a
second implementation of the generated executable protocol, and it does not call Verus's SMT
solver. A change to this subsystem therefore has two obligations: preserve the intended
finite-state semantics and preserve the evidence boundary exposed in reports.

The implementation is centered in
[`transpiler/src/modelcheck/`](../transpiler/src/modelcheck/mod.rs), with CLI orchestration and
report construction in [`transpiler/src/main.rs`](../transpiler/src/main.rs). A useful dataflow
is:

```text
protocol.rs + types.rs
        │ parse and resolve LInit/LNext/helpers/types
        ▼
ProtocolSourceBundle + SpecSchema
        │                     model.toml
        │                         │ parse, override, validate
        ├─────────────────────────┘
        ▼
finite RuntimeValue domains + initial states + TransitionIr
        │
        ▼
direct branch solver ──fallback──► bounded candidate evaluator
        │
        ▼
BFS / DFS / DPOR ─► invariant/deadlock checks ─► optional graph/liveness
        │
        ▼
human report / JSON / parity artifacts / checked-in evidence
```

### Source ingestion and entrypoint resolution

The spec analyzer reads the protocol and type sources into one
`ProtocolSourceBundle`. The bundle contains parsed spec functions, a type schema, source paths,
and resolved entrypoints. Model checking fails early if the requested `--init`, `--next`,
invariant, or liveness predicate cannot be resolved unambiguously.

Keep this stage distinct from evaluation support. The Verus parser can represent more
expressions than the runtime evaluator can execute, just as the TLA+ parser can represent more
than either translator preserves. Adding a parser AST variant without adding evaluation,
domain, bytecode, and reporting support is a valid incremental change, but its unsupported
boundary must stay explicit.

The entrypoint convention is relational: the initial predicate constrains a concrete state and
constants value, and each `LNext` branch constrains current state, next state, constants, and
possibly additional existential parameters. Extra `LNext` parameters beyond the recognized
state/state_/constants prefix are expanded as transition-level existential choices.

### Configuration and domain resolution

[`config.rs`](../transpiler/src/modelcheck/config.rs) is the schema authority. Serde applies
defaults, CLI overrides replace selected limits/domains, and validation runs again after the
overrides. Validation is semantic as well as syntactic: it rejects assignment/domain overlap,
empty and duplicate names, invalid ranges, zero collection/search limits, duplicate liveness
obligations, fairness-label duplication, deadlock with stuttering, and deadlock with the
invisible-branch POR heuristic.

[`domain.rs`](../transpiler/src/modelcheck/domain.rs) recursively turns Verus types into finite
`RuntimeValue` domains. Primitive domains come from the config; named aliases, structs, and
enums come from the source schema; tuples and containers form finite cross-products. Expansion
has its own failure modes before exploration: recursive types are depth-limited, unsupported
generic forms are rejected, and candidate counts are bounded by the larger of `max_states` and
the candidate-evaluation guardrail.

Constants deserve special care. The checker constructs candidate `LConstants` values, filters
or synthesizes them using assignments and domains, and runs the model once per matching
valuation. Summary counts aggregate across valuations, while the retained detailed execution
is the first violation, otherwise the first incomplete run, otherwise the first successful
run. A change to aggregation must keep `constants_valuations_total` and
`constants_valuations_explored` meaningful and must not hide a later violation behind an early
successful valuation.

### Initial-state construction

[`init.rs`](../transpiler/src/modelcheck/init.rs) analyzes `LInit`; the orchestration layer also
recognizes pinned field equalities and constants-dependent assignments. When direct extraction
does not determine a complete state, the checker can evaluate candidates from the finite state
domain. The same principle used for successor solving applies here: derive values directly when
the relation gives them, enumerate only the unresolved remainder, and refuse an expansion whose
size defeats the configured guardrail.

Initial states are deduplicated before entering the frontier. A defect here changes every
downstream count and can masquerade as a transition bug, so parity tools compare initial-state
sets separately from the rest of the graph.

### Transition IR and branch solving

[`ir.rs`](../transpiler/src/modelcheck/ir.rs) lowers `LNext` into labeled branches. A branch
records next-state equalities, predicate constraints, and existential variables. The labels are
observable: they appear in traces, fairness configuration, telemetry, DPOR action identities,
and parity edges. Treat label stability as part of the report schema.

[`solver.rs`](../transpiler/src/modelcheck/solver.rs) first tries direct assignment. Equalities
such as `s_.field == expression` populate a next-state value, and remaining predicates are
checked against it. This avoids enumerating every possible `LState`. Helper-wrapped relations
can also take the direct path when the helper exposes a compatible `LStep(s, s_, c)` shape.

If no complete assignment can be derived, the solver evaluates bounded candidate states. The
per-state/per-branch `candidate_eval_guardrail` stops a relational shape from silently becoming
an enormous brute-force search. Guard predicates are evaluated as early as possible to prune
existential assignments and candidates. The branch telemetry records which route was used,
candidate counts, guard pruning, equality/predicate counts, evaluator calls, successes, and
fallback reason. Any new solver optimization should keep a slow reference route available in
tests and demonstrate successor-set parity before being enabled generally.

No-successor handling is applied after all branches have been solved. Under stuttering
semantics the orchestrator adds a labeled `stutter` self-loop; under deadlock semantics it
returns the empty set. That distinction must be identical in sequential and parallel paths.

### Runtime values and expression evaluation

[`value.rs`](../transpiler/src/modelcheck/value.rs) defines the executable value universe:
unit, booleans, signed integers, naturals, strings, tuples, sequences, sets, maps, structs, and
enums. Constructors enforce configured collection bounds. Canonical keys recursively include
type/variant/field information and sort unordered structures, which makes them suitable for
stable identity and reports.

[`evaluator.rs`](../transpiler/src/modelcheck/evaluator.rs) interprets the supported Verus AST.
It provides explicit hooks for function calls, method calls, and quantifier domains so the
orchestrator can resolve helpers against the ingested bundle. Helper evaluation is recursive
but bounded; zero-argument helper caching is reset at run boundaries to avoid carrying values
between protocols.

The execution dispatch has three layers:

1. With `--native-codegen`, supported expressions are compiled into native dynamic libraries.
2. Otherwise, or on native fallback, the default bytecode cache compiles supported expressions
   once and reuses them.
3. Unsupported compilation shapes fall back to the AST evaluator.

All three paths must agree on value, error, bounds, and short-circuit behavior. A performance
change is not ready when it merely makes a fixture faster; add dispatch-parity tests for success
and failure cases. Division/modulo by zero, bad indexing, type mismatch, failed casts, and an
unresolved helper are semantic results that must not be optimized away.

### Ordinary BFS and DFS

[`explorer.rs`](../transpiler/src/modelcheck/explorer.rs) owns ordinary frontier exploration,
deduplication, invariant/deadlock stops, and parent links for safety traces. BFS pops from the
front and DFS from the back, but both add successor states in deterministic branch order and
deduplicate globally.

At `max_depth`, a state is recorded and checked for invariants but its successors are not
generated. Once those frontier items have been consumed, the stop reason is
`FrontierExhausted`; there is no separate “depth bound reached” reason. Report consumers must
therefore compare `summary.depth` with `search.max_depth` before calling the graph closed.
Deadlock is checked only below the depth cutoff, because an unexpanded boundary state has an
unknown successor set.

Sequential exploration checks timeout around frontier, invariant, and successor work and also
passes a cooperative timeout hook to candidate solving. Parallel BFS uses level-synchronous
workers and fresh immutable closures rather than the sequential mutable successor cache and
telemetry capture. Preserve state-set and violation parity tests when changing either route;
telemetry equality is not expected when the implementation deliberately omits shared mutable
instrumentation.

### State identity, symmetry, and POR

Ordinary canonical dedup stores the full normalized key and preserves distinctions represented
by `RuntimeValue`. `hash_compaction64` stores a 64-bit key; a collision can suppress a distinct
state. The explorer tracks observed hash collisions when it retains a representative canonical
key, but no counter can recover a behavior already merged.

Symmetry normalization rewrites selected top-level fields before dedup. The implementation does
not prove that the selected identities are permutable in the protocol or properties. That is a
modeling premise supplied by the user, which is why the report marks every such run lossy.

[`por.rs`](../transpiler/src/modelcheck/por.rs) implements the separate invisible-branch
heuristic. Its visibility argument is syntactic and property-dependent. Extending it requires a
false-negative-oriented design: an uncertain dependency must retain the branch. Keep deadlock
checking incompatible unless the reduction acquires a deadlock-preservation argument and tests.

### Integrated DPOR

The integrated DPOR implementation lives in
[`modelcheck/dpor/`](../transpiler/src/modelcheck/dpor/mod.rs). `enabled.rs` enumerates concrete
enabled transitions from the same source bundle and solver semantics. `types.rs` defines process
and action identities, vector clocks, transition footprints, and path-aware conflicts.
`explore.rs` implements iterative DFS, backtrack sets, sleep sets, invariant checks, a shared
state store, and parallel frontier/work-stealing execution.

Independence is conservative at the footprint level: unknown footprints and same-process steps
are dependent, and any write/read or write/write path overlap conflicts. The optional conflict
profile is diagnostic. Runtime observations that a statically written field did not change are
useful for finding overly coarse footprints, but turning observations into an independence
override changes the reduction argument and needs dedicated parity evidence.

The CLI adapter in `main.rs` is currently less expressive than `DporResult`. It converts only
counts and a coarse stop reason into `ExplorationResult`, drops the retained state values and
witness details, does not expose max-depth/max-state termination, and has no timeout in
`DporConfig`. The DPOR state store also uses fingerprints as an authoritative fast path. These
are integration gaps, not details to paper over in documentation. A repair should introduce an
explicit DPOR termination enum, retain or stream enough state/edge data for consumers, propagate
witnesses, apply timeout, and update the evidence classifier before enabling DPOR for liveness
or parity artifacts.

### Invariants, deadlocks, and traces

[`invariant.rs`](../transpiler/src/modelcheck/invariant.rs) resolves selected boolean predicates
and evaluates them on each reached state. Ordinary exploration records the first failing
invariant, state, depth, and parent chain. The internal `ExplorationResult` has a complete
action-labeled counterexample trace, although the current JSON invariant/deadlock payload emits
only the failing state key and depth. Adding the omitted trace to JSON is a schema change and
should be accompanied by stable serialization tests and regenerated artifacts.

A deadlock is a reached state below `max_depth` with an empty successor set under deadlock
semantics. It is not necessarily a protocol bug: finite models often encode intentional
terminal states. Property selection must decide whether termination is allowed.

### Graph construction, liveness, and fairness

For ordinary exploration, [`graph.rs`](../transpiler/src/modelcheck/graph.rs) indexes retained
states and reconstructs action-labeled edges by solving successors again. The graph includes
depth and initial-state metadata. [`liveness.rs`](../transpiler/src/modelcheck/liveness.rs)
resolves `from`/`to` state predicates, computes cyclic SCCs, applies branch-label fairness, and
builds a shortest prefix plus representative cycle edge for the first violation.

The present algorithm flags a component that contains a `from` state, contains no `to` state,
and survives fairness filtering. Weak and strong fairness are approximated at SCC granularity
using enabled and internal-edge label sets. This makes the feature valuable for bounded cycle
diagnosis but weaker than full temporal model checking. Because graph analysis runs when the
ordinary stop reason is `FrontierExhausted`, the depth-cutoff caveat applies directly. A future
termination schema should distinguish a truly closed finite graph from a graph truncated at
depth.

### Reports, parity, and evidence integrity

`main.rs` constructs the JSON document explicitly; it is therefore part of the public interface
even though it is not yet represented by versioned Serde structs. Appendix E lists the current
fields. Keep result labels, stop reasons, branch labels, canonical state keys, and evidence-mode
semantics backward-compatible or make a deliberate schema migration.

`parity.rs` contains streaming debug export support, while the current ordinary
`--export-parity` branch in `main.rs` independently writes only deduplicated `states.jsonl`.
Avoid fixing one exporter and assuming the other changed. Cross-engine comparisons use the
canonical JSON `state` payload because IDs can be encoded differently by TLC and source-first
tools.

The matrix script rebuilds the binary, runs pinned BFS fixtures, and rewrites report artifacts.
The drift guard normalizes only documented host-dependent timing fields and Git revision. A new
report field will therefore fail the guard until reviewed and committed. That friction is
intentional: evidence should change in the same commit as the semantics that changed it.

### Safely add a construct or optimization

Use the narrowest layer that owns the behavior:

1. Add parser/spec-analyzer tests for the source shape.
2. Add runtime-value and domain tests if it introduces a new type or finite domain.
3. Add AST evaluator tests for value and error cases.
4. Add bytecode and native parity tests if those engines can compile it; otherwise test clean
   fallback.
5. Add transition-IR and direct-solver tests for relational use.
6. Compare successor sets against candidate enumeration.
7. Compare BFS and DFS reached states on a closing fixture.
8. For a reduction, compare against canonical unreduced BFS on adversarial dependency cases.
9. Add violation, cap, timeout, and depth-bound report tests.
10. Regenerate the checked-in matrix and review normalized drift.

Never improve a benchmark by silently shrinking a domain, replacing an unsupported predicate
with `true`, merging states without classifying the run as lossy, or translating a cap into
`FrontierExhausted`. Those changes optimize the claim away rather than the checker.

## Chapter 23 — TLA+ Translation and Round-Trip Internals

The translation subsystem contains two TLA+ → Verus pipelines and one Verus → TLA+ pipeline.
They share syntax infrastructure but have different semantic contracts. Contributors should
resist the temptation to route all three through one permissive “universal translator”: the
clean projector's value is precisely that it refuses inputs whose distributed meaning cannot
be recovered mechanically.

### Tokenizer, parser, and AST

The TLA+ frontend is under [`transpiler/src/tla/`](../transpiler/src/tla/mod.rs).
[`tokenizer.rs`](../transpiler/src/tla/tokenizer.rs) records spans used by parse and linter
diagnostics. [`parser.rs`](../transpiler/src/tla/parser.rs) builds the structures in
[`ast.rs`](../transpiler/src/tla/ast.rs).

The module AST represents a module name, `EXTENDS`, constants, variables, assumptions,
operators, theorems, and instances. Expression variants cover literals, primes, boolean,
arithmetic and set operators, operator/function application, sets and comprehensions,
functions and `EXCEPT`, records and record sets, tuples, quantifiers, `LAMBDA`, `CHOOSE`,
conditionals, `CASE`, `LET`, `UNCHANGED`, `ENABLED`, temporal operators, and fairness.

That list is parser coverage, not translation coverage. For example, the general translator
renders multi-binder set comprehensions and `LAMBDA` as unsupported comments, and module
assumptions/theorems/instances are not emitted into generated Verus. TLAPS proof bodies after a
theorem are skipped rather than preserved. Tests and support tables must name the downstream
stage they exercised.

### The general global-model translator

The `translate-tla` route is:

```text
tokens → TlaModule → TypeInference (+ optional .tla-types) → ModuleTranslator
       → Verus state/constants/record types and spec functions
       → optional source-shaped .automan
```

[`types.rs`](../transpiler/src/tla/types.rs) infers types from declarations and expression use.
Explicit annotations override variable, constant, and operator entries, after which unresolved
variables are resolved with fallbacks. Fallback is necessary to emit Rust syntax, but it is
also where a semantically unknown TLA+ value can acquire an unjustified scalar or collection
shape. Keep inferred/fallback origin visible in diagnostics when extending the type system.

[`translator.rs`](../transpiler/src/tla/translator.rs) first collects record shapes and symbolic
atoms, emits imports and state/constants definitions, classifies operators as constants,
predicates, or actions, propagates that classification through calls, infers signatures, and
prints each operator body. An action receives current and next state parameters; predicates
receive current state; constants are threaded where needed. The generated-D1 normalization
path contains deliberate recovery heuristics for TLA+ previously emitted from Verus, including
`arbitrary()` placeholders for unresolved external values. Those heuristics improve compilation
coverage but weaken preservation claims.

Expression translation handles representative boolean, arithmetic, set, sequence, map, record,
quantifier, and control-flow forms. Context matters. `Head` and `SubSeq` have explicit
one-indexed-to-zero-indexed rewrites, whereas generic function application cannot decide whether
its operand is a TLA+ sequence or function and emits direct indexing. Function-set membership
can become a type-shaped tautology. Temporal constructs become marker calls rather than proof
obligations. Action composition emits a comment plus conjunction. Unsupported placeholders must
be treated as diagnostics to review, not harmless formatting.

### The clean-subset projector

The `tla-lint`/`clean-tla` route reuses tokens, parser, and AST, then intentionally diverges:

```text
TlaModule
   ├── clean_subset.rs: infer nodes/network and enforce C1–C5
   └── projection.rs + action_projection.rs: delete node dimension,
       project messages/actions/types, synthesize frame conditions
             │
             └── emit.rs: all-or-nothing protocol-layer Verus spec
```

[`clean_subset.rs`](../transpiler/src/tla/clean_subset.rs) is both checker and diagnostic
contract. Every finding should explain the design decision a human must make. Adding a syntax
case is not enough: positive and negative corpus guards pin rule names and exact finding counts.

[`projection.rs`](../transpiler/src/tla/projection.rs) carries typed projected state,
constants, messages, helpers, and actions. [`action_projection.rs`](../transpiler/src/tla/action_projection.rs)
recognizes send/receive/discard patterns and turns global network mutation into action inputs and
packet outputs. [`emit.rs`](../transpiler/src/tla/emit.rs) either emits the full result or returns
a list of gaps. It must never substitute `arbitrary()` for a missing projected conjunct: this
pipeline's guarantee comes from refusal.

The clean projector is not responsible for inventing messages for C2 violations, proving the
human rewrite faithful, generating executable functions, or generating proofs. The corpus
separates those responsibilities through lint guards, projection/golden tests, optional Verus
typechecking, and finite TLC observable-state comparisons.

### Mode annotations and the spec-to-exec boundary

The mode-annotation generator in
[`translator.rs`](../transpiler/src/tla/translator.rs) analyzes source operator signatures:
input parameters use `+`, outputs use `-`, and actions are distinguished from initializers and
predicates. The general pipeline consumes these `.automan` annotations to choose executable
witnesses.

Projection changes signatures by removing the acting node and replacing network state with
message inputs/outputs. Source-shaped annotations are therefore invalid for projected output.
The current `pipeline --clean-subset` writes them but stops before exec generation. A correct
implementation of projected mode generation should derive modes from `ProjectedModule`, add
golden tests for parameter order and polarity, and only then enable the exec stage.

Even on the general path, mode-correct code generation is not verification. The default
pipeline assumes generated postconditions, and proof generation is opt-in elsewhere. Integration
tests should distinguish “transpilation succeeded,” “Verus typechecked,” and “all proof
obligations verified without unexpected assumptions.”

### Verus spec extraction and TLA+ emission

The reverse route is under
[`transpiler/src/verus2tla/`](../transpiler/src/verus2tla/mod.rs). The normal Verus parser
extracts spec functions; the type parser separately extracts structs, enums, aliases, and
function signatures. [`converter.rs`](../transpiler/src/verus2tla/converter.rs) registers types,
converts supported function bodies to the shared TLA+ AST, and detects direct self-recursion.
[`printer.rs`](../transpiler/src/verus2tla/printer.rs) renders that AST.

Default output extends `Integers`, `Sequences`, and `FiniteSets`. Named types used by parameters
may become TLA+ constants; registered structs and enums generate type-shaped operators. Prefix
stripping is conservative: the configured prefix is removed only before an uppercase character.

The converter erases spec/exec views and casts, turns struct updates into `EXCEPT`, sequence
literals into TLA+ tuples, set literals into enumerations, and recognized sequence/set/map
methods into built-ins. Some conversions are approximations: an empty map is represented with
an empty tuple, a populated map literal with a set of key/value tuples, enum tests with a `tag`
field, and a missing `else` with `TRUE`. Default handling turns an unknown method into an
operator whose receiver is its first argument. Each approximation needs either a documented
target convention or a refusal; silently mixing encodings makes round-trip comparison
meaningless.

Only function bodies travel through the current converter. Verification metadata and proof code
do not. The `include_recommends` configuration is presently unused after CLI construction. Add
a focused failing test before implementing it; otherwise the flag can continue to promise an
artifact it does not produce.

### Canonicalization and structural comparison

[`roundtrip/canonical.rs`](../transpiler/src/roundtrip/canonical.rs) normalizes representational
differences such as the `L` naming prefix, inequality shape, and record-field order.
[`roundtrip/compare.rs`](../transpiler/src/roundtrip/compare.rs) reports AST differences with
paths. These are library utilities used by tests; there is no CLI command that certifies a
semantic round trip.

Canonical equality is structural equality under configured rewrites. It can establish that two
supported AST fragments have the same normalized shape. It cannot recover an ignored
assumption, prove an `arbitrary()` placeholder equal to the original expression, compare
unbounded behaviors, or validate a function/map encoding. Keep “canonical,” “structural,” and
“semantic” separate in test names and documentation.

### Relational TLC wrappers

[`mc_wrapper.rs`](../transpiler/src/tla/mc_wrapper.rs) adapts relational modules to TLC. It
parses the source module, creates wrapper variables and zero-argument initial/next operators,
optionally lifts relational packet outputs, and emits a `.cfg` skeleton with requested
invariants. Golden wrapper fixtures pin formatting and operator wiring.

Wrapper generation is another translation boundary. A packet mode changes state and transition
semantics; a cfg constant assignment changes the finite model. Cross-engine tests must retain
both generated wrapper and filled cfg, not just the final state counts.

### Testing claims by layer

The existing test suites supply different evidence:

- parser unit tests and `corpus_parse_guard.rs` show that named source files build an AST;
- `tla_examples_test.rs` and `roundtrip_test.rs` check generated declarations, expression
  snippets, action classification, and annotations for curated modules;
- the clean lint/projection guards test C1–C5 decisions and projected shapes;
- `corpus_v3_guard.rs` byte-compares projector output with frozen generated blocks;
- `corpus_v1_guard.rs` typechecks goldens only when a Verus binary is available;
- the corpus TLC script compares finite observable state sets for cases with a declared common
  projection;
- reverse-conversion integration tests prove that selected files can be converted and parsed,
  but some are skipped when a prebuilt binary or generated workspace is absent; and
- ignored or skip-on-missing tests are evidence only when their prerequisites were present in
  the recorded run.

Do not derive a feature table from test function names alone. Read whether the test executes a
full conversion, merely checks a substring, returns early on a missing tool, or acknowledges
future work. Appendix D uses conservative stage-specific status for exactly this reason.

### Add a TLA+ or Verus construct end to end

For a TLA+ construct, proceed in layers:

1. Add tokenizer and parser positives, precedence cases, and malformed negatives with spans.
2. Add the AST variant to every traversal, canonicalizer, printer, and free-variable/type walk.
3. Decide whether the general translator preserves, approximates, marks, or rejects it.
4. Decide independently whether the clean linter permits it and how projection transforms it.
5. Add type-inference and explicit-type-override cases.
6. Add generated Verus typechecking, not just text assertions.
7. If exec generation applies, add mode and spec-to-exec tests and audit assumptions.
8. If reverse conversion applies, define one data encoding and add normalized structural tests.
9. If semantic preservation is claimed, compare a finite model's observables or transition
   graph and state the limits.

For a Verus construct, start with the Verus parser and converter error policy, then add the same
printer, canonicalization, reverse-parse, and semantic checks. Unsupported is safer than a
plausible expression with different meaning. The desired failure mode is a precise diagnostic
that tells the contributor which layer is missing.

## Chapter 24 — Testing, CI, and Evidence Integrity

The test suite protects four different products: the transpiler, the checked-in
generated code, the verified crate, and the executable services. A passing test in one
product cannot substitute for a missing gate in another.

### Authoritative CI gates

`.github/workflows/ci.yml` is the current contract. Its jobs cover:

| Job | Main evidence |
|---|---|
| Test | Builds the transpiler, rebuilds model-check/DPOR corpus data, regenerates and runs the quickstart, and runs Cargo tests. |
| Lint | Runs Clippy over all targets and features with warnings denied. |
| Format | Checks Rust formatting. |
| Verus Verification | Installs the pinned Verus/Rust pair, runs the SCons Verus build, captures trigger and timing inventories, applies guards, and verifies/runs the quickstart. |
| Model-Check Evidence Drift Guard | Rebuilds the checked-in source-first matrix, normalizes volatile report fields, checks structural drift, and validates manifest/evidence paths. |

Read the workflow before claiming that a local wrapper reproduces CI. In particular,
`scripts/run_ci_local.sh` is useful but does not currently mirror every quickstart,
normalization, trigger, timing, and drift step.

### Test the smallest responsible unit

Put a regression where the defect first became observable:

- parser and type errors belong in module unit tests;
- unsupported lowering belongs in translator/codegen positive and negative fixtures;
- `.automan` data-flow failures belong in mode/checker tests;
- TOML interactions belong in configuration resolution tests;
- a real protocol generation bug also needs a checked-in regeneration parity test;
- evaluator and finite-domain bugs belong in model-check unit tests with a minimal
  protocol fixture;
- wire changes need per-variant round trips and malformed-input tests;
- scheduler changes need packet, timeout, guard, and role-dispatch tests;
- FFI changes need an integrated process or cluster test in addition to compilation.

A negative test should assert the stable semantic part of the diagnostic, not an
incidental byte offset or complete debug rendering.

### Generated-output parity

Parity tests generate into a temporary directory and compare with checked-in output.
They should use the same ordered input set and configuration as the real regeneration
script. A good parity failure tells the reviewer which input/config/output tuple
drifted; it should not overwrite the expected file.

After a transpiler change, run the focused parity test and inspect the diff before
updating artifacts:

```bash
cargo test --manifest-path transpiler/Cargo.toml \
  regen_matches_checked_in -- --test-threads=1
git diff -- src/generated
```

If the change is intentionally global, regenerate all protocols and review by
generator feature rather than accepting a bulk diff on faith.

### Source-first model-check evidence

The checked-in CI matrix is produced by:

```bash
scripts/run_model_check_matrix.sh
python3 scripts/check_model_check_drift.py
```

The matrix currently contains small and safety-invariant runs for TwoPhase,
PrimaryBackup, LeaderElection, and Paxos, plus guard-pruning and liveness fixtures.
PBFT is attempted separately on a best-effort basis because candidate expansion can
exceed limits on CI runners. Other protocols have reproducible blocker fixtures or
experimental profiles; they are not silently equivalent to a successful bounded run.
See [`model_checker_status.md`](model_checker_status.md) for the current per-protocol
record.

Every model-check artifact should make these facts recoverable:

1. source and type files;
2. resolved `model.toml` values and finite domains;
3. init/next functions and selected invariants/liveness properties;
4. search strategy and implementation profile;
5. depth, state, candidate, and timeout bounds;
6. result and stop reason;
7. explored-state/transition counts and relevant telemetry;
8. generator command and source revision.

`scripts/run_model_check_matrix.sh` rebuilds the debug binary before running and writes
a manifest. The drift checker normalizes only declared volatile data such as elapsed
times and the Git revision. Do not normalize state counts, property results, search
semantics, or resolved domains merely to make a diff pass.

### Interpret bounded results correctly

Use language tied to the report:

- **exhausted finite model, property held**: all states in that resolved finite model
  were explored and no violation was found;
- **bounded/limited run, property held so far**: no violation was found before a depth,
  state, candidate, or time limit;
- **violation**: preserve the trace and determine whether it is a protocol defect, a
  modeling abstraction, or an evaluator defect;
- **unsupported/configuration error**: the intended model was not explored;
- **skipped/best effort**: no successful result exists for that run.

An invariant failure caused by a deliberately message-free abstraction is still a real
result of that model. Explain the abstraction; do not relabel the run as passing.

### Quickstart as a documentation test

`examples/quickstart/` is both an example and an API compatibility test. CI regenerates
it, verifies it, and runs it. When changing CLI flags, generated imports, or default
contracts, update the quickstart source and its documented command in the same change.
Prefer examples that start from source inputs; do not check in unexplained output that
cannot be regenerated.

### Failure triage

When a gate fails, preserve the first meaningful failure:

1. rebuild the exact binary used by the test;
2. rerun the smallest failing test with output visible;
3. distinguish semantic output drift from formatting drift;
4. for Verus, identify the first failed assertion/module before raising resource
   limits;
5. for model checking, inspect the resolved model and stop reason before comparing
   counts;
6. for CI-only failures, reproduce its OS, versions, features, and generated-corpus
   steps;
7. fix the source of truth and rerun the adjacent gate, then the full affected job.

Do not update a golden artifact until the new semantics have been reviewed.

### Adding or changing a CI gate

A durable gate has a focused script/test, a clear artifact, and a wiring test when its
absence could look like success. It must fail on the intended regression, not on normal
machine noise. Keep capture and enforcement separate when useful: CI can upload a
trigger inventory even if verification fails, while a later guard decides whether its
contents regress.

## Chapter 25 — Performance and Solver Diagnostics

tla-rs has three independent performance surfaces: generated/runtime execution,
bounded state exploration, and SMT-backed verification. Measure the surface you are
changing; an optimization in one can make another worse.

### Record a reproducible baseline

For any performance claim, record:

- commit and dirty-tree status;
- Verus, Rust, .NET, SCons, OS, CPU, and memory versions where relevant;
- protocol configuration, node count, client threads, duration, and payload;
- generation options such as functional versus mutable-state lowering;
- warm-up policy, number of trials, and the statistic reported;
- raw output or a machine-readable artifact.

Use repeated trials and report distribution or at least median/minimum with the raw
samples. Historical throughput numbers in the README are snapshots on a particular
machine, not acceptance thresholds.

### Runtime profiles

RSL has a dedicated server/client path and benchmark workflow. The generic benchmark
script accepts `raft`, `pb`, `pbft`, and `epaxos`; those are the protocols understood
by the current generic client. Do not benchmark another generic server by pretending
one of those wire protocols is compatible.

Functional generated transitions clone or reconstruct state. `arc_wrap_types` and
`arc_wrap_fields` can make unchanged non-scalar fields shallowly shared while keeping
the functional convention. `mut_self_types` instead lowers eligible state transitions
to `&mut self`. The resolver treats these approaches as incompatible and clears Arc
wrapping for mutable-self types. Benchmark the complete host path after either change:
state allocation can move out of a generated function into message conversion or
scheduler glue without disappearing.

When measuring a service, separate at least:

- protocol transition time;
- serialization/deserialization;
- FFI crossings and allocation;
- C# receive/send loop;
- batching and client concurrency;
- cryptography or certificate setup when enabled.

Throughput without latency, error rate, completed-operation semantics, and server logs
can hide overload or dropped requests.

### Model-checker profiles

Use the same resolved model when comparing explorer implementations. `model-check`
supports BFS, DFS, and DPOR search, optional bytecode bypass, native code generation,
parallel workers, and conflict profiling. Change one dimension at a time:

```bash
cargo run --manifest-path transpiler/Cargo.toml -- model-check \
  --input src/protocol/Paxos/paxos.rs \
  --types src/protocol/Paxos/types.rs \
  --model transpiler/tests/model_check_fixtures/paxos_small.model.toml \
  --search dpor --workers 1 --conflict-profile --json-report
```

Compare result, stop reason, distinct states, transitions, and property outcomes before
comparing elapsed time. A faster run that pruned reachable states incorrectly is a
semantic regression. Keep the DPOR parity corpus current when conflict/independence
logic changes.

Candidate construction, existential enumeration, successor solving, canonicalization,
deduplication, and liveness-cycle analysis have different bottlenecks. Use the JSON
telemetry and branch/conflict profiles to optimize the dominant component instead of
guessing from total wall time.

### Verus timing and trigger inventory

Capture an inventory with the same verifier and trigger mode on both sides:

```bash
scripts/collect_trigger_inventory.sh \
  --verus-path /path/to/verus/verus \
  --triggers-mode all-modules \
  --label "baseline"

scripts/trigger_inventory.py diff base.json candidate.json \
  --fail-on-regression
scripts/trigger_sites.py src --repo-root . --json -o trigger-sites.json
```

`selective`, `all-modules`, and `verbose` inventories are not interchangeable. The
trigger diff detects additions and changed choices, not only a total count.

For solve-time comparisons, capture `--time-expanded`, parse several runs, and merge
both baseline and candidate using the same method:

```bash
scripts/verus_timing.py parse run-1.log -o run-1.json
scripts/verus_timing.py merge run-1.json run-2.json run-3.json -o merged.json
scripts/verus_timing.py diff baseline.json candidate.json \
  --max-regression-pct 20 --fail-on-regression
```

Parallel module verification is noisy. Follow the sample count and noise-floor policy
in [`phase54-trigger-workflow.md`](phase54-trigger-workflow.md); do not compare a
single lucky baseline with a multi-run candidate. Large speedups also deserve review:
an over-restrictive trigger can make a goal fast because a needed instantiation never
occurs in a weakened or vacuous path.

### Diagnose `rlimit exceeded`

Treat an rlimit error as a symptom:

1. reproduce with the pinned toolchain and isolate the module/function;
2. compare automatic trigger notes with the baseline;
3. inspect new quantifiers, recursive unfolding, nonlinear arithmetic, and large
   disjunctions;
4. bind complex terms and lambdas before quantified assertions;
5. split branch and collection-extensionality reasoning into small lemmas;
6. add an explicit trigger only with a reason and inventory/timing evidence;
7. raise the limit only after the proof shape is understood and the cost is justified.

An rlimit increase is a resource-policy change. Include before/after timing and the
reason it is preferable to restructuring.

### Performance acceptance

Accept an optimization only when semantics, proof/trust inventory, and the relevant
performance metric all remain sound. The minimum comparison is:

```text
same logical behavior
same or stronger contracts
no new proof escape hatch
same wire/client semantics
measured improvement on repeated trials
no material verifier or model-check regression
```

## Chapter 26 — Verus Compatibility, Toolchain Upgrades, and Releases

A Verus upgrade is a verification migration, not a version-string edit. Parser rules,
vstd APIs, trigger selection, solver behavior, generated syntax, and the compatible
Rust toolchain can all change together.

### Locate every pin and compatibility claim

Start with a source search rather than a remembered list:

```bash
rg -n '0\.2026|rustc 1\.|VERUS_PIN|verus-x86|--verus-path' \
  .github README.md AGENTS.md docs scripts SConstruct
```

At minimum inspect `.github/workflows/ci.yml`, `AGENTS.md`, the README,
`scripts/verify_local.sh`, trigger/timing artifact metadata, and any cache keys or
download URLs. A checked-in report remains historical; label it with the old release
rather than rewriting its result as if produced by the new one.

### Establish the old-toolchain baseline

On a clean source state:

1. run format, Clippy, and full Cargo tests;
2. regenerate affected checked-in artifacts and confirm no drift;
3. run whole-crate verification with `--time-expanded`;
4. capture at least the documented number of timing samples and a trigger inventory;
5. run the quickstart verification/execution;
6. run runtime smoke tests if ABI or code generation may be affected.

Store the exact command, Verus commit/release, Rust version, OS, and stop status.

### Evaluate the candidate in isolation

Install the candidate beside the old release. Do not replace the only working verifier.
Confirm the candidate's stated Rust version and launcher/glibc requirements. Run the
smallest quickstart first, then the crate.

Classify failures before editing:

| Class | Typical response |
|---|---|
| Syntax/parser change | Update source or printer generically; add a generation fixture. |
| vstd/API change | Migrate imports/contracts and search all call sites. |
| Stricter proof obligation | Fix the proof or contract at its source; do not add a fallback. |
| Trigger-selection change | Compare inventories, add measured explicit triggers only where justified. |
| Solver/performance change | Isolate the module, gather repeated timing, and report a minimal reproducer upstream if appropriate. |
| Launcher/platform change | Update CI image and local compatibility instructions without bypassing verification. |
| Generated-output change | Fix the generator, regenerate, and run parity; never patch `src/generated/`. |

The guarded generated-text migration commands may help with an exact one-time syntax
migration, but the generator must still learn the new syntax so fresh output matches.

### Compare candidate evidence

Use identical trigger capture modes and symmetric timing samples. Run:

- full Cargo tests and regeneration parity;
- whole-crate Verus verification;
- trigger inventory diff and ceiling guard;
- merged per-module timing diff;
- quickstart generation, verification, and execution;
- relevant C# build and cluster smoke tests;
- model-check matrix only when parsing/evaluation/model semantics could have changed.

Review new warnings as future failures, especially automatic trigger notes and
deprecated vstd APIs. A green verification with new external bodies, assumptions, or
audit-classified source is not an equivalent result.

### Land the upgrade atomically

One upgrade change should update:

1. Verus release/commit and compatible Rust version in CI;
2. download URL, checksum or release identifier, cache keys, and CI runner image;
3. local verification defaults/instructions;
4. source, generator, and generated artifacts required for compatibility;
5. trigger ceilings/baselines only after reviewed evidence;
6. README, `AGENTS.md`, this book, and release notes;
7. an upgrade record with known warnings, trust deltas, timing deltas, and rollback
   instructions.

Do not mix unrelated protocol behavior into the upgrade. A narrow diff makes verifier
regressions bisectable.

### Release checklist

Before a tagged release or published artifact:

- the branch is clean and all checked-in generated output reproduces;
- CI format, lint, test, verify, and model-evidence gates pass;
- version/toolchain statements agree;
- server and applicable clients build and complete smoke tests;
- protocol support and trust/model-check matrices reflect current source;
- known assumptions, external bodies, FFI boundaries, and bounded-evidence limits are
  called out rather than hidden;
- commands in the README and quickstart run from a fresh checkout;
- release notes separate verified properties, bounded results, runtime tests, and
  experimental work.

If the candidate verifier introduces an unresolved soundness or reproducibility concern,
keep the old pin and publish the blocker. Compatibility pressure is not a reason to
weaken a proof boundary.

## Chapter 27 — Contributor Playbooks

These playbooks identify the usual source files, the evidence that must move with a
change, and the point at which the work is complete. Adapt paths to the protocol, but
do not skip a boundary because the initial edit was small.

### Add supported Verus syntax

1. Reduce the motivating construct to the smallest accepted/rejected source snippet.
2. Add parser and AST support in `transpiler/src/parser/` and `transpiler/src/ast/`.
3. Decide explicitly whether the construct is legal in spec, proof, and exec contexts.
4. Add printing/round-trip support if the AST can be emitted.
5. Add a positive test and nearby negative cases with stable diagnostics.
6. If it is executable, add mode, type, lowering, contract, and proof handling rather
   than letting it fall through to raw text.
7. Run focused tests, all Cargo gates, affected regeneration parity, and Verus.

The work is not complete when parsing succeeds but translation silently changes the
meaning or emits a proof fallback.

### Add a relational-to-functional template

1. Capture the logical predicate and expected executable shape in a fixture.
2. Express applicability in AST/mode/type terms in `templates`, `checker`, or
   `translator`; do not test a protocol name.
3. Reject close but unsound shapes: missing coverage, duplicate output assignments,
   non-injective removal mappings, or output use under an unsupported quantifier.
4. Generate the body, validity contract, refinement contract, and needed proof block.
5. Test functional and mutable-self forms if both can apply.
6. Regenerate the motivating protocol and inspect behavior, contract, trust, and cost.
7. Run whole-crate verification and timing/trigger checks for proof-heavy output.

### Fix a generated proof failure

1. Do not edit `src/generated/`.
2. Reproduce the first Verus failure and read the emitted contract.
3. Determine whether the defect is behavior, a missing precondition, a View lemma, or
   a true external boundary.
4. Prototype a small proof in a non-generated fixture or translator unit test.
5. Encode proof-needs detection and helper generation generically.
6. Add positive, negative, and deduplication tests.
7. Regenerate, search for trust deltas, verify, and compare solver timing.

If the only passing version uses `assume(false)` or `external_body`, the proof fix is
not finished.

### Change a protocol action

1. Change the logical predicate in `src/protocol/<P>/` and its spec-level lemmas.
2. Update modes only if the action's caller/computed values changed.
3. Update TOML mappings only for representation or supported lowering changes.
4. Regenerate the affected functions and types.
5. Update refinement and invariant proofs, including preservation for every `LNext`
   branch.
6. Update scheduler action metadata and host dispatch if the runtime trigger changed.
7. Run model-check fixtures appropriate to the changed property and review traces/counts.
8. Run Verus and the relevant host/cluster test.

Document whether the change altered the algorithm or merely repaired its executable
realization.

### Add or change a state/message field

Trace the field end to end:

```text
logical type/action
  -> generated concrete type and View
  -> validity/clone/proof helpers
  -> logical/concrete message conversion
  -> wire tag and serialization
  -> host/scheduler use
  -> client/runtime compatibility
```

Update every variant constructor and match. Add backward compatibility or bump the wire
format deliberately; never let a field-order change silently reinterpret deployed
bytes. Round-trip all variants, test malformed/truncated input, regenerate, verify, and
run an integrated message path.

### Add a protocol to the generic runtime

1. Add logical types/actions, annotation, config, generated modules, and proofs.
2. Implement `ProtocolMessage`, `ProtocolConfig`, and `ProtocolHost`.
3. Classify every `LNext` action as message/timer/role driven and bind existentials to
   runtime values.
4. Add `src/services/<P>/main_i.rs` and all module declarations.
5. Add the name to Rust dispatch and C# server validation/help.
6. Add SCons/C# targets as required.
7. Decide whether a compatible generic client exists; if not, document server-only
   status and add a protocol-specific smoke driver.
8. Add dispatch, wire, host, cluster, generation, Verus, and model-check status tests.
9. Update Appendix F with a dated trust and evidence audit.

“The server recognizes the name” is an intermediate milestone, not integration.

### Change scheduler or host generation

1. Use `analyze-lnext` to capture the existing action set.
2. Update the generic scheduler schema and validation before protocol configuration.
3. Generate a scaffold into a temporary file and review each message, timer, role,
   existential, flag injection, and guard branch.
4. Add fixtures for flat and role-dispatched hosts and for invalid configuration.
5. Update the hand-written host deliberately; do not overwrite runtime policy blindly.
6. Run host tests and a cluster test whose success depends on the changed branch.

Liveness assumptions and retry cadence belong in the review even when safety contracts
are unchanged.

### Change serialization or FFI

1. Write down the old and new byte/signature contract.
2. Update Rust and C# definitions in one change.
3. Test every tag/field, edge length, allocation owner, callback failure, and early
   return.
4. Build both sides through SCons and run a real process boundary.
5. Decide compatibility explicitly: backward compatible, versioned, or intentionally
   breaking.
6. Update trust-boundary documentation and release notes.

No Verus contract proves that a C# delegate has the matching unmanaged layout.

### Extend the source-first model checker

1. Create a minimal semantic fixture and expected states/transitions/property result.
2. Add parser/type/domain/evaluator/solver support at the earliest missing layer.
3. Add an invalid model that must fail before exploration.
4. Compare bytecode, direct/native, and reference execution paths when applicable.
5. For POR/conflict changes, rebuild the DPOR parity corpus and prove/test that pruning
   preserves the selected property semantics.
6. Add telemetry for a new guardrail or expensive phase.
7. Rebuild the evidence matrix and review normalized structural drift.
8. Update [`model_checker_status.md`](model_checker_status.md) with the exact supported
   subset or blocker.

Do not increase `max_states` to conceal uncontrolled domain construction; add a
guardrail and make the configuration error reproducible.

### Remove an assumption or external body

1. Inventory the exact site and every caller.
2. State the proposition/contract being trusted and its intended justification.
3. Replace it with a verified body, stronger caller-proved precondition, or narrower
   external specification at the actual environment boundary.
4. Ensure the old construct is absent with a regression guard.
5. Run focused and whole-crate verification and compare timing/triggers.
6. Regenerate if the site is emitted and update trust documentation/counts from source.

Moving the same claim behind another external body is a relocation, not a removal.

### Make a documentation-only change

1. Run every command whose behavior is described.
2. Link to current source/config rather than duplicating volatile counts.
3. Label measurements and audits with date, commit, tool version, and reproduction
   command.
4. Keep examples free of local absolute paths.
5. Check relative links from `docs/tla-rs-book.md`.
6. Move superseded phase material to a clearly historical section instead of blending
   it into current guidance.

## Chapter 28 — Roadmap, Research Context, and Documentation Maintenance

The repository serves both as engineering infrastructure and as a record of research
work. Those roles coexist best when current capabilities are separated from proposed
work and historical evidence.

### Use explicit status vocabulary

Apply these labels consistently:

| Label | Meaning |
|---|---|
| Planned | A design or task exists; no implementation claim. |
| Experimental | An implementation exists but its interface, evidence, or integration is not a stable project promise. |
| Implemented | Current source performs the behavior and tests exercise it. |
| Generated reproducibly | Fresh generation matches the checked-in artifact. |
| Verus-verified | The named body/property verifies under stated contracts and trusted dependencies. |
| Model-checked | The named property was explored in a stated finite model with a stated result/limit. |
| Runtime-integrated | Server, wire path, and an appropriate driver work across the process boundary. |
| Supported | The project commits to the documented workflow and CI protects it. |
| Historical | Useful context from a dated state; not a current interface or status claim. |

Avoid “formally verified protocol” as a stand-alone status. Name the logical property,
refinement link, remaining assumptions/external boundaries, and runtime scope.

### Maintain a layered roadmap

Keep roadmap items tied to an evidence gap:

- language/transpiler coverage: unsupported syntax, relational patterns, types, or
  generated proof shapes;
- proof closure: active assumptions, external bodies/specifications, and missing
  invariant/refinement links;
- model checking: missing finite-domain support, evaluator semantics, scalability, or
  liveness/parity coverage;
- runtime integration: scheduler, wire/client, FFI, deployment, or benchmark gaps;
- performance: measured allocation, solver, or exploration bottlenecks;
- toolchain: Verus compatibility, trigger stability, and release reproducibility;
- documentation: untested commands, stale status, or missing conceptual explanation.

[`TODO.md`](../TODO.md) can remain a detailed ledger, but each active milestone should
name its source files, acceptance gates, and expected trust/evidence delta. Phase numbers
alone are not a user-facing roadmap.

### Preserve research evidence without overstating it

A research report should contain:

1. question and hypothesis;
2. source revision and toolchain;
3. input corpus/configuration;
4. command or script;
5. raw/machine-readable artifact;
6. result and stopping condition;
7. interpretation and threats to validity;
8. follow-up or superseding result.

Keep raw measurements separate from conclusions. A bounded counterexample can invalidate
an invariant in the model; a bounded pass cannot establish an unbounded theorem. A
Verus proof establishes its formal contract under its trusted base; it does not validate
the requirements or external runtime. A benchmark measures one environment and workload.

### Documentation ownership by source surface

Update documentation in the same change that alters its source:

| Source change | Documentation to review |
|---|---|
| CLI or config schema | Appendices A–C, quickstart, examples |
| Generated contract/proof policy | Chapters 13, 17–20 and Appendix G |
| Protocol/action/wire support | User guide, Chapter 21, Appendix F |
| Model-check semantics/matrix | User model-check chapter, Chapter 24, status report |
| Toolchain/CI | Setup chapters, Chapters 16, 24, and 26 |
| Trust site or proof closure | Architecture chapter, Appendix F, release notes |
| Benchmark/runtime path | Operations/performance chapters and reproducibility record |

Where possible, generate tables from source or add a test that compares documented
names with dispatch/config definitions.

### Age volatile statements visibly

Counts of assumptions, external bodies, trigger notes, states, timings, throughput, and
supported protocol profiles can change. Either derive them during publication or write:

```text
Audited: YYYY-MM-DD, commit <sha>, tool <version>
Reproduce: <command>
Scope: <paths/model/workload>
```

Never present an undated phase count as current. If a historical number explains a
design decision, keep its date and link to the artifact.

### Archive rather than erase

Phase plans and investigation notes often contain valuable failed approaches. Preserve
them as historical records, add a short status banner, link to the current replacement,
and remove obsolete instructions from the main path. In particular, any old advice to
hand-edit generated code must be marked superseded by the generated-code policy.

### Review this book as executable infrastructure

Before merging documentation changes:

- walk the first-time user path from a clean checkout;
- walk one contributor path from spec edit through regeneration and verification;
- test links and command working directories;
- compare protocol and CLI lists with source;
- search for version strings and volatile numerical claims;
- distinguish verification, model checking, tests, and runtime trust in every summary;
- ask a reader unfamiliar with the phase history to find the current source of truth.

The book succeeds when contributors can make a safe change without reverse-engineering
old reports—and when a researcher can still reproduce the evidence behind a claim.

# Appendices

## Appendix A — CLI Reference

The binary is named `verus-transpile`. From the repository root, invoke the current
source with:

```bash
cargo run --manifest-path transpiler/Cargo.toml -- <arguments>
```

For scripts and repeated work, build once and use
`transpiler/target/debug/verus-transpile`. Run `verus-transpile --help` and
`verus-transpile <command> --help` for the exact installed interface; this appendix
summarizes the current source.

### Default spec-to-exec command

When no subcommand is supplied, the CLI transpiles annotated Verus specifications:

```bash
verus-transpile \
  --input spec.rs \
  --annotations spec.automan \
  --config spec_transpile.toml \
  --output generated.rs
```

| Option | Meaning |
|---|---|
| `-i, --input FILE` | Input Verus specification. |
| `-a, --annotations FILE` | Mode annotations. |
| `-c, --config FILE` | Transpiler TOML. |
| `-o, --output FILE` | Generated Rust/Verus file. |
| `--stdout` | Write generated text to stdout. |
| `--project DIR --output-dir DIR` | Batch/project mode. |
| `--dry-run` | Analyze without writing output. |
| `--dump-config` | Print the fully resolved configuration as TOML. |
| `--auto-skip` | Continue after per-function translation failures and report skips. |
| `--proof-fallback` | Emit `external_body` stubs for failures; implies auto-skip and changes the trusted surface. |
| `-v, --verbose` | Print diagnostic progress. |

Normal contribution builds should not use auto-skip or proof fallback to conceal a
missing function.

### Inspection and validation

| Command | Important arguments | Output |
|---|---|---|
| `list-templates` | none | Current recognized quantifier/construction templates. |
| `check` | `--annotations FILE` | Parses the `.automan` file and reports module/entry counts. Full mode checks require transpilation. |
| `model-config` | `--model FILE`; optional `--max-depth`, `--max-states`, `--timeout-ms`, `--max-seq-len`, `--max-set-len`, `--max-map-len`, `--int-range MIN..MAX`, `--nat-max`, `--candidate-eval-guardrail` | Resolved model configuration after overrides. |
| `report-assumes` | `--input-dir DIR [--output FILE]` | JSON inventory of generated `assume(...)` sites in files directly under the directory. |

### Model checking

```bash
verus-transpile model-check \
  --input protocol.rs --types types.rs --model model.toml \
  --init LInit --next LNext \
  --invariant Safety --search bfs --json-report
```

| Option | Meaning |
|---|---|
| `--input FILE` | Required protocol specification. |
| `--types FILE` | Types file; defaults to sibling `types.rs`. |
| `--model FILE` | Required finite-model configuration. |
| `--init NAME`, `--next NAME` | Entrypoints; defaults are `LInit` and `LNext`. |
| `--invariant NAME` | Repeatable override for configured invariants. |
| `--search bfs|dfs|dpor` | Exploration strategy; default BFS. |
| `--max-depth N`, `--max-states N`, `--timeout MS` | Search-limit overrides. |
| `--json-report` | Emit the machine-readable report on stdout. |
| `--export-parity DIR` | Export ordinary reached-state JSONL for cross-engine comparison. The current main path does not emit edges here despite the CLI help text. |
| `--export-parity-debug DIR` | Stream generated/distinct states and edges with provenance. |
| `--no-bytecode` | Use the AST interpreter rather than the default bytecode evaluator. |
| `--native-codegen` | Opt into native expression code generation; adds compilation startup. |
| `--workers N` | Exploration workers; default one. |
| `--conflict-profile` | Emit DPOR independence-conflict diagnostics to stderr. |

The property result is data in the report. A successfully executed model-check command
can exit successfully while reporting an invariant or liveness violation; automation
must inspect `result`, `stop_reason`, and property fields, not only `$?`.

### Type and runtime scaffolding

| Command | Important arguments | Purpose |
|---|---|---|
| `generate-types` | repeat `--input FILE`; `--config FILE`; `--output FILE` | Emit concrete types, Views, validity/clone support. Input order is significant. |
| `generate-messages` | `--config FILE [--output FILE]` | Emit `ProtocolMessage` code from `[messages]`. |
| `generate-marshalable` | `--config FILE [--output FILE]` | Emit configured struct/enum `Marshalable` implementations. |
| `analyze-lnext` | `--input FILE --config FILE [--next-fn NAME] [--spec-prefix P] [--exec-prefix P] [--output FILE]` | Extract and classify scheduler actions. |
| `generate-host` | `--config FILE --protocol NAME`; optional `--gen-module NAME`, `--output FILE` | Emit a host scaffold from message/scheduler configuration. |

Generated host and serialization code still require runtime-policy and wire-format
review.

### TLA+ and round-trip commands

| Command | Important arguments | Purpose |
|---|---|---|
| `tla-lint` | positional `INPUT`; optional `--json` | Check the clean-subset rules. |
| `clean-tla` | positional `INPUT`; optional `-o, --output FILE` | Project a clean-subset TLA+ module to a single-process Verus specification; stdout if output is omitted. |
| `translate-tla` | `--input`, optional `--output`, `--types`, `--gen-modes`, `--spec-prefix`, `--state-name` | Translate TLA+ to a Verus specification and optionally modes. |
| `verus2-tla` | `--input`, optional `--output`, `--spec-prefix`, `--include-recommends`, `--generate-types`, `--batch` | Convert supported Verus specification syntax to TLA+. |
| `pipeline` | `--tla-input`, `--exec-output`; optional `--clean-subset`, `--types`, `--keep-intermediate`, `--spec-output`, naming options, and `--config` | Run TLA+ → Verus spec → executable generation. |
| `generate-mc-wrapper` | `--input`, `--output`; optional `--cfg-output`, `--init`, `--next`, `--module-suffix`, `--packet-mode none|append-seq|replace-seq`, `--packet-var`, repeat `--invariant` | Emit a TLC wrapper and configuration skeleton around relational Init/Next. |

`tla-lint` exits 0 for a clean result, 1 for subset violations, and 2 when the module
cannot be parsed. `clean-tla` exits 0 on a complete projection, 1 when required parts
cannot be emitted, and 2 for parse or clean-subset rejection. These verdict codes are
preserved with JSON output.

### Guarded migration utilities

| Command | Arguments | Safety behavior |
|---|---|---|
| `migrate-generated-import` | `--input FILE --from TEXT --to TEXT --expect N` | Rewrites one exact import only in a marked generated file and checks the count. |
| `migrate-generated-text` | `--input FILE --from TEXT --to TEXT --expect N` | Performs an exact guarded text replacement under the same marker/count rules. |

These commands do not waive the generated-code policy. Use them only for a controlled
mechanical migration and make the generator reproduce the result.

### Output conventions and general exit behavior

Machine-readable primary output goes to stdout (`--json-report`, `--json`, config
dumps); diagnostics and optional profiles should be kept on stderr. When redirecting a
report, do not merge stderr into it. File-producing commands may print a human status
line, so automation should consume the requested file rather than scrape that line.

Apart from the explicit TLA verdicts above, zero means the command completed and a
nonzero status means CLI, I/O, parse, configuration, generation, or execution failure.
Clap normally uses status 2 for malformed command-line arguments. Commands that encode
a semantic result in JSON, especially `model-check`, require inspecting the result
field even after status 0.

## Appendix B — `.automan` Grammar and Validation Rules

Mode annotations tell the transpiler which predicate arguments are inputs and which
must be computed. The grammar implemented by `transpiler/src/annotation/mod.rs` is
line-oriented and can be summarized as:

```text
file          := { comment | module }
module        := "module" path "{" newline { entry | comment } "}"
entry         := predicate | helper
predicate     := identifier "(" mode-list ")" ";"
helper        := "helper" identifier "(" mode-list ")"
                 [ "->" return-type ] ";"
mode-list     := [ mode { "," mode } ]
mode          := "+" | "-"
path          := identifier { "::" identifier }
comment       := line whose trimmed text starts with "//"
```

Use one module header, entry, or closing brace per line. Use `//` full-line comments;
do not depend on undocumented `#` or trailing-comment behavior.

### Modes

- `+` is an input supplied by the caller.
- `-` is an output constructed by the generated function.
- Modes are positional and must match the specification signature.
- A helper returns a value and should have input arguments only.
- A helper return type can be written explicitly; if omitted, the current translator
  uses the return type parsed from the specification.

Example:

```text
// Concrete code computes the initial state and the post-state.
module Example::Counter {
    LInit(+, -);
    LStep(+, +, -);
    helper LBoundedAdd(+, +) -> int;
}
```

If `LStep(s, delta, s_)` is the logical signature, this generates a function that
receives `s` and `delta` and returns or mutates the concrete representation of `s_`.

### Validation layers

`check --annotations FILE` validates annotation syntax. Full transpilation additionally
checks the annotation against parsed function signatures and applies:

| Rule | Rejected shape | Typical repair |
|---|---|---|
| Arity/signature | Mode count differs from parameter count, or function is absent. | Correct the declaration or qualification. |
| Predicate output | A predicate has no `-` argument. | Mark the actual computed parameter, or model it as a helper. |
| Helper discipline | A helper declares output parameters. | Return the value or make the relation a predicate. |
| Saturation | An output, or a known structured output field, is never assigned. | Cover every branch/field or assign the whole output. |
| Harmony | An output member receives incompatible duplicate assignments. | Make branches exclusive or construct once. |
| Obligation | An output is read before it is assigned. | Reorder construction or turn the needed value into an input/helper result. |
| Input immutability | The relation assigns a `+` parameter. | Correct the mode or reformulate the predicate. |
| Branch coherence | Branches construct different output sets. | Supply complete branch results. |
| Quantifier restriction | A general quantified clause assigns an output. | Use a supported comprehension pattern or add a generic translator pattern. |

### Qualification and multiple modules

The module path associates declarations with specification functions. Keep its spelling
consistent with the parsed module path; do not use the annotation file to remap Rust
names. Function/type/path remapping belongs in TOML. Multiple module blocks can coexist
in one file when the transpilation input spans them.

This appendix is the maintained prose reference. Parser source and tests remain
authoritative when examples and implementation behavior differ.

## Appendix C — Complete Transpiler Configuration Reference

Configuration is deserialized by `transpiler/src/config.rs`. Unless a default is named
below, maps/lists/strings are empty, booleans are false, and optional values are absent.
Use `--dump-config` to inspect inferred values and interactions for a real input.

### Root keys

| Key | Shape | Purpose |
|---|---|---|
| `remapping` | map | Logical type name → concrete type name. |
| `function_paths` | map | Logical function → qualified executable call path. |
| `spec_only_functions` | list | Functions that keep their spec-layer names and receive no executable prefix. |
| `method_calls` | map of tables | Lower a free function to a method call. |
| `primitive_types` | list | Integer-like types: no validity call; contract view uses a cast. |
| `skip_valid_types` | list | Types with a View but no validity call. |
| `skip_functions` | list | Functions omitted from ordinary translation. |
| `no_stub_functions` | list | Skipped functions for which proof-fallback must not emit a duplicate stub. |
| `modules` | map of tables | Per-module remapping, skips, and includes. |
| `view_overrides` | map | Per-field custom View expression, keyed `Type.field`. |
| `type_view_exprs` | map | Per-type contract View template containing `{param}`. |
| `extra_fields` | map | Concrete-only field keyed `Type.field`, value `type = default`. |
| `clone_strategy` | map | Per-concrete-type clone strategy, currently `derive` or `external_body`. |
| `clone_up_to_view_types` | list | Types cloned with a View-preserving helper. |
| `arc_wrap_types` | list | Functional-state types whose non-scalar fields use `Arc`. |
| `arc_wrap_fields` | map | Explicit/computed Arc fields per concrete type. |
| `mut_self_types` | list | State types lowered to `&mut self`. |
| `skip_types` | list | Parsed logical types omitted from concrete type generation. |
| `skip_validity_types` | list | Generated concrete types whose validity method is supplied elsewhere. |
| `skip_view_types` | list | Generated concrete types whose View implementation is supplied elsewhere. |
| `re_exports` | list | Generated top-level `use` paths, without `use`/semicolon. |
| `extra_type_aliases` | map | Extra concrete alias → type expression. |
| `custom_derives` | map | Additional derives per concrete type. |
| `skip_fields` | map | Logical fields omitted from a concrete type. |
| `variant_remapping` | map | Bare logical variant → qualified concrete variant. |
| `collection_fields` | list | Set/map fields using collection-aware clone/View lowering. |
| `vec_fields` | list | Vec/HashMap fields using standard clone and collection View. |
| `clone_fields` | list | Non-Copy identity-View fields that require clone. |
| `clone_field_types` | map | Clone field → concrete enum type for helper generation. |
| `struct_vec_fields` | map | Vec field → `[ConcreteElement, LogicalElement]`. |
| `map_fields` | map | Deep map field → `[ConcreteMap, abstractionPrefix, ConcreteValue]`. |
| `verified_clone_fns` | map | Abstraction prefix → verified map clone function. |
| `msg_vec_type` | optional two-item list | `[ConcreteMessage, LogicalMessage]` for packet-vector proof helpers. |
| `hashmap_index_fields` | list | Map-indexed fields that need borrowed keys but no deep-map helpers. |
| `extra_requires` | map | Executable function → additional precondition strings. |
| `inline_expansions` | map of tagged tables | Spec/exec call lowering strategy. |
| `eq_function_fields` | map | Field → verified/configured equality function. |
| `arrow_variants` | map | Arrow-accessed field → containing concrete enum variant. |
| `vec_element_ensures` | list | Per-element predicates added to vector output contracts. |
| `set_fields` | list | HashSet/Set fields used by cardinality proof injection and call lowering. |
| `messages` | optional table | Wire-message generator configuration. |
| `marshalable` | optional table | Serialization generator configuration. |
| `scheduler` | optional table | `LNext` action and host-scaffold configuration. |

The distinct names `skip_valid_types` and `skip_validity_types` are intentional. The
first affects how a referenced type is used in function contracts; the second suppresses
generation of a validity method for a concrete type that is still generated.

### `[naming]`

| Field | Default | Meaning |
|---|---|---|
| `spec_prefix` | `"L"` | Logical type/function prefix. |
| `exec_prefix` | `"C"` | Concrete type/function prefix. |
| `spec_fn_suffix` | empty | Optional suffix recognized on logical functions. |
| `exec_fn_suffix` | empty | Suffix placed on executable functions. |
| `int_type` | `"i64"` | Concrete representation of spec `int`. |
| `nat_type` | `"u64"` | Concrete representation of spec `nat`. |

### `[output]`

| Field | Default | Meaning and caution |
|---|---|---|
| `generate_abstraction_fns` | true | Generate View implementations. |
| `generate_validity_predicates` | true | Generate validity predicates. |
| `validity_predicate_name` | `"well_formed"` | Method name; RSL configurations commonly use `valid`. |
| `generate_clone` | true | Generate configured clone support. |
| `include_debug_comments` | false | Include generator diagnostics in output. |
| `output_dir` | absent | Configured output directory. |
| `custom_imports` | empty | Imports placed before the `verus!` block. |
| `generate_loops_for_verification` | false | Emit explicit loop forms for supported operations. |
| `generate_inline_types` | false | Generate types from the same specification input. |
| `generate_proofs` | false | Emit generated proof blocks when true; the false legacy path can emit assumptions and is not an acceptable proof-complete setting. |
| `assume_postconditions` | false | Insert `assume(false)` into generated functions; explicitly trusted migration mode. |
| `proven_functions` | empty | Logical names exempted from `assume_postconditions`. |
| `generate_wrapper_methods` | false | Add functional-to-method wrappers. |
| `wrapper_impl_type` | absent | Required concrete impl type for wrapper generation. |
| `clone_method` | absent | Alternate clone method used in loops. |
| `generate_clone_up_to_view_simple` | false | Generate View-preserving clone for primitive-only structs. |
| `generate_unreachable_value_helper` | false | Generate a shared trusted unreachable-value helper. |
| `manual_code` | absent | Inject a file into generated output; policy-sensitive legacy mechanism. |

Current proof-oriented protocol configs explicitly enable proof generation where
supported. Review any config that relies on the default `generate_proofs = false` by
inspecting its output trust inventory.

### Call-shaping tables

Each `method_calls.<LogicalFn>` table has `method_name`, zero-based
`receiver_arg_index` (default 0), and optional zero-based `destructure_index`.

Each `inline_expansions.<LogicalFn>` table may set `spec_binary_op` and must select a
tagged executable strategy:

- `strategy = "owned_call"`;
- `strategy = "conditional_binary"` with `op`, `condition_arg`, and
  `condition_types`;
- `strategy = "mixed_borrow"` with `borrowed_args`.

These are generic syntax/type policies, not places for protocol-name branching.

### Module, message, and serialization tables

`[modules.<Module>]` accepts `remapping`, `skip_functions`, and `custom_includes`.

`[messages]` has `enum_name`, `import_path` (default
`crate::common::framework::protocol_trait::ProtocolMessage`), `doc_comment`, and
repeated `[[messages.variants]]` entries. Each variant has `name`, optional `doc`, and
`fields = [[name, type], ...]`.

`[marshalable]` contains repeated struct and enum definitions:

```toml
[[marshalable.types]]
name = "CBallot"
fields = [["seqno", "u64"], ["proposer_id", "u64"]]

[[marshalable.enums]]
name = "CReply"

[[marshalable.enums.variants]]
name = "Ok"
tag = 0
fields = [["value", "u64"]]
```

Struct entries have `name` and field pairs. Enum entries have `name`; variants have a
unique `u8` `tag`, `name`, and field pairs. Named field types must implement the
expected marshalling interface.

### Scheduler tables

`[scheduler]` has:

| Field | Default | Meaning |
|---|---|---|
| `next_fn` | `"LNext"` | Logical next-state function. |
| `params` | empty | Ordered `LNext` parameter names. |
| `action_count` | 0 | Informational count; keep consistent with actions. |
| `message_response_overrides` | empty | Action-name patterns forced message-driven. |
| `role_prefixes` | empty | Prefixes stripped for message/action matching. |
| `timer_overrides` | empty | Action-name patterns forced timer-driven. |

Each `[[scheduler.actions]]` has required `spec_name` and `exec_name`, `kind`
(`timer_driven` by default or `message_driven`), optional `message_variant`, and lists
of `[name, type]` `existential_params`, `[state_field, value]` `flag_injections`, and
Rust boolean `guard_checks`.

Optional `[scheduler.role_dispatch]` has `dispatch_style = "config_index"` or
`"state_field"`, `dispatch_field`, and repeated roles. A role has `name`, `condition`,
and executable `actions`. The final config-index role may use an empty condition as the
fallback; state-field conditions name concrete variants.

### Important interactions

- `mut_self_types` and Arc wrapping are incompatible; resolution warns and removes Arc
  wrapping for mutable-self types.
- `generate_wrapper_methods = true` needs `wrapper_impl_type`.
- `manual_code`, `assume_postconditions`, `generate_unreachable_value_helper`,
  `clone_strategy = "external_body"`, and CLI proof fallback affect the trust review.
- `skip_functions` plus proof fallback may create stubs; use `no_stub_functions` only
  when a real implementation is intentionally supplied elsewhere.
- `skip_fields` and `extra_fields` change the representation relation and require an
  explicit View/validity story.
- collection classifications affect both executable clone behavior and generated proof
  lemmas; stale entries can compile yet express the wrong abstraction.
- message tags and field order form a wire contract and must be unique/tested.
- scheduler strings become executable scaffold text; validate names and review guards.

### Minimal and inspected configurations

A minimal proof-oriented file makes safety-relevant defaults explicit:

```toml
[naming]
spec_prefix = "L"
exec_prefix = "C"
int_type = "i64"
nat_type = "u64"

[output]
generate_abstraction_fns = true
generate_validity_predicates = true
validity_predicate_name = "well_formed"
generate_clone = true
generate_proofs = true
assume_postconditions = false
```

Before adopting an advanced config, run a dry generation and resolved dump, then search
the output for proof escape hatches:

```bash
verus-transpile --input spec.rs --annotations spec.automan \
  --config spec_transpile.toml --dump-config > resolved.toml
verus-transpile --input spec.rs --annotations spec.automan \
  --config spec_transpile.toml --dry-run --verbose
```

Real `_transpile.toml` files demonstrate supported combinations, but they may also
encode protocol-specific legacy debt. Treat `config.rs`, its tests, resolved dumps,
and generated output as the complete truth.

## Appendix D — TLA+ ↔ Verus Syntax and Support Matrix

“Supported” is not one bit. A construct may parse into an AST, translate to plausible Verus,
typecheck, execute in the source-first model checker, and still lack either a semantic
equivalence test or a deductive proof. This appendix records those stages separately.

The tables describe the current implementation, not all of TLA+ or Verus. They use this legend:

- **✓** — the stage handles the construct and representative tests exercise that path;
- **△** — only a documented shape is handled, the result is an approximation, or evidence is
  structural rather than semantic;
- **✗** — the stage rejects, drops, or does not preserve the construct; and
- **—** — the stage does not consume that language construct directly.

The columns are:

- **P**: tokenize and parse TLA+ into the local AST;
- **G**: general `translate-tla` import to Verus spec code;
- **C**: all-or-nothing `clean-tla` projection under C1–C5;
- **X**: `verus2-tla` export from Verus spec code;
- **RT**: normalized structural round-trip evidence for representative cases;
- **M**: evaluation by the source-first Verus model checker; and
- **E**: generation of an executable implementation from the imported spec.

`M` is deliberately not “TLC support”: the source-first checker consumes Verus source. A TLA+
row reaches `M` only after translation and only if the resulting Verus expression belongs to the
runtime evaluator's subset. `E` likewise means that the current spec-to-exec machinery can
consume an appropriate generated spec shape; it does not mean that generated proof obligations
are discharged.

### Modules and declarations

| Construct | P | G | C | X | RT | M | E | Current boundary |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| Module header and `EXTENDS` | ✓ | ✓ | ✓ | △ | △ | — | — | Importers use the local module model; export synthesizes a module and extension list rather than preserving source text. |
| `CONSTANT(S)` and `VARIABLE(S)` | ✓ | ✓ | ✓ | △ | △ | ✓ | △ | Model checking needs finite constant/type domains. Reverse export infers declarations from converted Verus shapes, so declaration identity is not generally round-trip exact. |
| Operator definitions | ✓ | ✓ | ✓ | ✓ | △ | ✓ | △ | Expression and signature restrictions in later rows still apply. Structural tests cover selected operators; semantic preservation is a separate claim. |
| `ASSUME` | ✓ | ✗ | ✗ | ✗ | ✗ | — | — | The general importer does not turn module assumptions into Verus preconditions. `verus2-tla --include-recommends` is currently wired at the CLI but unused by the converter. |
| `THEOREM` and TLAPS proof bodies | △ | ✗ | ✗ | ✗ | ✗ | — | — | The theorem formula can be parsed; a following proof body is skipped, not translated or checked. |
| `INSTANCE`, including `LOCAL INSTANCE` | ✓ | ✗ | ✗ | △ | ✗ | — | — | The AST/printer represent instances, but current conversion paths do not preserve general module instantiation semantics. |
| `LOCAL` operator | ✓ | △ | △ | △ | △ | △ | △ | General import emits locality metadata for supported definitions. Clean projection permits only projectable helpers. |
| `RECURSIVE` operator | ✓ | △ | △ | △ | △ | △ | △ | General import recognizes selected recursive patterns and has limited generated decreases heuristics. Termination and executable generation require separate review. |
| Comments and source locations | ✓ | △ | △ | △ | ✗ | — | — | Diagnostics retain useful spans, but comments and formatting are not a round-trip contract. |

### Values, expressions, and data structures

| Construct | P | G | C | X | RT | M | E | Current boundary |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| Boolean, integer, and string literals | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | Model domains are finite even though the specification types are mathematical. |
| `/\\`, `\\/`, `~`, `=>`, `<=>` | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | Representative precedence and emission cases are tested. |
| `=`, `/=`, `<`, `<=`, `>`, `>=` | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | Equality depends on the selected Verus/runtime representation of values. |
| `+`, `-`, `*`, integer division, modulo | ✓ | ✓ | ✓ | ✓ | △ | ✓ | ✓ | The evaluator reports division or modulo by zero. Numeric coercion and overflow assumptions must be reviewed at the executable boundary. |
| Exponentiation and integer range `a..b` | ✓ | △ | △ | △ | △ | △ | △ | The general importer has contextual lowering; these are not a blanket promise that every emitted form is executable by the checker or generated runtime. |
| Explicit set literals and membership | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | Model checking enumerates only bounded runtime sets. |
| Set union, intersection, difference, subset, powerset, and Cartesian product | ✓ | △ | △ | △ | △ | △ | △ | Support varies by operation and surrounding type information. Check emitted code and evaluator methods instead of treating “sets” as one feature. |
| Set comprehension with one binder | ✓ | △ | △ | △ | △ | △ | △ | Translation requires an inferable finite source domain. The model checker needs a domain-resolver hook for quantified evaluation. |
| Multi-binder set comprehension | ✓ | ✗ | △ | ✗ | ✗ | ✗ | ✗ | The general translator emits an explicit unsupported marker. Clean projection accepts only its own recognized/projectable shapes. |
| Sequence and tuple literals | ✓ | ✓ | ✓ | △ | △ | ✓ | △ | Literal construction is supported; tuple/sequence distinctions and element types still need to survive translation. |
| Sequence indexing, `Head`, `Tail`, `SubSeq`, append, and concatenation | ✓ | △ | △ | △ | △ | △ | △ | TLA+ sequence indices are one-based while Verus/Rust indices are normally zero-based. Known operators receive targeted lowering; generic `f[x]` does not prove which convention was intended. |
| Function/map literal, application, domain, and update/`EXCEPT` | ✓ | △ | △ | △ | △ | △ | △ | TLA+ functions are total mathematical values; Verus maps and runtime maps use a finite encoding. Reverse conversion simplifies some map literals. |
| Records, record sets, and field access | ✓ | △ | ✓ | △ | △ | ✓ | △ | Clean projection covers corpus-backed record/state shapes. General import may synthesize or merge record types, so nominal identity is not generally preserved. |
| Struct/record update | ✓ | △ | ✓ | △ | △ | ✓ | △ | Model evaluation requires the base to evaluate to a struct or enum value. |
| Enum variants and payloads | △ | △ | △ | △ | △ | ✓ | △ | Enum support is strongest on the Verus side. TLA+ has no identical nominal enum construct, so import/export use encodings. |
| `IF / THEN / ELSE` | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | Generated-D1 fallback shapes can still contain arbitrary placeholders; inspect the emitted branch. |
| `CASE` | ✓ | △ | △ | △ | △ | ✓ | △ | General import expects supported arms and an appropriate `OTHER` shape; partial cases require review. |
| `LET / IN` | ✓ | ✓ | ✓ | △ | △ | △ | △ | The evaluator accepts identifier `let` patterns, not arbitrary destructuring patterns. |
| Bounded `\\A` and `\\E` | ✓ | △ | △ | △ | △ | △ | △ | The model checker evaluates quantifiers only with a finite domain resolver and identifier bindings. Branch-level existentials in `LNext` have a separate finite-expansion path. |
| Unbounded quantifier syntax | ✓ | △ | ✗ | △ | △ | ✗ | ✗ | Parsing or emitting mathematical Verus quantification does not make it executable over an unbounded domain. |
| `CHOOSE` | ✓ | △ | △ | △ | △ | △ | ✗ | Choice needs a finite, nonempty, evaluator-resolvable domain; it is not a deterministic executable selection contract. |
| `LAMBDA` and general higher-order functions | ✓ | ✗ | △ | ✗ | ✗ | ✗ | ✗ | The general translator marks `LAMBDA` unsupported and reverse conversion rejects general closures. Recognized clean helpers do not imply general higher-order support. |
| Casts and views | — | △ | △ | △ | ✗ | △ | △ | The evaluator supports casts to `int`, `nat`, and `bool`; reverse export erases or approximates Verus views and casts. |
| Bitwise and shift operators | — | — | — | ✗ | ✗ | ✗ | △ | The model evaluator rejects them. Executable Rust can use them, but that does not establish a TLA+ mapping. |

### Actions and temporal operators

| Construct | P | G | C | X | RT | M | E | Current boundary |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| Primed variables and relational next-state equality | ✓ | ✓ | ✓ | △ | △ | ✓ | ✓ | Import normally lowers the relation to `(s, s_)`. Reverse export reconstructs relational operators from Verus parameters rather than preserving original prime syntax. |
| `UNCHANGED` | ✓ | ✓ | ✓ | △ | △ | ✓ | ✓ | The clean projector expands projectable frame conditions. Verify that all state fields are represented. |
| Disjunctive `Next` actions | ✓ | ✓ | ✓ | △ | △ | ✓ | △ | Branch labels drive exploration, fairness, and telemetry. Executable generation needs mode annotations and witness construction for nondeterminism. |
| Existential action parameters | ✓ | ✓ | ✓ | △ | △ | ✓ | △ | Every witness type needs a finite model domain; exec generation must supply a concrete choice mechanism. |
| Network send/receive and packet-set idioms | ✓ | △ | ✓ | △ | △ | △ | △ | Clean C4 projection recognizes selected idioms. Runtime transport and serialization remain outside the mathematical action itself. |
| `ENABLED` | ✓ | △ | ✗ | ✗ | ✗ | ✗ | ✗ | The general importer can retain a marker/lowered form in selected contexts; the source-first temporal engine does not execute arbitrary TLA+ `ENABLED` expressions. |
| `[]`, `<>`, `~>` | ✓ | △ | ✗ | ✗ | ✗ | △ | ✗ | General import uses markers rather than a proved temporal translation. Model checking implements separately configured bounded `leads_to` graph analysis, not evaluation of imported temporal syntax. |
| `WF_` and `SF_` | ✓ | △ | ✗ | ✗ | ✗ | △ | ✗ | The model checker applies weak/strong fairness to configured `LNext` branch labels during bounded SCC filtering. That is separate from translating a TLA+ fairness formula. |
| Action composition | ✓ | △ | ✗ | ✗ | ✗ | ✗ | ✗ | General import currently approximates composition with emitted comments/conjunction; do not claim semantic preservation. |
| Dynamic membership/reconfiguration | ✓ | △ | ✗ | △ | ✗ | △ | △ | The clean subset deliberately excludes reconfiguration/fixed-membership rewrites that require human redesign. |

### Type/domain support for model evaluation

After a construct reaches Verus, the source-first checker has its own support boundary:

| Verus/runtime category | Status | Finite-model requirement or limitation |
|---|---:|---|
| `unit`, `bool`, `int`, `nat`, string | ✓ | `int` and `nat` need configured fallback ranges when enumerated; strings normally come from explicit `values`. |
| Named structs and enums, including payload variants | ✓ | The source schema must be discoverable and every recursively enumerated field must have a finite domain. |
| Tuples and references | ✓ | References are modeled through the underlying value; this is not Rust aliasing semantics. |
| `Seq<T>`, `Set<T>`, `Map<K,V>` | ✓ | Enumeration is bounded by `collections.max_*_len`; these are the supported generic domain constructors. |
| Other generic types | ✗ | Domain expansion rejects generic constructors outside the three recognized collections. |
| Helper spec-function calls | △ | The helper must be ingested and evaluable; unresolved names and excessive helper recursion are errors. |
| `forall`/`exists` expressions | △ | Bindings must be identifiers and a finite domain-resolver hook must be present. |
| `match` and struct update | ✓ | Patterns/variants must belong to the parsed subset; update bases must be struct/enum values. |
| Arbitrary Rust/Verus proof syntax | ✗ | Proof blocks, triggers, ghost reasoning, and SMT facts are not interpreted as executable transition semantics. |

The implementation-backed evaluator list lives in
[`model_checker_status.md`](model_checker_status.md) and
[`modelcheck/evaluator.rs`](../transpiler/src/modelcheck/evaluator.rs). When these disagree,
the source plus a focused executable test is authoritative.

### Evidence and verification are separate stages

The following labels describe increasingly strong but non-interchangeable checks:

| Evidence | What ran | What it establishes | What it does not establish |
|---|---|---|---|
| Parse | tokenizer/parser and AST construction | The input belongs to the accepted grammar. | Translation, typing, or meaning. |
| Translate | one importer/exporter completed without a gap | An output representation was emitted. | That the output typechecks or preserves behavior. |
| V1 | generated Verus typecheck | The selected generated code is accepted by the available Verus toolchain. | Behavioral equivalence or discharged functional-correctness obligations. A test that skips because Verus is absent is not V1 evidence for that run. |
| V2 | finite observable state-set comparison | TLC and the selected generated model agree on the declared finite observables for that fixture. | Full trace equivalence, unbounded equivalence, or unseen inputs. |
| V3 | byte-for-byte golden generated block | The generator did not drift from reviewed output. | That the golden is correct or semantically equivalent. |
| Structural round trip | normalized AST/declaration comparison | Selected syntax survives conversion modulo documented normalization. | Semantic equivalence, especially for indexing, maps, views, and temporal formulas. |
| Finite model check | bounded state exploration/evaluation | A violation was found, or no selected violation was found inside the recorded finite boundary. | A Verus proof or unbounded temporal theorem. |
| Verus proof | verifier discharges explicit obligations without unreviewed assumptions | The stated deductive obligations hold relative to the trusted boundary and assumptions. | Runtime correctness outside that boundary or TLA+ equivalence unless refinement is among the obligations. |

Two command-level cautions follow from this table. First, `clean-tla` emits spec code only; it
does not generate or discharge a proof. Second, the general `pipeline` configuration currently
defaults `output.generate_proofs` to `false` and `output.assume_postconditions` to `true`.
Pipeline completion alone must therefore never be reported as “verified.”

### Current test anchors

Use tests as stage-specific evidence rather than as global feature claims:

- [`clean_subset_lint_test.rs`](../transpiler/tests/clean_subset_lint_test.rs) checks C1–C5
  decisions and linter exit behavior;
- [`corpus_parse_guard.rs`](../transpiler/tests/corpus_parse_guard.rs) and
  [`corpus_projection_guard.rs`](../transpiler/tests/corpus_projection_guard.rs) cover the
  checked-in clean corpus;
- [`corpus_v1_guard.rs`](../transpiler/tests/corpus_v1_guard.rs) supplies V1 only when its
  Verus prerequisite is present;
- [`corpus_v3_guard.rs`](../transpiler/tests/corpus_v3_guard.rs) freezes generated projection
  blocks;
- [`tla_examples_test.rs`](../transpiler/tests/tla_examples_test.rs) checks representative
  general-import shapes;
- [`roundtrip_test.rs`](../transpiler/tests/roundtrip_test.rs) supplies structural, not
  semantic, round-trip evidence; and
- model-check unit/integration fixtures under
  [`transpiler/tests/model_check_fixtures`](../transpiler/tests/model_check_fixtures) exercise
  finite evaluator, search, report, and blocker behavior.

Before changing a ✓ to a broader claim, add a test at every newly claimed stage. A substring
assertion is translation evidence; it is not typechecking, evaluation, equivalence, or proof.

## Appendix E — `model.toml`, Reports, and Evidence Schema

This appendix is the operational contract for a source-first model-check run. It records the
finite universe, search policy, selected properties, result schema, and reproducibility
artifacts. The Rust definitions in
[`modelcheck/config.rs`](../transpiler/src/modelcheck/config.rs) and report construction in
[`main.rs`](../transpiler/src/main.rs) remain authoritative when the CLI evolves.

### A complete `model.toml` shape

The following example shows every current configuration group. Its field and type names are
illustrative: they must match the `LConstants`, state, enum, helper, invariant, and `LNext`
branch names in the protocol being checked.

```toml
[constants.assignments]
quorum = 2
recovery_enabled = false

[constants.domains.node]
kind = "values"
values = ["n1", "n2", "n3"]

[constants.domains.epoch]
kind = "nat_range"
max = 2

[quantifiers.int]
min = -1
max = 3

[quantifiers.nat]
max = 3

[quantifiers.types.NodeId]
kind = "values"
values = ["n1", "n2", "n3"]

[quantifiers.types.LRole]
kind = "enum_subset"
variants = ["Follower", "Leader"]

[collections]
max_seq_len = 3
max_set_len = 3
max_map_len = 3

[search]
max_depth = 12
max_states = 50000
timeout_ms = 30000
state_dedup = "canonical"
symmetry_fields = []
por_heuristic = "none"
candidate_eval_guardrail = 10000

[properties]
invariants = ["LTypeOK", "LSafety"]
leads_to = [
  { name = "request_completes", from = "LRequestPending", to = "LRequestDone" },
]
fairness = { weak = ["LDeliver"], strong = [] }
check_deadlock = false
successor_semantics = "deadlock"
```

`model.toml` does not choose BFS, DFS, or DPOR. Search strategy is a CLI setting; absent
`--search`, the command selects BFS.

### Constants and finite domains

| Key | Type/default | Meaning |
|---|---|---|
| `constants.assignments.<field>` | Boolean, signed integer, or string; none by default | Fix one `LConstants` field to one value. |
| `constants.domains.<field>` | `DomainSpec`; none by default | Enumerate a field over a finite set. Every combined constants valuation is explored. |
| `quantifiers.int.min/max` | optional inclusive signed range | Fallback domain for mathematical `int` and compatible named integer types. |
| `quantifiers.nat.max` | optional inclusive upper bound | Fallback domain `0..max` for `nat` and compatible unsigned named types. |
| `quantifiers.types.<Type>` | `DomainSpec`; none by default | Override the finite values used for a named type in quantifiers, state expansion, or branch witnesses. |

A constants field may appear in assignments or domains, never both. A run fails before
exploration if it cannot construct any matching `LConstants` valuation or if a required named
type has no finite domain.

`DomainSpec` is a tagged TOML table:

| `kind` | Required fields | Values represented |
|---|---|---|
| `values` | nonempty `values = [...]` | Explicit Boolean, signed-integer, or string literals. |
| `int_range` | `min`, `max` with `min <= max` | Inclusive signed integer range. |
| `nat_range` | `max` | Inclusive natural range `0..max`. |
| `enum_subset` | nonempty `variants = [...]` | Named subset of variants from a parsed Verus enum. |

The TOML parser validates shape; model-check preflight validates the domain against the source
type. Thus a syntactically valid string domain can still be the wrong domain for a numeric or
enum field.

### Collection and search limits

| Key | Default | Meaning and interaction |
|---|---:|---|
| `collections.max_seq_len` | `4` | Maximum sequence length generated during finite domain expansion. Must be greater than zero. |
| `collections.max_set_len` | `4` | Maximum set cardinality generated during finite domain expansion. Must be greater than zero. |
| `collections.max_map_len` | `4` | Maximum map cardinality generated during finite domain expansion. Must be greater than zero. |
| `search.max_depth` | `30` | States at this depth are recorded but their successors are not generated. Must be greater than zero. |
| `search.max_states` | `100000` | Cap on distinct accepted states. Hitting it produces `MaxStatesReached`. |
| `search.timeout_ms` | `30000` | Wall-clock exploration limit for the ordinary explorers. Hitting it produces `TimeoutReached`. |
| `search.state_dedup` | `canonical` | `canonical` retains full normalized keys; `hash_compaction64` uses a lossy 64-bit fingerprint. |
| `search.symmetry_fields` | `[]` | Top-level `LState` fields anonymized before dedup. Nonempty means intentionally merged states. |
| `search.por_heuristic` | `none` | `none` or `invisible_branch`, the syntactic invisible-write branch heuristic. |
| `search.candidate_eval_guardrail` | `10000` | Per-state/per-branch cap on predicate-only fallback candidate evaluation. Exceeding it is a configuration/evaluation error, not a clean model-check result. |

The three collection limits bound generated values; they do not say that every value of length
up to the limit is necessarily reachable. `max_states` bounds accepted search states, while
`candidate_eval_guardrail` bounds work spent trying candidates before a successor is accepted.

`state_dedup = "hash_compaction64"` can merge states on collisions. `symmetry_fields` also
merges states intentionally. Neither setting is appropriate when a passing run is meant to
preserve every explored-state distinction. `por_heuristic = "invisible_branch"` removes
branches based on syntactic read/write visibility; it is disallowed together with deadlock
checking because pruning may hide the only outgoing transition.

### Properties and transition semantics

| Key | Default | Meaning and validation |
|---|---|---|
| `properties.invariants` | `[]` | Unique nonempty spec-function names checked on reachable states. |
| `properties.leads_to` | `[]` | Unique `{from,to,name?}` predicate obligations analyzed over the explored graph. Pairs and optional names must be unique. |
| `properties.fairness.weak` | `[]` | Unique `LNext` branch labels used as weak-fairness assumptions in liveness cycle filtering. |
| `properties.fairness.strong` | `[]` | Unique `LNext` branch labels used as strong-fairness assumptions. A label cannot also appear in `weak`. |
| `properties.check_deadlock` | `false` | Report a reached state with no successor. Conflicts with stuttering semantics and with the POR heuristic. |
| `properties.successor_semantics` | `deadlock` | `deadlock` leaves an empty successor set; `stuttering` adds `s_ == s` when no branch is enabled. |

Fairness labels are checked against the branch labels extracted from the selected `LNext`.
Spelling, qualification, and action decomposition therefore matter. Fairness affects only the
bounded liveness check; it does not make safety exploration more complete.

### Resolve and override a configuration

Use `model-config` to parse a file, apply its supported diagnostic overrides, revalidate it, and
print the fully defaulted TOML:

```bash
transpiler/target/debug/verus-transpile model-config \
  --model model.toml \
  --max-depth 16 \
  --max-states 100000 \
  --timeout-ms 60000 \
  --max-seq-len 4 \
  --max-set-len 4 \
  --max-map-len 4 \
  --int-range=-2..5 \
  --nat-max 5 \
  --candidate-eval-guardrail 20000
```

The `model-check` command itself accepts `--max-depth`, `--max-states`, and
`--timeout` (with `--timeout-ms` as an alias), plus `--search`. Repeatable `--invariant`
arguments replace the configured invariant list when at least one is supplied. Other changes
belong in `model.toml`; `model-config` output can be reviewed and saved explicitly if desired.

For evidence, retain both the authored input and the effective values recorded under `search`
and `summary` in the report. A command transcript alone can miss defaults and overrides.

### JSON report: top-level schema

`model-check --json-report` writes one JSON object to standard output. Diagnostics and optional
profiles use standard error. Automation should parse `result`; the process can exit successfully
even when a property violation is reported.

| Field | Shape | Meaning |
|---|---|---|
| `result` | string | Semantic outcome label described below. |
| `protocol`, `types` | string | Source paths actually ingested. |
| `entrypoints` | `{init,next}` | Resolved init and next function names. |
| `invariants` | object | `configured_count`, `resolved_count`, and the corresponding `configured`/`resolved` name arrays. |
| `search` | object | Effective strategy, semantics, reduction/dedup settings, limits, and evidence classification. |
| `summary` | object | State/transition/depth totals, constants coverage, solver telemetry, branch telemetry, and phase timing. |
| `liveness` | object or `null` | Bounded leads-to/fairness status when temporal requirements were configured. |
| `stop_reason` | string | Explorer enum name, distinct from the user-facing `result`. |
| `invariant_violation` | object or `null` | First invariant name, depth, and canonical state key. |
| `deadlock` | object or `null` | First deadlock depth and canonical state key. |
| `leads_to_violation` | object or `null` | Violating SCC/cycle and a representative initial-to-cycle trace. |

The `search` object contains:

| Field | Meaning |
|---|---|
| `strategy` | `bfs`, `dfs`, or `dpor`. |
| `successor_semantics` | Effective `deadlock` or `stuttering` setting. |
| `state_dedup`, `symmetry_fields`, `por_heuristic` | Effective identity and reduction choices. |
| `por_pruned_branches` | Branch labels pruned by the configured invisible-branch analysis. |
| `max_depth`, `max_states`, `timeout_ms` | Effective search limits. |
| `evidence_mode.class` | `exact_proof_strength` or `lossy_bug_finding_accelerator`. |
| `evidence_mode.proof_strength` | Whether the dedup/symmetry classifier considers explored-state distinctions preserved. |
| `evidence_mode.lossy_reasons` | `hash_compaction64_collision_risk`, `symmetry_fields_state_merging`, or both. |
| `evidence_mode.guidance` | Human-readable use guidance for the class. |

The name `exact_proof_strength` is narrower than it sounds. The classifier currently examines
only hash compaction and symmetry fields. It does not prove that the finite domains are complete,
that the depth/state/timeout caps did not truncate the run, that POR preserved the selected
property, that DPOR reporting is complete, or that the evaluator matches an unbounded Verus
specification. Read it as “ordinary selected dedup settings preserve distinctions among the
states this run explores.”

### Summary and telemetry schema

The stable semantic counters at `summary` are:

| Field group | Fields |
|---|---|
| Explored graph | `states`, `transitions`, `depth`, `generated_states`, `distinct_states`, `duplicate_states`, `initial_states`, `explored_states` |
| Constants coverage | `constants_valuations_total`, `constants_valuations_explored` |
| Reductions | `pruned_by_por`, `hash_compaction_collisions`, `symmetry_collapses` |
| Solver paths | `direct_assignment_branch_solves`, `enumeration_fallback_branch_solves`, `enumeration_candidate_evaluations`, `guard_pruned_candidate_evaluations`, `candidate_evaluation_guardrail_per_state_branch`, `successor_cache_hits`, `successor_cache_misses` |
| Wall clock | `elapsed_ms` and the nested `timing` object |

`summary.branch_telemetry` is an array keyed conceptually by `branch_label`. Each entry contains:

| Field group | Fields |
|---|---|
| Volume | `invocations`, `existential_assignment_count`, `candidate_state_count`, `successful_successors` |
| Solver route | `direct_solver_hits`, `enumeration_fallback_hits`, `fallback_reason` |
| Work avoided/performed | `guard_pruned_candidate_evaluations`, `direct_assigned_fields`, `deferred_constraint_evaluations`, `evaluator_calls`, `guard_pruned_assignments` |
| Constraint mix | `eq_constraints`, `predicate_constraints` |
| Timing | `cumulative_solve_elapsed_ms` |

`fallback_reason` is one of `direct`, `no_next_state_assignment`,
`not_all_fields_assigned`, or `unknown`. An increase in fallback and candidate evaluation often
explains a performance regression without any change to the reachable graph.

The `summary.timing` object contains millisecond counters for:

- `source_ingestion_parsing_ms`;
- `model_config_resolution_ms`;
- `initial_state_construction_ms`;
- `successor_solving_ms`;
- `candidate_generation_evaluation_ms`;
- `dedup_hashing_normalization_ms`;
- `invariant_evaluation_ms`; and
- `report_serialization_output_ms`.

These are measurements, not semantic evidence. Preserve them for profiling, but normalize them
out of cross-host drift comparisons.

### Result and stop-reason interpretation

| `result` | Typical `stop_reason` | Interpretation |
|---|---|---|
| `ok` | `FrontierExhausted` | No selected violation was found in the constructed finite graph. Check depth and every configured bound before calling the graph closed. |
| `max_states_reached` | `MaxStatesReached` | Exploration stopped at the distinct-state cap; safety and liveness success are incomplete. |
| `timeout_reached` | `TimeoutReached` | Ordinary exploration reached the wall-clock cap; success is incomplete. |
| `invariant_violated` | `InvariantViolated` | A concrete reached state failed the first reported invariant. |
| `deadlock_detected` | `DeadlockDetected` | Under deadlock semantics, a reached state below the expansion horizon had no successors. |
| `leads_to_violated` | usually `FrontierExhausted` | Bounded SCC analysis found a representative fair cycle violating a configured obligation. |

The ordinary explorers record states at `max_depth` without expanding them and can still return
`FrontierExhausted`. Therefore `FrontierExhausted` is not, by itself, evidence that the
unbounded reachable graph was exhausted. If `summary.depth` reaches `search.max_depth`, report
the result as depth-bounded. The current liveness gate keys on `FrontierExhausted`; it can
analyze this truncated graph, so its conclusion must carry the same depth boundary.

DPOR has an additional schema caveat. The integrated adapter currently returns an empty ordinary
`explored` vector, maps any non-violation completion to `FrontierExhausted`, and does not
propagate ordinary timeout/depth/state stop detail or invariant/deadlock payloads. Graph-based
liveness and parity fields are consequently not authoritative for `--search dpor`. Use BFS or
DFS for report-backed traces, liveness, and cross-engine parity; use current DPOR results as
bounded safety/reduction or bug-finding evidence.

### Liveness and counterexample payloads

When temporal requirements are present, `liveness` contains:

| Field | Meaning |
|---|---|
| `obligations` | Count of resolved `leads_to` obligations. |
| `checked` | Whether graph analysis ran. |
| `violation_found` | Whether one obligation produced a violating component/cycle. |
| `skipped_reason` | For example `incomplete_exploration`, or `null` when checked. |
| `fairness.weak_count/strong_count` | Counts of configured branch-label assumptions. |
| `fairness.weak/strong` | The exact configured labels. |

`invariant_violation` and `deadlock` expose only a canonical state-key string and depth in the
JSON report, even though the explorer retains internal parent/counterexample information. Do not
promise a step-by-step JSON safety trace until that schema is extended.

`leads_to_violation` is richer:

- `obligation`, `from`, and `to` identify the failed property;
- `component_size` records the violating strongly connected component size;
- `cycle_edge.from/to` identifies a representative edge inside it; and
- `counterexample.initial_state` plus `counterexample.steps[]` records the action branch,
  canonical state key, and field-level `diffs[]` with `path`, `before`, and `after`.

This is one representative lasso-style explanation, not a proof that it is the shortest or only
counterexample.

### Parity export schemas

Parity artifacts use one JSON object per line and canonical runtime JSON values. Structs become
objects with stable field order, enum values include `_variant`, sets become sorted arrays, and
maps become sorted `[key,value]` pairs. The comparison tool should compare normalized `state`
values, not assume that IDs from different engines are interchangeable.

The current `--export-parity DIR` implementation writes `DIR/states.jsonl` with:

| Field | Shape |
|---|---|
| `id` | canonical state-key string |
| `state` | canonical JSON runtime value |
| `initial` | Boolean |
| `depth` | nonnegative integer |

Although the CLI help still says “states + edges,” this command's current main path writes only
`states.jsonl`. Treat an expected `edges.jsonl` as a schema/implementation gap, not as evidence
that a zero-edge graph was explored.

`--export-parity-debug DIR` streams three files during ordinary exploration:

| File | Per-line fields |
|---|---|
| `generated_states.jsonl` | `state_id`, `state`, `depth`, `initial`, nullable `branch_label`, nullable `predecessor_state_id`, and `classification` (`accepted_distinct` or `duplicate`) |
| `distinct_states.jsonl` | The same provenance fields except `classification`; one line per first-seen accepted state. |
| `edges.jsonl` | `src`, `dst`, `branch_label`, and successor `depth`. |

Debug edges include transitions to duplicate states. This is useful for first-divergence analysis,
but the files reflect the selected dedup, symmetry, and search settings. DPOR currently does not
populate the ordinary stream needed for a useful equivalent export.

For TLC comparison, follow
[`cross-engine-state-normalization.md`](cross-engine-state-normalization.md) and use
[`scripts/diff_parity_states.py`](../scripts/diff_parity_states.py). Equality of finite
normalized state sets is V2 evidence for the declared observable projection; it is not trace
equivalence or an unbounded refinement proof.

### Checked-in evidence and normalized drift

The project evidence workflow is:

```bash
./scripts/run_model_check_matrix.sh
./scripts/check_model_check_drift.py
```

The matrix script regenerates the artifacts named by
[`reports/model_check/MANIFEST.txt`](../reports/model_check/MANIFEST.txt). The drift checker
compares those artifacts with a Git reference after recursively removing host-dependent timing
fields. It ignores:

- `elapsed_ms`;
- `cumulative_solve_elapsed_ms`;
- the complete `timing` subtree and its named phase counters; and
- the `git_rev:` line in the text manifest.

It deliberately retains `timeout_ms`, despite the suffix, because that is a semantic search
input. It also retains result/stop labels, source paths, state and transition counts, every
non-timing telemetry field, and newly added fields. Review any such drift, regenerate in the
intended working directory, and commit the updated artifacts with the behavior change.

The checked-in matrix is evidence about the exact source revision, fixture, model, command,
engine path, and normalization policy that produced it. A responsible evidence statement names
all of those and answers five questions:

1. **Translation boundary:** Was this TLA+ lint/projection, general translation, or direct Verus
   ingestion?
2. **Execution boundary:** Which evaluator path and search strategy ran, and was graph/tracing
   support complete for it?
3. **Finite boundary:** What constants, type domains, collection limits, depth, state cap, and
   timeout applied?
4. **Reduction boundary:** Were hash compaction, symmetry, POR, or DPOR active?
5. **Property boundary:** Which invariants, deadlock semantics, leads-to obligations, and
   fairness labels were actually resolved?

If any answer is absent, say “bounded bug-finding run” rather than “verified.” If all are present
and ordinary canonical exploration closed below its limits, “exact finite-model evidence under
the recorded bounds” is accurate. Reserve “proved” for separately discharged Verus obligations.

## Appendix F — Protocol and Trust-Boundary Matrix

This appendix separates protocol intent, available proof structure, finite-model
evidence, and runtime usability. The “fault/model” column names the protocol family and
intended environment; it is not by itself a claim that every failure assumption is
formalized or proved. Read the cited logical constants/environment predicates before
making a fault-tolerance claim.

### Protocol status

| Protocol | Purpose and intended fault/model family | Proof surface | Runtime/client status | Source-first status |
|---|---|---|---|---|
| RSL | Multi-Paxos replicated state machine; crash-fault-oriented IronFleet lineage | Extensive `common_proof/` and `refinement_proof/` trees plus generated action contracts | Dedicated UDP server/client; legacy TCP+SSL retained; generic server name also wired | Reproducible unsupported fixture: finite domain for named `LConstants` is missing |
| Paxos | Single-decree Paxos; crash-fault consensus | Generated action/refinement contracts; no separate end-to-end refinement-proof tree | Generic server wired; no current generic benchmark-client mode | Small and safety-invariant cases in the required CI matrix |
| Raft | Leader-based replicated log; crash-fault consensus | Dedicated refinement tree, currently with open assumed lemmas | Generic server and generic client | Reproducible blocker: existential assignment expansion limit |
| EPaxos | Leaderless generalized/fast-path Paxos family; crash-fault consensus | Generated action/refinement contracts; no separate end-to-end refinement-proof tree | Generic server and generic client | Reproducible blocker: constants/state candidate expansion limit |
| PBFT | Byzantine-fault-tolerant state-machine replication | Generated action/refinement contracts; no separate end-to-end refinement-proof tree | Generic server and generic client; benchmark uses four replicas | Best-effort bounded case; may be skipped when state candidates exceed runner limits |
| ChainReplication | Ordered head-to-tail replication; fail-stop/crash-oriented model | Generated action/refinement contracts; no separate end-to-end refinement-proof tree | Generic server wired; no current generic benchmark-client mode | Reproducible blocker: existential assignment expansion limit |
| PrimaryBackup | Primary/backup replication; fail-stop/crash-oriented model | Generated action/refinement contracts; no separate end-to-end refinement-proof tree | Generic server and generic client (`pb`) | Small and safety-invariant cases in the required CI matrix |
| VerticalPaxos | Reconfigurable Paxos family with an external configuration/master role | Generated action/refinement contracts; no separate end-to-end refinement-proof tree | Generic server wired; no current generic benchmark-client mode | Reproducible blocker: existential assignment expansion limit |
| TwoPhase | Two-phase atomic commit; blocking coordinator/participant protocol, not consensus | Generated action/refinement contracts; no separate end-to-end refinement-proof tree | Generic server wired; no current generic benchmark-client mode | Small and safety-invariant cases in the required CI matrix |
| LeaderElection | Bully-style leader-election model; failure-detector/environment assumptions are specification-dependent | Generated action/refinement contracts; no separate end-to-end refinement-proof tree | Generic server wired; no current generic benchmark-client mode | Small and safety-invariant cases in the required CI matrix |

“Generated action/refinement contracts” means executable functions have contracts tying
their Views to logical action predicates where generation succeeded. It is narrower
than an inductive global safety theorem or an end-to-end distributed refinement proof.

### Dated proof-escape snapshot

The following lexical audit was run on 2026-08-05 at commit `189b227a`. It intentionally
scopes counts to `src/protocol/<P>/` and `src/generated/<P>/`; implementation/common/FFI
boundaries are listed separately. `A` is an active statement beginning with
`assume(`, `EB` is an `#[verifier(external_body)]`/`#[verifier::external_body]`
annotation, and `ES` is an `assume_specification` occurrence.

| Protocol | Spec A | Generated A | Generated EB | Spec/generated ES | Interpretation |
|---|---:|---:|---:|---:|---|
| RSL | 0 | 0 | 32 | 0 | No generated active assumes, but many trusted generated helpers/fallback bodies remain. |
| Paxos | 0 | 0 | 1 | 0 | One generated external body. |
| Raft | 12 | 0 | 5 | 0 | Open refinement assumptions and generated external helpers are separate gaps. |
| EPaxos | 0 | 0 | 0 | 0 | No sites in this narrow lexical scope. |
| PBFT | 0 | 0 | 0 | 0 | No sites in this narrow lexical scope. |
| ChainReplication | 0 | 0 | 1 | 0 | One generated external body. |
| PrimaryBackup | 0 | 0 | 0 | 0 | No sites in this narrow lexical scope. |
| VerticalPaxos | 0 | 0 | 1 | 0 | One generated external body. |
| TwoPhase | 0 | 0 | 0 | 0 | No sites in this narrow lexical scope. |
| LeaderElection | 0 | 0 | 1 | 0 | One generated external body. |

These numbers age immediately. Reproduce them rather than copying them into release
claims:

```bash
protocol=RSL
rg -n '^[[:space:]]*assume[[:space:]]*\(' \
  "src/protocol/$protocol" "src/generated/$protocol"
rg -n '^[[:space:]]*#\[verifier(::external_body|\(external_body\))\]' \
  "src/protocol/$protocol" "src/generated/$protocol"
rg -n 'assume_specification' \
  "src/protocol/$protocol" "src/generated/$protocol"

# Generated assume JSON (the input directory is scanned directly, not recursively)
verus-transpile report-assumes --input-dir "src/generated/$protocol"
```

The regex is a review aid, not a semantic Verus audit. It does not prove that contracts
are adequate, detect every macro-generated construct, or explain a boundary's soundness.

### Shared trust/runtime boundaries

All rows inherit boundaries outside the narrow table:

- `src/lib.rs` carries crate-level `#![verus::trusted]`, which places source in the
  trusted/manual-audit classification used by Verus audit tooling. It is not the same
  as counting proof assumptions, and the attribute alone does not say which bodies were
  or were not checked.
- exported Rust ABI functions, raw-pointer ownership, callbacks, and the C# runtime are
  external to ordinary Verus body proofs;
- UDP/TCP delivery, clocks, scheduling, filesystem/configuration parsing, process
  behavior, and cryptographic/platform libraries need explicit environment assumptions
  and runtime tests;
- `src/common/` and `src/implementation/` contain external bodies/specifications for
  collection, marshalling, native I/O, and RSL integration; audit them for an end-to-end
  claim;
- model-check results inherit finite-domain, reduction, evaluator, and fairness choices;
- a verified refinement relation does not establish that the logical requirements are
  the right ones.

For a complete audit, search all of `src`, inspect Verus's trusted-code/line-count
report, and record path, contract, justification, and owner for each accepted site.
Runtime integration status should be tested with the exact client/wire path named in the
table.

## Appendix G — Proof-Pattern Catalog

Each catalog entry has an applicability test. Generate or invoke a pattern only after
that test succeeds; proof text selected by protocol name is technical debt.

### Whole-output equality

**Applies when:** a conjunct assigns an output directly, `out == expression`, and the
expression uses only inputs/previously constructed values.

**Generated shape:** compute the expression once, establish validity and its View, and
fold the equality into the logical predicate.

**Reject when:** the output also receives independent field assignments or appears on
the right before assignment. Harmony/obligation checks should catch these cases.

**Anchors:** `transpiler/src/moder/`, `transpiler/src/checker/`, and translator unit
tests in `transpiler/src/translator/mod.rs`.

### Field-by-field struct construction

**Applies when:** every field of a known structured output is assigned exactly once,
possibly after branch normalization.

**Generated shape:** construct the concrete struct; prove field View equalities and
validity; conclude the relational predicate.

**Reject when:** fields are missing, duplicated, or branches produce different field
sets. Do not fill a logical field with `Default` simply to satisfy Rust.

**Anchors:** struct-construction template in `transpiler/src/templates/` and saturation/
harmony tests in `transpiler/src/checker/`.

### Input-only conjunct extraction

**Applies when:** a conjunct constrains only `+` parameters/constants and does not define
an output.

**Generated shape:** add the normalized fact to `requires`; callers prove it before the
body is entered.

**Reject when:** the clause is actually a post-state invariant or can be derived after
construction. An unnecessary precondition narrows the executable action.

**Counterexample:** moving `s_.field == value` to `requires` would refer to a result that
does not yet exist.

### Conditional correspondence

**Applies when:** logical branches cover the condition and construct coherent outputs.

**Generated shape:** mirror the executable `if`/`match`; in each branch assert the guard,
the constructed Views, and the corresponding logical disjunct.

**Reject when:** the executable condition is only approximately equivalent or one branch
leaves an output underspecified.

**Performance note:** branch-local assertions are usually more stable than unfolding a
large disjunction globally.

### Identity transition and View-preserving clone

**Applies when:** the logical post-state equals the pre-state, or unchanged fields need
to be carried into a functional result.

**Generated shape:** use a verified `clone_up_to_view` whose result View equals the input
View; copy scalar fields directly where their View is identity.

**Reject when:** ordinary `Clone` lacks a usable View-preservation contract. Do not add
an external clone merely because Rust's implementation is intuitively obvious.

**Anchors:** `clone_up_to_view_types`, `verified_clone_fns`, type generation in
`transpiler/src/codegen/mod.rs`, and clone/proof-helper tests in `transpiler/src/lib.rs`.

### Empty mapped set or sequence

**Applies when:** an empty concrete collection maps to a logical collection with a
different element representation.

**Generated shape:** bind the mapping function and mapped collection, prove extensional
equality with the logical empty collection, and invoke the lemma at initialization.

**Reject when:** the element abstraction is partial or lacks the required validity
premise.

**Anchors:** `lemma_empty_set_map`, `lemma_empty_seq_map`, per-field empty-map helpers,
and their tests in `transpiler/src/lib.rs`.

### Set insert/remove commutation

**Applies when:** the concrete update inserts/removes an element and the logical field is
the image of that set under a mapping.

**Generated shape:** prove image/update commutation by extensional equality. Removal also
requires injectivity—or a stronger premise sufficient to distinguish the removed value.

**Reject when:** two concrete values can share one logical image; mapped removal then need
not correspond to logical removal.

**Anchors:** `lemma_set_map_remove_commute` generation and tests in
`transpiler/src/lib.rs`.

### Sequence push and processed-prefix loop

**Applies when:** the body builds a sequence in input order and element abstraction is
stable.

**Generated shape:** track index bounds, output length, and per-index View equality for
the processed prefix; use a push/map commutation lemma; prove the full sequence
extensionally after the loop.

**Reject when:** iteration order is nondeterministic or the specification uses a set/map
semantics instead.

### Deep map abstraction

**Applies when:** concrete map keys and/or values have a non-identity abstraction and the
executable operation is among the analyzed empty/singleton/get/contains/insert/remove/
filter shapes.

**Generated shape:** call the operation-specific `abstractify_*` lemma and maintain map
validity. Use `verified_clone_fns` when a checked clone exists.

**Reject when:** the operation changes collision behavior under key abstraction or a
filter predicate is not preserved.

**Anchors:** `map_fields` handling and proof-helper generation in
`transpiler/src/lib.rs`; RSL learner-state mappings are the main real example.

### Set cardinality bridge

**Applies when:** the logical guard compares `Set` cardinality and the executable field
is a valid `HashSet` representation whose View has the intended membership.

**Generated shape:** establish finite domain/membership correspondence, then bridge
concrete length to logical cardinality before using the guard.

**Reject when:** duplicate/colliding abstraction can change cardinality or validity is
not known.

**Anchors:** `set_fields`-driven cardinality proof injection in the translator and Raft
generation tests.

### Mutable-state refinement

**Applies when:** the first state parameter is configured in `mut_self_types` and the
action can be implemented without an unsupported intermediate whole-state assignment.

**Generated shape:** express pre-state facts through `old(self)@`, mutate fields, prove
post validity, and establish the logical action between `old(self)@` and `self@`.

**Reject when:** aliasing, early return, or intermediate replacement invalidates the
analyzed update sequence. Fall back to the functional convention as a supported design,
not a hand-written generated-file wrapper.

### Quantifier trigger with arithmetic index

**Applies when:** Verus selects an unstable/arithmetic trigger for a quantified array or
sequence fact.

**Proof shape:** introduce a separate index variable, relate it arithmetically (for
example `j == i + 1`), and trigger on the meaningful collection/function term involving
`j`.

**Reject when:** the proposed trigger does not contain every bound variable or can match
too broadly. Capture inventory and timing before/after.

**Anchors:** source sites from `scripts/trigger_sites.py` and workflow in
[`phase54-trigger-workflow.md`](phase54-trigger-workflow.md).

### Recursive fold/batch equivalence

**Applies when:** executable code processes a finite sequence in a loop/fold while the
logical function is recursive or relational over the same order.

**Generated shape:** prove a prefix accumulator invariant and a lemma connecting one
executable step to one logical recursive step; termination uses the remaining length.

**Reject when:** executable reordering, early termination, or batching changes observable
semantics. A trusted fold-equivalence contract must remain visible until induction is
proved.

### Unreachable branch

**Applies when:** a branch is impossible from checked preconditions and invariants.

**Generated shape:** prove `false` locally and use an unreachable expression only after
that proof.

**Reject when:** impossibility is only expected runtime behavior. A generated trusted
`unreachable_value` helper turns a missing proof into a TCB obligation.

### Trust-boundary decision

When no pattern applies, choose in this order:

1. correct the executable body if it does not implement the relation;
2. derive a real caller-proved precondition for an input-only constraint;
3. add a reusable checked View/collection/control-flow lemma;
4. restructure quantifiers and measure solver behavior;
5. place the narrowest external specification at a genuine library/environment boundary;
6. record the boundary, soundness argument, owner, guard, and removal plan.

Never treat `assume`, `assume(false)`, proof fallback, manual generated code, or an
external body as a proof pattern. `#[verus::trusted]` is also not a proof pattern: it is
an audit/TCB classification that calls for manual inspection, separate from the direct
proof assumptions just listed.

## Appendix H — Glossary, Error Index, and Further Reading

### Glossary

| Term | Meaning in this project |
|---|---|
| TLA+ | A state-machine specification language based on temporal logic of actions. |
| TLC | The standard explicit-state model checker for TLA+ modules. |
| Verus | A deductive verifier for Rust that checks specifications, proofs, and executable contracts. |
| SMT | Satisfiability Modulo Theories; the automated logical reasoning used beneath Verus. |
| `spec fn` | Pure ghost-level mathematical function; not runtime code. |
| `proof fn` | Ghost proof procedure erased from execution. |
| `exec fn` | Executable function checked against its Verus contract. |
| Ghost code | Specification/proof data or computation erased before normal execution. |
| View | A mapping, written with `@`, from a concrete value to its logical abstraction. |
| Refinement | A relation/proof showing that concrete steps correspond to allowed abstract steps. |
| Invariant | A predicate intended to hold in every reachable state. An inductive proof needs initialization and preservation. |
| Safety | A property that rules out bad finite behavior, often expressed as invariants. |
| Liveness | A property requiring desired progress eventually. |
| Fairness | A scheduling assumption used to exclude unfair infinite executions in liveness reasoning. |
| State space | Reachable states and transitions of a resolved model. |
| Finite-domain expansion | Enumerating bounded concrete candidates for symbolic values during source-first checking. |
| Relational predicate | A logical function that constrains inputs and outputs rather than returning the output directly. |
| Functionalization | Converting a well-moded relation into an executable function or mutation. |
| AutoMan mode | `+` caller-supplied input or `-` generated output. |
| Saturation | Every output/member is assigned. |
| Harmony | No output/member is assigned incompatibly more than once. |
| Obligation | No output is read before assignment. |
| POR | Partial-order reduction: prunes redundant interleavings using action independence. |
| DPOR | Dynamic partial-order reduction: discovers relevant independence/conflicts during exploration. |
| Canonicalization | Stable state normalization used for equality, symmetry, and deduplication. |
| Parity | Structural/semantic comparison of states, edges, or artifacts from two paths/engines. |
| Trusted computing base (TCB) | Code, contracts, tools, and environment assumptions relied upon without an internal proof of the whole behavior. |
| `assume(P)` | Adds proposition `P` to the proof context without proving it at that site. |
| `external_body` | Trusts a function's specified contract without checking its body in the ordinary way. |
| `#[verus::trusted]` | Marks source for Verus's trusted/manual-audit classification; inventory separately from direct assumptions. |
| FFI | Foreign-function interface between Rust and the C# runtime. |
| Generated artifact | Derived checked-in code that must be reproduced from spec, annotation, config, and transpiler sources. |

### Error index

| Message or symptom | First checks | See |
|---|---|---|
| `Failed to read`, file not found | Working directory, relative path, generated prerequisite | Chapters 2, 16; Appendix A |
| annotation/module/entry parse error | One declaration per line, braces, semicolon, `//` comment, module path | Chapter 18; Appendix B |
| mode count/signature mismatch | Spec parameter order and helper/predicate form | Chapter 17; Appendix B |
| saturation failure | Missing output or field, incomplete branch | Chapters 17–18; Appendix B |
| harmony/duplicate assignment | Overlapping clauses or branches assign the same output | Chapters 17–18; Appendix B |
| obligation/read-before-assignment | Output used before construction | Chapters 17–18; Appendix B |
| unsupported expression/template/type | Reduce a fixture; inspect parser/type/template coverage | Chapters 17 and 27 |
| `TRANSLATE-GAP`, auto-skipped function | Unsupported lowering; do not accept skipped output as complete | Chapters 17 and 19 |
| `PROOF-GAP`, fallback stub | Missing generated proof support; inspect new external body | Chapters 19–20; Appendix G |
| no method `valid` / View type mismatch | `primitive_types`, `skip_valid_types`, View mappings, validity name | Chapter 18; Appendix C |
| failed postcondition/assertion | Read requires/body/validity/refinement contract in order | Chapter 20 |
| `rlimit exceeded` | Module isolation, trigger inventory, quantifier shape, timing | Chapters 20 and 25 |
| automatic trigger note changed | Compare same-mode inventories under same Verus release | Chapter 25; trigger workflow |
| Verus launcher/glibc error | Pinned runner requirements or `scripts/verify_local.sh` | Chapters 16 and 26 |
| SCons cannot find Verus | Pass the executable path, not only its directory | Chapter 16 |
| checked-in generation differs | Rebuild transpiler, compare exact inputs/config/order, find manual drift | Chapters 19 and 24 |
| missing model domain | Add a finite domain for the named type/constant; inspect resolved config | Chapters 8 and 22; Appendix E |
| candidate/existential expansion guardrail | Shrink/configure the domain or improve construction; do not just hide the limit | Chapters 22, 25, and 27 |
| invariant/liveness violation | Preserve trace; classify protocol, abstraction, or evaluator defect | Chapter 24; Appendix E |
| timeout/max-depth/max-states | Result is bounded, not exhausted; inspect hot phase and telemetry | Chapters 24–25 |
| clean-subset rejection | Run `tla-lint`; repair C1–C5 violations before `clean-tla` | Chapters 9 and 23; Appendix D |
| unknown protocol or wire decode failure | Rust/C# dispatch list, tag/field order, endpoint encoding | Chapter 21; Appendix F |
| Cargo build-lock contention | Avoid parallel regeneration tests; use documented single-thread mode | Chapters 16 and 19 |

### Further reading

- Project landing page, quickstart, essential commands, and attribution:
  [`README.md`](../README.md).
- IronFleet methodology and RSL lineage: [IronFleet paper](https://doi.org/10.1145/2815400.2815428)
  and [original source](https://github.com/microsoft/Ironclad/tree/main/ironfleet).
- AutoMan's relational-to-executable workflow: [AutoMan paper](https://doi.org/10.1145/3731569.3764822)
  and [source](https://github.com/stonysystems/automan).
- Verus language and proof guide: [Verus guide](https://verus-lang.github.io/verus/guide/).
  For trust terminology, read the [Verus TCB chapter](https://verus-lang.github.io/verus/guide/tcb.html)
  and the [trusted-code line-count tool](https://github.com/verus-lang/verus/blob/main/source/tools/line_count/README.md).
- TLA+ language and tools: [TLA+ home](https://lamport.azurewebsites.net/tla/tla.html)
  and [TLA+ tools repository](https://github.com/tlaplus/tlaplus).
- Dynamic partial-order reduction: Flanagan and Godefroid,
  [“Dynamic Partial-Order Reduction for Model Checking Software”](https://doi.org/10.1145/1040305.1040315).
- Verified IronKV, from which selected I/O, utility, marshalling, and interop code was
  adapted: [verified-ironkv](https://github.com/verus-lang/verified-ironkv).
- Current project internals: [`model_checker_status.md`](model_checker_status.md),
  [`model-checker-architecture/glossary.md`](model-checker-architecture/glossary.md),
  [`phase54-trigger-workflow.md`](phase54-trigger-workflow.md), and Chapters 17–25.

The project is MIT licensed; see [`LICENSE`](../LICENSE). Attribution details and the
division between imported foundations and project-specific extensions are in the README.
