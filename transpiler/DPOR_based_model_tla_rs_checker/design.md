# DPOR-Based Model Checker — Design Notes

## Workfolder Organization Decision (Phase 38.1.2)

**Decision**: This workfolder is a **separate Cargo crate** (`dpor-checker`)
under `transpiler/DPOR_based_model_tla_rs_checker/`.

**Rationale**:
- **Isolation**: A separate crate prevents accidental coupling with the
  existing `transpiler/src/modelcheck/` code during early prototyping.
- **Independent testing**: The crate can have its own `cargo test` without
  polluting the transpiler's test suite.
- **Clear integration boundary**: When the prototype matures, integration
  means adding a dependency edge, not untangling interleaved code.
- **Shared types later**: The crate can depend on `verus-transpiler` as a
  library for shared types (`RuntimeValue`, `canonical_key`, etc.) when
  needed, without the reverse dependency.

The Cargo crate will be initialized when implementation begins (Phase 38.5+).
Until then, the workfolder contains design docs, test corpus, and scripts.

---

## Upstream References (Phase 38.2.1 / 38.2.2)

### GenMC (`https://github.com/MPI-SWS/genmc`)

- **Inspected**: 2026-03-25
- **Commit**: `22d3d0b44dedb4e8e1aae3330e546465e4664529` (master)
- **Repo areas reviewed**: README.md, doc/manual.md, src/ directory listing
- **Architecture summary**:
  GenMC is a stateless model checker for C programs operating at the LLVM-IR
  level. It constructs *execution graphs* (not explicit state spaces) and
  uses a "sound, complete, and optimal" DPOR technique. Key architectural
  components: LLVM-IR interpreter, execution graph construction,
  consistency checking against memory models (SC, TSO, RA, RC11, IMM),
  and symmetry reduction / barrier-aware model checking (BAM).
  Source structure: `src/` with `Interpreter.{h,cpp}`, `Execution.cpp`,
  `ExternalFunctions.cpp`; `doc/` with manual; `tests/` for validation.
- **What to borrow (conceptually)**:
  - Execution graph as the core data structure (rather than explicit state storage)
  - Layered architecture: interpreter → graph builder → consistency checker → explorer
  - Stateless exploration (reconstruct execution rather than store all states)
  - Separation of memory-model consistency from exploration strategy
- **What NOT to copy**:
  - LLVM-IR-specific infrastructure (we operate on tla-rs spec predicates, not C code)
  - Full production complexity (GenMC handles C11/C++11 atomics, relaxed memory — irrelevant for TLA+ state machines)
  - External function handling (C library stubs)
- **tla-rs mapping**:
  - GenMC's "thread" → tla-rs "process" (server/node in a distributed protocol)
  - GenMC's "memory access" → tla-rs "field assignment in next-state predicate"
  - GenMC's "execution graph" → tla-rs "trace of (process_id, action_branch, state) tuples"
  - GenMC's consistency check → tla-rs invariant checking on reached states

### Nidhugg (`https://github.com/nidhugg/nidhugg`)

- **Inspected**: 2026-03-25
- **Commit**: `9e86fc0e0e3922e2d21c5bcf7a3d5db42e585056` (master)
- **Repo areas reviewed**: README, src/ file listing (via GitHub API)
- **Architecture summary**:
  Nidhugg is a stateless model checker for concurrent C/C++ programs at
  LLVM-IR level. Supports SC, TSO, PSO, POWER, ARM memory models. The
  key architectural pattern is `DPORDriver` + pluggable `TraceBuilder`
  implementations:
  - `DPORDriver.{cpp,h}` — main exploration driver
  - `TraceBuilder.{cpp,h}` — base class for trace-building strategies
  - `TSOTraceBuilder.{cpp,h}` — TSO-specific DPOR
  - `PSOTraceBuilder.{cpp,h}` — PSO-specific DPOR
  - `RFSCTraceBuilder.{cpp,h}` — Reads-From Sequential Consistency (optimal DPOR)
  - `DetCheckTraceBuilder.{cpp,h}` — determinism checking
  - `Trace.{cpp,h}` — execution trace representation
  - `BVClock.{cpp,h}`, `FBVClock.{cpp,h}` — bit-vector clock / fast bit-vector clock
  - `Execution.cpp` — execution infrastructure
  - `CPid.{cpp,h}` — process/thread IDs
  Source-DPOR, optimal-DPOR, and RFSC are the key algorithm variants.
- **What to borrow (conceptually)**:
  - `DPORDriver` + `TraceBuilder` separation: driver controls exploration loop, trace builder implements the specific DPOR algorithm
  - The `TraceBuilder` interface pattern: each DPOR variant is a pluggable strategy
  - Vector clock (`BVClock`) for happens-before tracking between processes
  - `CPid` for compact process identification
  - Source-DPOR as the starting algorithm (simplest correct DPOR)
  - Backtrack set computation from the trace builder
- **What NOT to copy**:
  - LLVM-IR interpreter infrastructure
  - Memory-model-specific trace builders (TSO, PSO, POWER, ARM)
  - C/pthreads-specific concurrency primitives
- **tla-rs mapping**:
  - `DPORDriver` → `DporExplorer` (our exploration loop)
  - `TraceBuilder` → `DporStrategy` trait (pluggable DPOR algorithms)
  - `Trace` → `ExecutionTrace` (sequence of (process, action, state) events)
  - `BVClock` → `VectorClock` (happens-before tracking between tla-rs processes)
  - `CPid` → `ProcessId` (derived from protocol server/node index)
  - `RFSCTraceBuilder` → future optimal DPOR (not v1)

### CDSChecker (`https://github.com/computersforpeace/model-checker`)

- **Inspected**: 2026-03-25
- **Commit**: `5c4efe5cd8bdfe1e85138396109876a121ca61d1`
- **Repo areas reviewed**: README, source file listing, output format examples
- **Architecture summary**:
  CDSChecker is a C11/C++11 model checker that exhaustively explores
  concurrent behaviors using partial order reduction. Compact source
  structure with clear data abstractions:
  - `model.{cc,h}` — main model checker engine
  - `execution.{cc,h}` — execution representation
  - `schedule.{cc,h}` — scheduler for thread interleavings
  - `nodestack.{cc,h}` — search stack for backtracking
  - `action.{cc,h}` — individual operation/event representation
  - `clockvector.{cc,h}` — Lamport vector clocks for happens-before
  - `cyclegraph.{cc,h}` — constraint/cycle detection
  - `hashtable.h` — state deduplication
  - `datarace.{cc,h}` — data race detection
  - `scanalysis.{cc,h}`, `traceanalysis.h` — trace analysis
  Execution traces are recorded with columns: sequence#, thread_id,
  action_type, memory_ordering, location, value, reads_from, clock_vector.
- **What to borrow (conceptually)**:
  - Compact `Action` struct: (seq_no, process_id, action_type, target, value)
  - `NodeStack` for search backtracking (stack of decision points with alternatives)
  - `ClockVector` for happens-before (Lamport timestamps per process)
  - `Execution` as sequence of actions with dependency tracking
  - `Schedule` as the sequence of process choices at each step
  - Hash table for state fingerprinting / deduplication
- **What NOT to copy**:
  - C/C++ memory model specifics (memory orderings, atomics, promises)
  - `cyclegraph` (cycle detection for memory model consistency — not needed for TLA+)
  - Thread-level implementation details (pthreads, libthreads)
- **tla-rs mapping**:
  - `Action` → `TlaAction { seq: usize, process: ProcessId, branch: String, state_delta: StateDiff }`
  - `NodeStack` → `BacktrackStack` (decision points where alternative process choices exist)
  - `ClockVector` → `VectorClock<ProcessId>` (per-process Lamport timestamps)
  - `Execution` → `ExecutionTrace` (ordered sequence of TlaActions)
  - `Schedule` → `ProcessSchedule` (sequence of process_id choices)
  - `hashtable` → reuse `canonical_key()` fingerprinting from existing checker

---

## DPOR Concept Selection Table (Phase 38.2.3)

| Concept | Source | Borrow / Adapt / Reject | tla-rs Mapping | Notes |
|---------|--------|------------------------|----------------|-------|
| Stateless exploration | GenMC | **Adapt** | Replay traces instead of storing full state graph | TLA+ specs are deterministic per (state, action), so replay is feasible |
| Execution graph | GenMC | **Adapt** | Event trace with happens-before edges | Simpler than GenMC's full graph — no memory model consistency needed |
| DPORDriver + TraceBuilder | Nidhugg | **Borrow** | `DporExplorer` + `DporStrategy` trait | Core architecture pattern for pluggable DPOR variants |
| Source-DPOR algorithm | Nidhugg | **Borrow** | First algorithm to implement | Conservative, correct, well-understood |
| Optimal-DPOR / RFSC | Nidhugg | **Defer** (v2+) | Future optimization | Only after source-DPOR works correctly on all 20 cases |
| Vector clocks | CDSChecker, Nidhugg | **Borrow** | `VectorClock<ProcessId>` | Track happens-before between tla-rs process steps |
| Action representation | CDSChecker | **Adapt** | `TlaAction { seq, process, branch, state_delta }` | Replace memory-access fields with TLA+ branch/state fields |
| NodeStack / backtrack stack | CDSChecker | **Borrow** | `BacktrackStack` with per-node alternative sets | Decision points where different process choices are available |
| Sleep sets | Nidhugg, GenMC | **Defer** (v2+) | Future optimization after source-DPOR | Requires correct dependence relation first |
| Wakeup trees | Nidhugg | **Defer** (v2+) | Future optimization | Advanced; not needed for conservative v1 |
| Symmetry reduction | GenMC | **Defer** (v2+) | Reuse existing Phase 36 symmetry infrastructure | Only if v1 performance is insufficient |
| State fingerprinting | CDSChecker, Phase 36 | **Reuse** | `canonical_key()` or u64 fingerprint | Mirror Phase 36's canonical JSON / SHA-256 scheme |
| Memory model consistency | GenMC, CDSChecker | **Reject** | Not applicable | TLA+ operates under sequential consistency by design |
| C/LLVM IR interpretation | All three | **Reject** | Not applicable | tla-rs uses spec predicate evaluation, not program interpretation |
| Barrier-aware checking | GenMC | **Reject** | Not applicable | No barrier primitives in TLA+ |

---

## tla-rs-Specific Design Questions (Phase 38.2.4)

### 1. What is the checker input contract for translated tla-rs specs?

The checker takes:
- A tla-rs spec module with `Init` and `Next` predicates (Verus `spec fn`)
- A set of invariant predicates to check
- A model configuration (constant assignments, finite domains, bounds)
- Optionally: process-id extraction metadata (which state fields identify a "process")

The existing `transpiler/src/modelcheck/` infrastructure already parses these
inputs and builds transition IR. The DPOR prototype should reuse or mirror
this input contract.

### 2. What is the unit of concurrency?

In TLA+, the `Next` predicate is a disjunction of actions, each typically
parameterized by a process/server ID:
```
Next == \E server \in Servers: \/ Action1(server)
                                \/ Action2(server)
                                \/ ...
```

The unit of concurrency is **(process_id, action_branch)** — a specific
server taking a specific action. Two steps are *concurrent* if they
involve different process IDs. Steps by the same process are sequentially
ordered.

### 3. How is `ProcessId` identified?

For protocol specs, `ProcessId` is derived from the existential quantifier
variable in the `Next` predicate (e.g., `server` in `\E server \in Servers`).
The existing checker's transition IR already identifies this as the
"branch existential" — the outer variable over which actions are parameterized.

For specs without an explicit process parameter (e.g., single-process
micro-models), all transitions share `ProcessId = 0` and DPOR degenerates
to exhaustive exploration (which is correct).

### 4. What is the initial conservative dependence relation?

Two transitions `(p1, a1)` and `(p2, a2)` are **dependent** if:
- `p1 == p2` (same process — always dependent), OR
- They read/write overlapping state fields (conservative: any shared field access)

The initial v1 relation is: **all cross-process transitions are dependent**
(i.e., no reduction). This is correct but provides no DPOR benefit.

The first useful refinement: transitions by different processes are
**independent** if they modify disjoint sets of state fields. This is
statically derivable from the spec's field-assignment structure, which the
existing solver already analyzes (see `direct_assigned_fields` telemetry).

### 5. What is the event trace representation?

```rust
struct TlaEvent {
    seq: usize,                    // Global sequence number
    process_id: ProcessId,         // Which process stepped
    action_branch: String,         // Which Next disjunct was taken
    pre_state: StateFingerprint,   // u64 fingerprint of state before step
    post_state: StateFingerprint,  // u64 fingerprint of state after step
    clock: VectorClock,            // Lamport vector clock at this event
}

struct ExecutionTrace {
    events: Vec<TlaEvent>,
    backtrack_points: Vec<BacktrackPoint>,  // Unexplored alternatives
}
```

### 6. What data is stored for backtrack sets, sleep sets, wakeup tree nodes?

**v1 (source-DPOR)**:
- **Backtrack set**: At each event in the trace, a `BTreeSet<ProcessId>` of
  processes that should be explored as alternatives at this decision point.
- **Done set**: `BTreeSet<ProcessId>` of processes already explored.
- Sleep sets and wakeup trees are **out of scope for v1**.

**v2+ (with sleep sets)**:
- **Sleep set**: `BTreeSet<(ProcessId, ActionBranch)>` of transitions to skip.
- **Wakeup tree**: deferred to v3+ (requires optimal-DPOR).

### 7. What is out of scope for v1?

- Liveness / fairness checking (leads-to, temporal properties)
- Weak / relaxed memory models (TLA+ is sequentially consistent)
- Symbolic solving or constraint-based exploration
- Sleep sets, wakeup trees, optimal-DPOR (v2+)
- Integration with `transpiler/src/modelcheck` (must earn it via regression suite)

---

## Core DPOR Runtime Types (Phase 38.7.1)

The following types are the core runtime objects for the DPOR prototype.
They are defined here first (design.md) and will be implemented in Rust
when Phase 38.8 begins.

```rust
/// Identifies a process/actor in the protocol.
/// For distributed protocols: server/node index.
/// For single-process specs: always ProcessId(0).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProcessId(pub u32);

/// Identifies a specific action branch within the Next predicate.
/// E.g., "LTMRcvPrepared", "LTMCommit", "LAdd" — corresponds to
/// one disjunct in the Next == A1 \/ A2 \/ ... predicate.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ActionId {
    pub branch_label: String,
    pub process: ProcessId,
}

/// A single step in an execution trace.
/// Represents one process taking one action, producing a successor state.
#[derive(Clone, Debug)]
pub struct Event {
    pub seq: usize,                       // Global sequence number (0-indexed)
    pub action: ActionId,                 // Which process took which action
    pub pre_state: StateFingerprint,      // State before this step
    pub post_state: StateFingerprint,     // State after this step
    pub clock: VectorClock,               // Lamport vector clock at this event
}

/// Compact state identity for dedup and comparison.
/// Mirrors Phase 36's canonical_key() / u64 fingerprint scheme.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct StateFingerprint(pub u64);

/// Lamport vector clock indexed by ProcessId.
/// Used to track happens-before between events.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct VectorClock {
    pub clocks: BTreeMap<ProcessId, u64>,
}

impl VectorClock {
    pub fn tick(&mut self, process: ProcessId) {
        *self.clocks.entry(process).or_insert(0) += 1;
    }
    pub fn merge(&mut self, other: &VectorClock) {
        for (&pid, &ts) in &other.clocks {
            let entry = self.clocks.entry(pid).or_insert(0);
            *entry = (*entry).max(ts);
        }
    }
    pub fn happens_before(&self, other: &VectorClock) -> bool {
        self.clocks.iter().all(|(&pid, &ts)| {
            ts <= *other.clocks.get(&pid).unwrap_or(&0)
        }) && self != other
    }
}

/// An ordered prefix of an execution: a sequence of events from the initial state.
#[derive(Clone, Debug)]
pub struct ExecutionPrefix {
    pub events: Vec<Event>,
    pub initial_state: StateFingerprint,
}

/// The set of processes that are enabled (have at least one valid transition)
/// in a given state.
pub type EnabledSet = BTreeSet<ProcessId>;

/// At each event in the trace, records which alternative processes should be
/// explored at this decision point (source-DPOR backtrack insertion).
#[derive(Clone, Debug, Default)]
pub struct BacktrackInfo {
    pub backtrack: BTreeSet<ProcessId>,   // Processes to try as alternatives
    pub done: BTreeSet<ProcessId>,        // Processes already explored here
}

/// Per-event sleep set (v2+, initially empty).
pub type SleepSet = BTreeSet<ActionId>;

/// Wakeup tree node (v3+, placeholder).
pub struct WakeupTree {
    // Deferred — not implemented in v1
}
```

---

## Event Model Decision (Phase 38.7.2)

**Decision**: A tla-rs step becomes a DPOR event as
**(process_id, branch_label, concrete_existential_bindings)**.

**How it works**:
1. The `Next` predicate is a disjunction: `Next == \E p \in Procs: A1(p) \/ A2(p) \/ ...`
2. The model checker's transition IR decomposes this into branches, each with:
   - A `branch_label` (e.g., "LTMRcvPrepared")
   - Existential variables (e.g., `p`, `r`, `sender`)
   - A solver that produces successor states
3. For DPOR, the **unit of scheduling** is `(process_id, branch_label)`:
   - `process_id` = the existential variable that identifies the acting process
   - `branch_label` = which action disjunct was taken
4. Two events at the same sequence position are **alternative interleavings**
   if they have different `process_id` values.

**Tradeoffs**:
- **Coarser than helper-expanded steps**: We don't decompose a single action
  into sub-steps. This is simpler but may miss independence within an action.
- **Finer than branch-only**: We distinguish by process_id, not just branch label.
  This enables DPOR to skip interleavings between independent processes.
- **Practical**: Matches the existing checker's branch/solver structure.

---

## Conservative Dependence Relation (Phase 38.7.3)

**v1 dependence relation** (conservative over-approximation):

Two events `e1 = (p1, a1)` and `e2 = (p2, a2)` are **dependent** if:
- `p1 == p2` (same process — always dependent), **OR**
- They both appear in the same execution and the post-state of one differs
  depending on whether the other has already occurred (observable effect).

**v1 implementation** (simplest correct approach):
- **All cross-process events are dependent** (no reduction).
- This is trivially sound: it explores every interleaving, same as BFS/DFS.
- DPOR with this relation degenerates to exhaustive exploration.

**v1.1 refinement** (first useful reduction):
- Two events are **independent** if they modify **disjoint sets of state fields**.
- The existing solver already tracks `direct_assigned_fields` per branch.
- Static analysis: if `branch_A` writes only `{s.x, s.y}` and `branch_B` writes
  only `{s.z}`, and neither reads the other's written fields, they are independent.
- This is a **field-level** independence check, not a value-level check.

**Why conservative is OK**: Missing reductions means exploring more interleavings
(slower but correct). Missing bugs means under-approximating dependence (unsound).
v1 is correct by construction; v1.1 must be validated against v1 on all small cases.

---

## Process Identity Derivation (Phase 38.7.4)

| Case | Protocol | ProcessId derivation | Notes |
|------|----------|---------------------|-------|
| 01 | APlusB | `ProcessId(0)` (single process) | No concurrency |
| 02 | CounterIncDec | Existential `p` in `\E p \in Procs` | Process = thread |
| 03 | CounterRaceBug | Existential `p` in `\E p \in Procs` | Process = thread |
| 04 | LockBasic | Existential `p` in `\E p \in Procs` | Process = thread |
| 05 | BrokenLockBug | Existential `p` in `\E p \in Procs` | Process = thread |
| 06 | TicketLock | Existential `p` in `\E p \in Procs` | Process = thread |
| 07 | ProducerConsumer | Action name (`Produce`/`Consume`) | 2 implicit processes |
| 08 | BoundedBuffer | Action name (`Produce`/`Consume`) | 2 implicit processes |
| 09 | PetersonMutex | Existential `p` in `\E p \in P` | P = {0, 1} |
| 10 | BakeryMutex | Existential `p` in `\E p \in Procs` | Process = thread |
| 11 | ReadersWriters | Existential `r`/`w` in `\E r \in Readers` / `\E w \in Writers` | Two process families |
| 12 | DiningPhilosophers | Existential `p` in `\E p \in Phil` | Process = philosopher |
| 13 | TwoPhase | Existential `r` in `\E r \in RM` + TM actions | RM processes + 1 TM |
| 14 | LeaderElection | Existential `node` in branch params | Process = node |
| 15 | ChainReplication | Existential `c` / node id in branch params | Process = chain node |
| 16 | PrimaryBackup | Existential `c` / node id in branch params | Process = primary/backup |
| 17 | Paxos | Existential over acceptors/proposers | Process = acceptor/proposer |
| 18 | PBFT | Node id in branch params | Process = replica |
| 19 | EPaxos | Node id in branch params | Process = replica |
| 20 | Raft | Server id in branch params | Process = server |

---

## Phase 38.14 — "20/20 ALL GREEN" Honest Postmortem (2026-04-09)

### Summary

The Milestone M9 "20/20 ALL GREEN" claim from 2026-04-01 (commits `4a232ed`,
`8e9aef8`, `79dd5b8`, `96a4253`, `0855bd2`, `ded3b81`) **does not survive
audit**. After running the new structural stub detector
(`scripts/detect_stub_specs.py`) and re-reading the source TLA+ files,
**8 of the 20 cases — every single protocol case (13–20) — pass vacuously**.
The honest baseline-checker score is **12/20**, not 20/20:

| Case range | Status | Notes |
|---|---|---|
| 01–12 | **Real pass** (12/12) | Micro-models and concurrency primitives. Honest invariants, honest verdicts, plausible state counts. |
| 13–20 | **Vacuous pass** (8/8) | All 8 protocol cases either explore 0 states, have stuttering Next, drop actions, have tautological invariants, check no invariant at runtime, or all of the above. |

The Phase 38.8.2.a translator fixes that flipped 16/20 → 20/20 only achieved
clean exit codes from `verus-transpile model-check`. They did **not** verify
that the translated specs were semantically meaningful, that invariants were
non-tautological, that state spaces were non-empty, or that runtime invariant
checking was actually wired through.

### Two distinct root causes

#### Bug A — degenerate hand-written source TLA+ stubs

Cases 13, 17, 18, 20 use hand-authored "small" TLA+ files that are themselves
stubs. The translator faithfully translates them; the translation is correct,
the **input is broken**.

- **17_paxos_small** ([Paxos.tla:38](../tests/tla/17_paxos_small/Paxos.tla)):
  ```tla
  Next == msgs' = msgs /\ maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVal' = maxVal
  TypeOK == msgs = msgs /\ maxBal = maxBal
  ```
  Literal stuttering frame as Next, literal `X = X` as TypeOK. The Send1a/1b/2a/2b
  actions are defined but never invoked. `Acceptor`, `Quorum`, `Value` constants
  are declared but never referenced.

- **20_raft_small** ([Raft.tla:38-41](../tests/tla/20_raft_small/Raft.tla)):
  ```tla
  Next == BecomeCandidate \/ BecomeLeader \/ StepDown
  AtMostOneLeader == state = Leader => votesGranted = votesGranted
  ```
  Single-node role automaton. `GrantVote(voter)` is defined but dropped from
  Next (it has an extra parameter). The "safety" invariant is `X => X`. The
  `Server` constant is declared but never referenced. There is no log, no
  AppendEntries, no commitIndex — none of Raft is modeled.

- **13_twophase_small** ([TwoPhase.tla:19](../tests/tla/13_twophase_small/TwoPhase.tla)):
  `Next == TMCommit \/ TMAbort` — drops `TMRcvPrepared(r)`. No safety invariant.

- **18_pbft_small** ([PBFT.tla:54](../tests/tla/18_pbft_small/PBFT.tla)):
  `Next == EnterCommit \/ ExecuteAndReply \/ ViewChange` — drops the three
  parameterized `Send*` actions, leaving prepareCount/commitCount permanently
  zero, which makes Prepared/Committed/EnterCommit/ExecuteAndReply unreachable.
  `CommitSafety` is non-tautological but never checked at runtime.

The structural pattern is consistent: **the test author dropped every action
that takes parameters beyond `(s, s_, c)` from the Next disjunction**, probably
to avoid setting up existential bindings. This makes the resulting specs
trivially small — and trivially uninteresting.

#### Bug B — Verus → TLA+ → spec roundtrip degradation

Cases 14, 15, 16, 19 use auto-generated TLA+ from `verus2tla`. The source TLA+
files are real and meaningful (e.g., [Election.tla:111-127](../tests/tla/14_leader_election_small/Election.tla)
has 7 actions and 3 honest safety invariants), but the **TLA+ → spec
roundtrip** then collapses them into garbage. Diagnostic fingerprint of every
Bug B case (verified by `detect_stub_specs.py`):

1. `LState = LRecord` flat alias whose fields are scraped from message records
   (`leader`, `responder`, `sender`) instead of the real state fields
   (`electing`, `alive`, `has_leader`, ...).
2. `LInit` parameter `s` typed as `int` rather than `LState`, so the
   model checker cannot construct an initial state object.
3. Every operator body is a soup of `arbitrary::<T>()` calls (15+ per body)
   because every dot-access on the wrong-typed `s` falls back to nondet.
4. Predicates degenerate to `Set::empty().contains(x) ==> Set::empty().contains(x)`,
   `arbitrary::<bool>() == false`, and `arbitrary::<int>() == arbitrary::<int>()`.
5. `distinct_states = 0` at runtime — the explorer can't even start.
6. `result = "ok"` because no exception was raised, no invariant was checked,
   and the empty frontier was "exhausted" trivially.

The Phase 38.8.2.a "translator fixes" (state-variable inference, flat-alias
double-indirection, constants param aliasing, RecordAccess field harvesting,
`.tag` enum discriminator) fixed the symptom (no exception) but not the
underlying field-harvesting collapse.

### Three latent script-level enablers

Even given Bugs A and B, the suite would have caught the vacuous passes if
the run script had been honest. Three enablers let "ok" propagate as PASS:

1. **No invariant flag for protocol cases.** All 8 protocol cases have
   `expected_property = ""` in `manifest.toml`, so [run_full_suite.sh:137-139](../scripts/run_full_suite.sh)
   never adds `--invariant` to the model-check invocation. Combined with
   `[properties] invariants = []` and `check_deadlock = false` in every
   per-case `model_configs/*.toml`, **the model checker is asked to check
   nothing**.

2. **`distinct_states = 0` was treated as PASS.** Cases 14, 15, 16, 19 all
   reported zero distinct states explored. The script's pass logic
   (`expected_result == "ok" && result_status == "ok"`) rubber-stamped them.

3. **Per-case bounds are pathologically tiny.** PBFT with `Replica = 1` is
   not a Byzantine fault-tolerance check; LE/CR/PB/EPaxos with `int 0..1` and
   `max_set_len = 1` cannot represent any real distributed scenario.

### Fixes shipped in Phase 38.14

- **`scripts/run_full_suite.sh`**: detect vacuous passes (zero states OR no
  property checked) and report them as `VACUOUS` instead of `PASS`. New
  `vacuous` field in `latest.json`. Summary now distinguishes "Passed (real)"
  from "Vacuous (theatre)".
- **`scripts/detect_stub_specs.py`**: structural detector for the five
  degeneracy patterns (stuttering Next, tautological invariants, arbitrary
  soup, primitive state param, incomplete Next). Wired into
  `run_full_suite.sh` as a final gate so it warns on every run.
- **`tests/manifest.toml`**: every protocol case now carries a `stub_status`
  field (`bug_a_stub_source`, `bug_a_incomplete_next`, or
  `bug_b_roundtrip_degraded`) and an honest, detailed `notes` entry.
- **Reports**: `latest.md`, `latest.json`, `hard_case_blocker_ledger.md`
  rewritten to reflect the 12/20 honest baseline.

### What is **NOT** fixed in Phase 38.14

- **Bug A's broken stub specs** (cases 13, 17, 20 — and the `Replica = 1`
  problem in 18). Fixing these requires writing real Paxos / Raft / PBFT /
  TwoPhase TLA+ specs from scratch with proper existential action bindings
  and non-tautological invariants. Out of scope for this audit.
- **Bug B's Verus → TLA+ → spec roundtrip rot** (cases 14, 15, 16, 19).
  Fixing this requires repair work in the `verus2tla` field harvesting and
  the `tla → spec` Init parameter type inference, ideally so that LState's
  struct fields are taken from VARIABLE declarations rather than from
  RecordAccess fallback, and so the Init parameter type is forced to be the
  state struct, not `int`. Out of scope for this audit.

Until at least one of those two tracks lands, the protocol half of the corpus
should be considered an open work item and the M9 milestone should be read
as **"the explorer no longer crashes on the corpus"**, not as
**"the explorer correctly model-checks 20 protocols"**.

---

## Prototype-to-Mainline Integration Gate (Phase 38.2.5)

**No rewrite of `transpiler/src/modelcheck` is allowed** until ALL of the
following conditions are met:

1. The DPOR prototype has its own green 20-case regression suite.
2. Baseline exhaustive exploration and DPOR agree on verdict AND normalized
   reachable-state set (or first violation witness) on all small cases.
3. The prototype has been reviewed against the existing checker's telemetry
   and parity infrastructure (Phase 36).
4. A migration plan exists that preserves the existing checker as a fallback.
5. The prototype's performance on at least 3 protocol-scale cases (e.g.,
   TwoPhase, LeaderElection, PrimaryBackup) is documented with before/after
   numbers.

Until these gates are passed, this workfolder is an incubator only.

---

## Phase 38.14.11 — Integration Gate Re-evaluation (2026-04-10)

This section records the first-pass evidence matrix for re-evaluating the
Phase 38.10 integration gate after 38.14.7-38.14.10.

### 38.10.1 precondition matrix (current evidence)

| 38.10.1 precondition | Current evidence (2026-04-10) | Status |
|---|---|---|
| 20-case corpus exists and is reproducible | Corpus and harness are present under `tests/tla/`, `tests/tla-rs/`; full-suite script run at `2026-04-10T04:47:49Z` reports `20 real / 0 vacuous / 0 failed`. | MET |
| `design.md` has pinned reference notes | Upstream-reference and concept-selection sections remain populated with pinned commits and mapping notes. | MET |
| Baseline oracle exists | Baseline runner and baseline-vs-DPOR comparison path are present (`src/baseline.rs`, `dpor.rs` comparison harness). | MET |
| Full-suite harness exists | `scripts/run_full_suite.sh` is checked in and used as the authoritative suite gate. | MET |
| Parity subset is exact under DPOR | Current enforced safety contract is subset parity (`conservative ⊆ independence`, `conservative ⊆ sleep`), not exact-set parity; automated comparison still allows subset/superset statuses. | NOT MET |
| Required hard protocol gates are no longer hand-waved | Protocol cases are non-vacuous in suite scoring (`20 real / 0 vacuous`) with audited reports synced. | MET |

### Explicit integration-gate decision (38.14.11.b)

- **Decision: NOT MET**.
- `38.10.1` remains open: the matrix is `5/6` MET and the unmet row is
  "Parity subset is exact under DPOR".
- `38.10.2` is now **MET** via
  `docs/integration_migration_plan.md` (module move map, shadow-mode
  comparison plan, rollback plan, and report-schema compatibility plan).
- Therefore the prototype remains an incubator and does not yet clear the
  Phase 38.10 gate for mainline integration.

### Post-38.14.10 optimization evidence snapshot

- Sleep-set reduction gate (Phase 38.14.10) is now closed:
  `>10%` transition reduction on `3 / 3` measured multi-process cases.
- Latest measured transition reductions:
  - `02_counter_incdec`: `6 -> 4` (`33.3%`)
  - `09_peterson_mutex_2p`: `16 -> 9` (`43.8%`)
  - `17_paxos_small`: `168 -> 39` (`76.8%`)

### Remaining blockers for 38.10 gate re-evaluation

- The exact-parity wording in 38.10.1 is not yet met under the current
  subset-parity contract.

### 38.14.11.c.b parity-gap measurement snapshot

- Added `docs/exact_parity_gap_analysis_38_10_1.md` with explicit
  measurement for the declared comparison subset from
  `test_automated_baseline_vs_dpor_comparison`.
- Current measured status: `12` compared cases, `11` exact, `1` non-exact.
- Current non-exact case: `05_broken_lock_bug`
  (`baseline=5`, `dpor=7`, status `dpor_superset_violation`), which points to
  negative-case parity policy mismatch (baseline early-stop semantics vs DPOR
  continued exploration) as the current exact-parity blocker.

### 38.14.11.c.b.b negative-case exact-parity policy decision

- **Policy selected**: witness-first parity for negative cases.
- Exact-parity contract under this policy:
  - Positive rows (`result = ok`): require exact verdict parity plus exact
    normalized reachable-state-set parity (current distinct-state equality
    check).
  - Negative rows (`result = invariant_violated` or `deadlock_detected`):
    require exact verdict-class parity plus first-witness signature parity
    (violation/deadlock kind + first witness depth), with state-count deltas
    tracked as diagnostics rather than gate-breaking mismatches.
- Why this is not a safety weakening:
  - both engines are first-counterexample searchers for negative outcomes, and
    pre-violation explored-state counts are traversal-order dependent (baseline
    BFS vs DPOR DFS/backtrack order);
  - safety equivalence for negative rows is carried by witness equivalence
    (same bug class and first witness depth) plus replay confirmation on the
    DPOR side, not by matching incidental frontier volume.
- Current evidence motivating this policy:
  - `05_broken_lock_bug` baseline JSON reports first invariant violation
    `LMutualExclusion` at depth `2`, while DPOR replay tests already confirm a
    reproducible `LMutualExclusion` witness at depth `2`; the state-count
    mismatch (`5` vs `7`) reflects traversal order, not contradictory verdicts.
