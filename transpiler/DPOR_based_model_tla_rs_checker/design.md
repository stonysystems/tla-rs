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
