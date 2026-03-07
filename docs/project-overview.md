# tla-rs Project Overview

> Automated Verified System Development Workflow

---

## 1. Vision

An end-to-end automated pipeline that takes a **natural-language description or research paper** as input and produces a **runnable, formally verified distributed system implementation** as output — with minimal human intervention.

The core insight: by composing specification generation, correctness verification, and verified code synthesis into a single workflow, we can dramatically lower the cost of building verified systems.

---

## 2. Pipeline Architecture

```
                        ┌──────────────────────┐
                        │  Text Description /   │
                        │  Research Paper        │
                        └──────────┬─────────────┘
                                   │
                          ① Spec Generation
                            (LLM-assisted)
                                   │
                                   ▼
                        ┌──────────────────────┐
                        │  Verus TLA+ Spec      │
                        │  (LInit, LNext, Types) │
                        └──────────┬─────────────┘
                                   │
                    ┌──────────────┴──────────────┐
                    │                             │
           ② Model Checking              ③ Proof Agent
           (bounded verification)         (deductive proof)
                    │                             │
                    ▼                             ▼
              ┌───────────┐              ┌────────────────┐
              │ Bug-free   │              │ Verus proofs    │
              │ confidence │              │ (full soundness)│
              └─────┬──────┘              └───────┬────────┘
                    │                             │
                    └──────────────┬──────────────┘
                                   │
                        Verified Verus TLA+ Spec
                                   │
                      ④ Transpiler (code generation)
                                   │
                    ┌──────────────┼──────────────┐
                    │              │               │
                    ▼              ▼               ▼
             ┌───────────┐ ┌─────────────┐ ┌─────────────┐
             │ Rust Exec  │ │ Refinement  │ │ Glue Code   │
             │ Impl Code  │ │ Proofs      │ │ (networking,│
             │ (CState,   │ │ (impl ⊑     │ │  marshalling│
             │  C*Fns)    │ │  spec)      │ │  service)   │
             └──────┬──────┘ └──────┬──────┘ └──────┬──────┘
                    │              │               │
                    └──────────────┼──────────────┘
                                   │
                          ⑤ Integration & Build
                            (scons + Verus verifier)
                                   │
                                   ▼
                        ┌──────────────────────┐
                        │  Runnable Verified     │
                        │  Implementation        │
                        │  (.dll / .so + C# I/O) │
                        └──────────────────────┘
```

---

## 3. Pipeline Stages

### Stage ① — Spec Generation

**Input**: Natural-language protocol description or academic paper.

**Output**: Verus TLA+ spec files — `types.rs` (state and message types), `spec.rs` (LInit, LNext predicates), invariants.

**Method**: LLM-assisted translation from informal description to formal Verus spec in the relational TLA-style (pre/post state predicates with `s`, `s_`, `c` parameters).

**Status**: Manual / research prototype.

### Stage ② — Model Checking (Bounded Verification)

**Input**: Verus spec + `model.toml` (finite domain bounds).

**Output**: Bug reports with counterexample traces, or bounded-correctness confidence.

**What it does**: Source-first model checker that directly evaluates `LInit`/`LNext` on finite state spaces. Checks safety invariants, deadlock freedom, and liveness (leads-to) properties.

**Key capabilities**:
- BFS/DFS bounded state-space exploration
- Hash compaction, symmetry reduction, partial-order reduction
- SCC-based liveness checking with weak/strong fairness
- Counterexample trace generation

**Status**: Complete (Phase 22 + 22.x). See [model-checking-source-first.md](model-checking-source-first.md).

**Limitations**: Finite domains only; does not support `forall`/`exists`, `match`, struct update, recursive helpers in evaluated expressions (these are addressable — see analysis in Phase 22 extension notes).

### Stage ③ — Proof Agent (Deductive Verification)

**Input**: Verus spec + proof obligations.

**Output**: Verus proof annotations (`proof fn`, `assert`, `ensures`) that make the spec verifiably correct under the Verus/SMT solver.

**Method**: Automated proof generation — potentially LLM-guided or tactic-based.

**Status**: Research / future work.

### Stage ④ — Transpiler (Code Generation)

**Input**: Verified Verus TLA+ spec + TOML configuration + annotation file (`.automan`).

**Output**: Three artifacts:

| Artifact | Description |
|----------|-------------|
| **Exec implementation** | Concrete Rust types (`CState`, `CConstants`) and executable functions (`C*`) that mirror each spec predicate |
| **Refinement proofs** | `ensures` clauses on each exec function proving it refines the corresponding spec predicate: `LAction(s@, result.0@, ...)` |
| **Glue code** | Networking layer (marshalling, host scheduler, service entry point) that wires the verified protocol into a deployable service |

**Key transpiler capabilities**:
- Type translation (spec `LState` → exec `CState` with `View` trait)
- Function body synthesis from relational predicates
- Proof injection (empty-vec, cardinality bridge, contains-membership, helper-preserves)
- Composite handler auto-generation (multi-action functions)
- Message type generation, host scaffold generation, scheduler analysis

**Status**: Mature. 9 protocols transpiled (RSL + 8 non-RSL). 669 verified functions, 0 errors. See [transpiler-config-reference.md](transpiler-config-reference.md).

### Stage ⑤ — Integration & Build

**Input**: Generated Rust code + C# I/O framework.

**Output**: Deployable verified service binary.

**What it does**:
- Verus verifier checks all proofs (exec correctness + refinement)
- scons build system compiles Rust → `.so` and C# → `.dll`
- C# runtime provides networking, marshalling, and service lifecycle (trusted I/O layer)

**Status**: Complete. RSL and Raft benchmarks operational.

---

## 4. What Exists Today

### Verified Protocols

| Protocol | Spec | Transpiler | Impl | Networking | Proof | Benchmark |
|----------|------|-----------|------|------------|-------|-----------|
| RSL (Multi-Paxos) | Complete | Complete | Complete | Complete | Complete (0 assumes) | Complete |
| Raft | Complete | Complete | Complete | Complete | Partial (12 assumes) | Complete |
| TwoPhase Commit | Complete | Complete | Complete | Complete | - | - |
| Primary-Backup | Complete | Complete | Complete | Complete | - | - |
| Chain Replication | Complete | Complete | Complete | Complete | - | - |
| PBFT | Complete | Complete | Complete | Complete | - | - |
| Leader Election | Complete | Complete | Complete | Complete | - | - |
| Vertical Paxos | Complete | Complete | Complete | Complete | - | - |
| EPaxos | Complete | Complete | Complete | Complete | - | - |
| Paxos | Complete | Complete | Complete | Complete | - | - |

### Tooling

| Tool | Description | Status |
|------|-------------|--------|
| **verus-transpile** | Spec → impl transpiler with proof generation | Mature (~25K LOC) |
| **Model checker** | Source-first bounded verification | Complete (~4K LOC) |
| **scons build** | Verus + .NET integrated build | Complete |
| **Integration tests** | Cluster-level protocol testing | Complete (RSL, Raft) |

### Verification Numbers

- **669** verified functions, **0** errors
- **10** RSL packet-identity assumes (IO trust boundary — irreducible)
- **12** Raft refinement proof assumes (7 LC blocked on `d_rli ≤ k` wall, 4 sound Z3 workarounds, 1 SMS blocked on LC)
- **1739** transpiler tests passing

---

## 5. Milestones

### Milestone 1 — Transpiler Feature-Complete (pre-open-source)

**Goal**: The transpiler can handle any relational TLA-style spec end-to-end without manual code.

| Task | Status | Notes |
|------|--------|-------|
| All RSL modules standalone (no delegation wrappers) | Done | All 8 modules standalone (Phase 19) |
| Auto-generate all composite handlers | Done | 8/8 Raft handlers auto-generated |
| Eliminate reducible external_body assumes | Done | Tier 1-2 verified; Tier 3-5 closed as WONTFIX (HashSet/HashMap iteration) |
| Support nested quantifier patterns in spec | Not started | Needed for more complex protocols |
| Transpiler test coverage > 95% | In progress | 1739 tests passing, 1 pre-existing failure |

### Milestone 2 — Model Checker Expression Coverage (pre-open-source)

**Goal**: The model checker can evaluate any expression that appears in real protocol specs.

| Task | Difficulty | Status | Notes |
|------|-----------|--------|-------|
| Struct update (`LState { field: val, ..s }`) | Easy (~10 LOC) | Not started | Pure BTreeMap merge |
| Match expressions | Easy (~50 LOC) | Not started | Need `match_pattern` recursive helper |
| Forall / Exists (finite-domain enumeration) | Medium (~80 LOC) | Not started | Requires EvalContext extension for schema/model access |
| Recursive spec helper functions | Hard (~150 LOC) | Not started | Needs function table, call depth guard, IR layer extension |
| Bitwise/shift operators | Easy (~20 LOC) | Not started | Low priority unless needed by a protocol |

### Milestone 3 — Open Source Release

**Goal**: Public repository, documentation, and community onboarding.

| Task | Status |
|------|--------|
| Clean up repository (remove internal paths, credentials, temp files) | Not started |
| Write user-facing README with quick-start guide | Not started |
| Write "define your own protocol" tutorial (spec → model check → transpile → run) | Not started |
| CI/CD pipeline (GitHub Actions: build + transpiler tests + Verus verification) | Not started |
| License selection (MIT / Apache-2.0 / dual) | Not started |
| Package `verus-transpile` as standalone CLI (crates.io or GitHub releases) | Not started |
| Example protocols gallery (simple ones for onboarding: mutex, counter, echo) | Not started |

### Milestone 4 — Community Growth & Adoption

**Goal**: Active users, contributors, and integrations.

| Task | Status |
|------|--------|
| Blog post / paper: "Verified Distributed Systems in Minutes, Not Months" | Not started |
| Conference talk (OSDI / SOSP / PLDI / Verus workshop) | Not started |
| Discord / Zulip community channel | Not started |
| Integration with Verus upstream (contribute patches, align on API) | Not started |
| Benchmark suite: comparative results vs. IronFleet / Dafny workflow | Not started |
| Attract first external contributor | Not started |

### Milestone 5 — Full Automation (Research Frontier)

**Goal**: Close the loop — text in, verified system out.

| Task | Status |
|------|--------|
| LLM-assisted spec generation from natural language / papers | Research |
| Proof agent for spec-level properties (inductive invariants, quantifier instantiation) | Research |
| Symbolic model checking for larger state spaces | Research |
| DPOR / sleep sets for model checker | Research |
| O(1) state clone via persistent data structures | Research |
| Incremental / parallel Verus verification | Research |

---

## 6. Evaluation Side Projects

Two empirical studies to validate the pipeline's value, runnable in parallel with the main milestones.

### 6.1 — Model Checking as Proof Accelerator

**Research question**: Does model-checking a spec before attempting deductive proof make proof development easier?

**Method**: Given the same set of protocol specs and a proof agent (or human prover):
- **Group A** (treatment): Run model checker first, fix all counterexamples, then write Verus proofs on the bug-free spec.
- **Group B** (control): Write Verus proofs directly on the spec without model checking.

**Metrics**:
- Proof development time (wall-clock or agent iterations)
- Number of failed proof attempts / backtracking steps
- Final proof size (LOC, lemma count)
- Number of spec bugs discovered during proof vs. discovered by model checker upfront

**Hypothesis**: Model checking catches shallow spec bugs (missing guards, wrong field updates, off-by-one in quorum) early. Without it, the proof agent wastes cycles on unprovable obligations from buggy specs, leading to longer development time and more backtracking.

**Prerequisites**: Proof agent (Milestone 5) or willing human provers; at least 3-5 protocols of varying complexity.

### 6.2 — Source-First Model Checker vs. TLC Performance

**Research question**: How does our source-first Rust model checker compare to TLC (the standard TLA+ model checker) in performance?

**Method**: For the same protocol specs, run both checkers on equivalent models:
- Translate our Verus TLA+ specs to standard TLA+ (or use the `generate-mc-wrapper` command to produce TLC-compatible artifacts).
- Configure equivalent finite domains, invariants, and search bounds.
- Measure on the same hardware.

**Metrics**:
- States explored per second
- Peak memory usage
- Time to full state-space exhaustion (for small models)
- Time to find seeded bugs (for bug-finding comparison)
- Reduction effectiveness (symmetry, POR) vs. TLC's built-in symmetry sets

**Protocols to compare**: TwoPhase, PrimaryBackup, LeaderElection, Paxos (all have both Verus specs and TLC wrapper fixtures).

**Expected advantages of source-first checker**:
- No TLA+ translation overhead (operates directly on Verus AST)
- Rust native performance (compiled, no JVM warmup)
- Tighter integration with the verification pipeline

**Expected advantages of TLC**:
- Mature, heavily optimized (decades of engineering)
- Multi-threaded exploration
- Larger expression coverage (full TLA+ operator set)

**Prerequisites**: TLC installation; equivalent `model.toml` ↔ `.cfg` configurations for each protocol.

---

## 7. Open Research Directions

### 7.1 — Spec Generation from Natural Language

Automating Stage ①: given a paper describing a protocol (e.g., "Raft: In Search of an Understandable Consensus Algorithm"), produce the Verus TLA+ spec. This involves:
- Extracting state machine structure from prose
- Formalizing invariants mentioned informally
- Generating `model.toml` for quick validation via model checker

### 7.2 — Proof Agent

Automating Stage ③: an agent that can write Verus proofs for spec-level properties. Challenges include:
- Inductive invariant discovery
- Quantifier instantiation strategies
- Integration with Verus's SMT backend for counterexample-guided refinement

### 7.3 — Model Checker Extensions

Expanding the bounded verification capability:
- Support `forall`/`exists` in evaluated expressions (finite-domain enumeration)
- Support `match`, struct update, recursive helpers
- Dynamic partial-order reduction (DPOR) and sleep sets
- Symbolic model checking for larger state spaces

### 7.4 — Transpiler Completeness

Remaining gaps in code generation:
- Full standalone generation for all RSL modules (election, replica)
- Eliminating remaining external_body assumptions (HashSet/HashMap iteration)
- Supporting more complex spec patterns (nested quantifiers, recursive definitions)

### 7.5 — Performance Optimization

- O(1) state clone (persistent data structures) to eliminate O(n) clone overhead
- Incremental verification for faster development cycles
- Parallel verification of independent modules
